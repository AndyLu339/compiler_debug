#!/usr/bin/env python3
import argparse
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


RV32_LINUX_START = """\
    .section .text
    .globl _start
_start:
    call main
    li a7, 93
    ecall
"""

@dataclass
class CaseResult:
    name: str
    status: str
    elapsed_ms: str
    reference_elapsed_ms: str
    speed_ratio: str
    score: float
    expected_code: int | None = None
    actual_code: int | None = None
    detail: str | None = None


@dataclass
class TestCase:
    root: Path
    src: Path
    relpath: Path


def run_cmd(cmd, *, stdin_text=None, timeout=None):
    return subprocess.run(
        cmd,
        input=stdin_text,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


def format_elapsed_ms(elapsed_s: float | None) -> str:
    if elapsed_s is None:
        return "-"
    return f"{round(elapsed_s * 1000)}ms"


def format_speed_ratio(candidate_s: float | None, reference_s: float | None) -> str:
    if candidate_s is None or reference_s is None or candidate_s <= 0.0:
        return "-"
    return f"{reference_s / candidate_s:.2f}x"


def require_tool(name: str):
    if shutil.which(name) is None:
        print(f"error: missing tool: {name}", file=sys.stderr)
        sys.exit(2)


def discover_cases(test_roots: list[Path], pattern: str | None):
    cases: list[TestCase] = []
    for test_root in test_roots:
        for src in sorted(test_root.rglob("*.c")):
            cases.append(TestCase(root=test_root, src=src, relpath=src.relative_to(test_root)))

    if pattern:
        exact = [
            case
            for case in cases
            if case.src.stem == pattern
            or str(case.relpath) == pattern
            or str(case.src) == pattern
        ]
        if exact:
            return exact
        cases = [
            case
            for case in cases
            if pattern in case.src.stem
            or pattern in str(case.relpath)
            or pattern in str(case.src)
        ]
    return sorted(cases, key=lambda case: (str(case.root), str(case.relpath)))


def build_compiler(repo_root: Path):
    proc = run_cmd(["dune", "build", "--root", str(repo_root)], timeout=300)
    if proc.returncode != 0:
        print(proc.stderr or proc.stdout, file=sys.stderr)
        print("error: dune build failed", file=sys.stderr)
        sys.exit(2)


def compile_startup(tmpdir: Path):
    start_s = tmpdir / "rv32_linux_start.S"
    start_o = tmpdir / "rv32_linux_start.o"
    start_s.write_text(RV32_LINUX_START, encoding="ascii")
    proc = run_cmd(
        [
            "riscv64-linux-gnu-as",
            "-march=rv32im",
            "-mabi=ilp32",
            "-o",
            str(start_o),
            str(start_s),
        ],
        timeout=30,
    )
    if proc.returncode != 0:
        print(proc.stderr or proc.stdout, file=sys.stderr)
        print("error: failed to assemble rv32 startup file", file=sys.stderr)
        sys.exit(2)
    return start_o


def assemble_and_link(startup_o: Path, asm_file: Path, obj_file: Path, elf_file: Path):
    as_proc = run_cmd(
        [
            "riscv64-linux-gnu-as",
            "-march=rv32im",
            "-mabi=ilp32",
            "-o",
            str(obj_file),
            str(asm_file),
        ],
        timeout=30,
    )
    if as_proc.returncode != 0:
        return "汇编失败", as_proc.stderr.strip() or as_proc.stdout.strip()

    ld_proc = run_cmd(
        [
            "riscv64-linux-gnu-ld",
            "-m",
            "elf32lriscv",
            "-e",
            "_start",
            "-o",
            str(elf_file),
            str(startup_o),
            str(obj_file),
        ],
        timeout=30,
    )
    if ld_proc.returncode != 0:
        return "链接失败", ld_proc.stderr.strip() or ld_proc.stdout.strip()

    return None, None


def run_reference(cc: str, startup_o: Path, src: Path, out_dir: Path, timeout_s: float):
    asm_file = out_dir / f"{src.stem}.ref.s"
    obj_file = out_dir / f"{src.stem}.ref.o"
    elf_file = out_dir / f"{src.stem}.ref.elf"
    compile_proc = run_cmd(
        [
            cc,
            "-O2",
            "-w",
            "-S",
            "-march=rv32im",
            "-mabi=ilp32",
            "-o",
            str(asm_file),
            str(src),
        ],
        timeout=60,
    )
    if compile_proc.returncode != 0:
        return None, f"reference compile failed:\n{compile_proc.stderr or compile_proc.stdout}"

    stage, stage_err = assemble_and_link(startup_o, asm_file, obj_file, elf_file)
    if stage is not None:
        return None, f"reference {stage} failed:\n{stage_err}"

    t0 = time.perf_counter()
    try:
        run_proc = run_cmd(["qemu-riscv32", str(elf_file)], timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return None, "reference run timed out"

    if run_proc.returncode < 0:
        return None, f"reference terminated by signal {-run_proc.returncode}"

    elapsed_s = time.perf_counter() - t0
    return (run_proc.returncode, run_proc.stdout, elapsed_s), None


def run_candidate(
    compiler_bin: Path,
    startup_o: Path,
    src: Path,
    out_dir: Path,
    timeout_s: float,
):
    asm_file = out_dir / f"{src.stem}.s"
    obj_file = out_dir / f"{src.stem}.o"
    elf_file = out_dir / f"{src.stem}.elf"

    source_text = src.read_text(encoding="utf-8")
    try:
        compile_proc = run_cmd([str(compiler_bin)], stdin_text=source_text, timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return "编译器异常", None, None, None, "compiler timed out"

    if compile_proc.returncode != 0:
        return "编译器异常", None, None, None, compile_proc.stderr.strip() or compile_proc.stdout.strip()

    asm_file.write_text(compile_proc.stdout, encoding="utf-8")

    stage, stage_err = assemble_and_link(startup_o, asm_file, obj_file, elf_file)
    if stage is not None:
        return "汇编/链接失败", None, None, None, stage_err

    t0 = time.perf_counter()
    try:
        run_proc = run_cmd(["qemu-riscv32", str(elf_file)], timeout=timeout_s)
    except subprocess.TimeoutExpired:
        return "运行超时", None, None, None, "candidate run timed out"

    elapsed_s = time.perf_counter() - t0
    return "完成", elapsed_s, run_proc.returncode, run_proc.stdout, run_proc.stderr.strip()


def print_result(result: CaseResult):
    print(
        f"{result.name}\t{result.status}\t{result.elapsed_ms}\t"
        f"{result.reference_elapsed_ms}\t{result.speed_ratio}\t{result.score:.2f}"
    )


def main():
    repo_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(
        description="功能测试框架：参考侧与当前编译器侧都在 rv32 + qemu-riscv32 环境下执行。"
    )
    parser.add_argument(
        "--test-root",
        action="append",
        default=None,
        help="测试根目录；可重复传入多个，默认同时运行功能测试和优化测试代码包",
    )
    parser.add_argument(
        "--pattern",
        default=None,
        help="仅运行文件名或路径中包含该字符串的测试",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=2.0,
        help="单个测试的编译或运行超时秒数",
    )
    parser.add_argument(
        "--score-total",
        type=float,
        default=100.0,
        help="总分，按通过用例均分",
    )
    parser.add_argument(
        "--keep-artifacts",
        action="store_true",
        help="已废弃；中间产物默认保留到 test/asm 目录",
    )
    parser.add_argument(
        "--reference-cc",
        default="riscv64-linux-gnu-gcc",
        help="参考 RISC-V 交叉编译器",
    )
    args = parser.parse_args()

    if args.test_root:
        test_roots = [Path(p).resolve() for p in args.test_root]
    else:
        test_roots = [
            repo_root / "test" / "test_cases",
            repo_root / "test" / "optimization_tests",
        ]
    for test_root in test_roots:
        if not test_root.exists():
            print(f"error: test root does not exist: {test_root}", file=sys.stderr)
            sys.exit(2)

    for tool in ["dune", args.reference_cc, "riscv64-linux-gnu-as", "riscv64-linux-gnu-ld", "qemu-riscv32"]:
        require_tool(tool)

    build_compiler(repo_root)
    compiler_bin = repo_root / "_build" / "default" / "bin" / "main.exe"
    if not compiler_bin.exists():
        print(f"error: compiler binary not found: {compiler_bin}", file=sys.stderr)
        sys.exit(2)

    cases = discover_cases(test_roots, args.pattern)
    if not cases:
        print("error: no test cases found", file=sys.stderr)
        sys.exit(2)

    score_per_case = args.score_total / len(cases)
    passed = 0
    results: list[CaseResult] = []

    tmpdir = repo_root / "test" / "asm"
    if tmpdir.exists():
        shutil.rmtree(tmpdir)
    tmpdir.mkdir(parents=True, exist_ok=True)
    startup_o = compile_startup(tmpdir)
    print("测试名\t状态\t当前运行\t参考运行\t速度比\t得分")

    for case in cases:
        src = case.src
        case_dir = tmpdir / case.root.name / case.relpath.parent
        case_dir.mkdir(parents=True, exist_ok=True)

        ref, ref_err = run_reference(args.reference_cc, startup_o, src, case_dir, args.timeout)
        if ref is None:
            result = CaseResult(src.stem, "参考失败", "-", "-", "-", 0.0, detail=ref_err)
            results.append(result)
            print_result(result)
            continue

        expected_code, expected_stdout, ref_elapsed_s = ref
        status, elapsed_s, actual_code, actual_stdout, detail = run_candidate(
            compiler_bin,
            startup_o,
            src,
            case_dir,
            args.timeout,
        )

        if status == "完成":
            if actual_code == expected_code and actual_stdout == expected_stdout:
                final_status = "通过"
                score = score_per_case
                passed += 1
            else:
                final_status = "错误输出"
                score = 0.0
        else:
            final_status = status
            score = 0.0

        result = CaseResult(
            name=src.stem,
            status=final_status,
            elapsed_ms=format_elapsed_ms(elapsed_s),
            reference_elapsed_ms=format_elapsed_ms(ref_elapsed_s),
            speed_ratio=format_speed_ratio(elapsed_s, ref_elapsed_s),
            score=score,
            expected_code=expected_code,
            actual_code=actual_code,
            detail=detail,
        )
        results.append(result)
        print_result(result)

    total_score = sum(r.score for r in results)
    print()
    print(f"通过 {passed}/{len(results)}")
    print(f"得分 {total_score:.2f}/{args.score_total:.2f}")

    failed = [r for r in results if r.status != "通过"]
    if failed:
        print()
        print("失败详情:")
        for r in failed:
            detail = r.detail or ""
            if r.status == "错误输出":
                print(
                    f"- {r.name}: 期望返回 {r.expected_code}, 实际返回 {r.actual_code}"
                )
            elif detail:
                first_line = detail.splitlines()[0]
                print(f"- {r.name}: {r.status}: {first_line}")
            else:
                print(f"- {r.name}: {r.status}")

    sys.exit(0 if not failed else 1)


if __name__ == "__main__":
    main()
