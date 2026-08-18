#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "$0")" && pwd)"
compiler="$repo_dir/_build/default/bin/main.exe"
test_dir="$repo_dir/test"
asm_dir="$test_dir/asm"

mkdir -p "$asm_dir"

echo "[1/2] Building compiler..."
dune build --root "$repo_dir"

if [ ! -x "$compiler" ]; then
  echo "error: compiler binary not found: $compiler" >&2
  exit 1
fi

shopt -s nullglob
sources=("$test_dir"/*.c)

if [ "${#sources[@]}" -eq 0 ]; then
  echo "error: no C test files found in $test_dir" >&2
  exit 1
fi

echo "[2/2] Generating assembly into $asm_dir ..."
for src in "${sources[@]}"; do
  base="$(basename "$src" .c)"
  out="$asm_dir/$base.s"
  "$compiler" < "$src" > "$out"
  echo "  generated: test/asm/$base.s"
done

echo "done."
