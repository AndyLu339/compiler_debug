# LLVM 优化管线差距分析（ToyC 编译器性能提升路线）

> 调研目标：对照 LLVM `-O2/-O3` 的完整优化管线，找出当前 ToyC 编译器尚未实现、
> 但对**整数计算 / 循环密集**的 benchmark（fib / gcd / prime / collatz / triangle /
> digit_sum / perfect_num 等）收益明显的优化，按优先级给出可落地实现路线。

---

## 0. 结论速览

当前编译器已覆盖 LLVM 管线中**大约 1/3 的标量优化**，但缺了几块"拿分大头"：

| 类别 | 现状 | 最大缺口 | 预估收益 |
|------|------|----------|----------|
| 中端标量/CFG | 有 CSE(局部)、SCCP、BranchFold、JumpThread | **GVN、SimplifyCFG、CVP** | ★★★★★ |
| 循环优化 | 有 LICM、Unroll、LoopEval | **Indvars + 强度削减、Loop Unswitch、Loop Rotate** | ★★★★★ |
| 后端 | 线性扫描分配、基础 codegen | **图着色分配、Peephole、指令选择打磨** | ★★★★☆ |
| 其他 | Inline、TailCallElim | DeadArgElim、GlobalDCE（廉价） | ★★☆☆☆ |

**最重要的三件事**（按投入产出比排序）：
1. **后端 Peephole + 指令选择打磨**——改动小、见效快，直接砍掉冗余 `mv`/`li`/`j`。
2. **GVN（全局值编号 + 部分冗余消除）**——中端最大的一块空白，跨块/跨循环去重。
3. **Indvars + Loop Strength Reduction（归纳变量化简 + 强度削减）**——把循环里的 `mul` 变 `add`，配合已有的 Unroll 效果翻倍。

> 说明：ToyC 无数组、无指针、无结构体、无浮点，因此 LLVM 里 SROA、向量化
> (LoopVectorize/SLP)、MemCpyOpt、别名分析(AliasAnalysis)、LoopIdiom(memset 识别)
> 等**基本用不上**，本文已过滤，不做推荐。

---

## 1. 当前已实现 vs LLVM 对照表

### 1.1 已有 Pass（含对应 LLVM 语义）

| ToyC Pass | 对应 LLVM Pass | 覆盖程度 |
|-----------|---------------|----------|
| Const_fold | instcombine 的常量折叠子集 | 部分 |
| Reassociate | reassociate | ✅ 基本完整 |
| Algebraic | instcombine 的代数化简子集 | **仅少数 pattern** |
| Muldiv_opt | 部分强度削减(仅 2 的幂) | 部分 |
| Copy_prop | (CSE 的副产品) | ✅ |
| Cse | early-cse（**仅块内**） | **只做局部** |
| Dce | dce | ✅（简单版） |
| Const_prop / Sccp | sccp | ✅ 基本完整 |
| Branch_fold | simplifycfg 的子集(分支折叠+删不可达块) | 部分 |
| Jump_thread | jump-threading | 部分（无 LVI 值域信息） |
| Dead_store_elim | dse | ✅（无内存语言，作用有限） |
| Licm | licm | ✅ 基本完整 |
| Loop_eval | 编译期循环求值(LLVM 无直接对应，属"激进"优化) | ✅ 独有 |
| Loop_unroll | loop-unroll | ✅ 基本完整 |
| Tail_call_elim | tailcallelim | ✅ |
| Inline | inline | ✅（但无成本模型？） |
| Mem2reg | mem2reg | ✅ |

### 1.2 未实现但对 ToyC 有价值的 LLVM Pass

按 LLVM 官方文档分类，下面每个都在 LLVM `-O2/-O3` 默认管线中出现：

| LLVM Pass | ToyC 是否缺 | 价值 |
|-----------|------------|------|
| **gvn** | ❌ 缺 | 高 |
| **simplifycfg** | ⚠️ 只有子集 | 高 |
| **indvars** | ❌ 缺 | 高 |
| **loop-reduce (LSR)** | ⚠️ 只有 pow2 | 高 |
| **simple-loop-unswitch** | ❌ 缺 | 高 |
| **loop-rotate** | ❌ 缺 | 中高 |
| **correlated-propagation (CVP)** | ⚠️ JumpThread 沾一点 | 中高 |
| **instcombine (完整)** | ⚠️ 只有子集 | 中高 |
| **adce (aggressive dce)** | ⚠️ 简单 DCE | 中 |
| **loop-deletion** | ❌ 缺 | 中 |
| **tailduplicate** | ❌ 缺 | 中 |
| **sink (代码下沉)** | ❌ 缺 | 中 |
| **deadargelim** | ❌ 缺 | 低(廉价) |
| **globaldce / globalopt** | ❌ 缺 | 低(廉价) |

---

## 2. LLVM `-O3` 默认管线参考（锚点）

从 LLVM 源码 `PassBuilderPipelines.cpp` 和 issue #89012 反推的**函数级优化管线**（省略
与本语言无关的向量化/别名/内存相关 pass），可作为 phase-ordering 参考：

```
(cgscc 调用图 SCC 级，callee 先于 caller 化简再内联)
  inline
  (每函数 eager 化简) sroa → early-cse → jump-threading → correlated-propagation
      → simplifycfg → instcombine → reassociate → ...
(每函数主优化管线)
  early-cse
  jump-threading
  correlated-propagation
  simplifycfg
  instcombine (aggressive-instcombine)
  tailcallelim
  reassociate
  (循环管线, 内层→外层)
      loop-instsimplify → loop-simplifycfg → licm → loop-rotate
      → licm → simple-loop-unswitch → loop-idiom → indvars → loop-deletion
      → loop-unroll
  sroa
  gvn
  sccp
  bdce
  instcombine
  jump-threading
  correlated-propagation
  adce
  dse
  simplifycfg
  (第二遍循环管线, 视收益决定是否 rerun)
```

**关键观察（可直接照搬进 `main.ml` 的顺序原则）**：
1. **CSE 要跑两次**：`early-cse` 在循环前，`gvn` 在循环后——循环变换会暴露新的公共子表达式。
2. **instcombine 穿插在几乎所有阶段之间**——它是"胶水"，每个变换后都要用代数化简吃掉冗余。
3. **jump-threading + correlated-propagation 总是成对**——因为共用 LVI 值域信息。
4. **indvars 在 loop-unroll 之前**——先把 IV 归一化，unroll 才能精确算出 trip count。
5. **gvn / sccp / adce 在循环之后**——吃掉循环变换产生的跨块冗余和死代码。

---

## 3. 高价值缺失项详解（按优先级）

### ★★★★★ 3.1 GVN — 全局值编号 + 部分冗余消除

**原理**：当前的 `Cse` 只做**块内**公共子表达式消除（相当于 LLVM `early-cse`）。GVN 把值编号
扩展到**整个函数**：沿支配树传播值编号，识别跨块、跨合并点、甚至跨循环的冗余计算，并做
**部分冗余消除(PRE)**——把"某条路径上重复计算"的表达式提升到共同前驱只算一次。

**对 ToyC 的收益**：这类 benchmark 大量存在 `if/else` 后合并点重复计算、循环体内重复的
下标/归约表达式。例如：

```c
// 合并点冗余：a*b 在两条分支都算了一遍
if (cond) { r = a * b + 1; } else { r = a * b + 2; }
// GVN 后：t = a*b; if (cond) r = t+1; else r = t+2;
```

**实现要点**（相对简单，SSA 上很好做）：
- 走**支配树 DFS**（已有 `Back/dominance.ml`），用哈希表 `(op, vn(lhs), vn(rhs)) → vreg`。
- 遇到同值编号的运算，直接 `Copy` 到已计算结果（或替换 dst）。
- Phi 节点：先给 incoming 赋值编号，处理不了 backedge 的就给新编号（见 Briggs GVN 算法）。
- 可选：做**冗余 load 消除**——但本语言 mem2reg 后几乎没有 load，可跳过。
- 位置：放在 `Loop_*` 之后、`Sccp` 之前（对应 LLVM 中 `gvn` 在循环后）。

**难度**：★★★☆☆　**预估收益**：显著（跨块/跨循环去重是当前最大空白）。

---

### ★★★★★ 3.2 Indvars + Loop Strength Reduction — 归纳变量化简 + 强度削减

**原理**：把循环里的"派生归纳变量"（derived IV，形如 `j = i*4`、`j = i*3+1`）从每轮
用 `mul` 重算，改成**在 preheader 算初值、每轮只 `add` 步长**。同时把循环**归一化为
从 0 步进 1 的单一 canonical IV**，便于 Unroll 精确计算 trip count。

**对 ToyC 的收益**：整数循环是这类 benchmark 的核心，而 `mul` 在多数实现里比 `add` 慢得多
（即使 qemu 上指令数也更多）。例如：

```c
int s = 0;
for (int i = 0; i < n; i++) s += i * 3;   // 每轮一个 mul
// 强度削减后：preheader 设 t=0; 每轮 s += t; t += 3;
```

**实现要点**：
1. 复用 `Loop_info` 识别循环，识别 header phi 作为 basic IV（`i = phi(init, i+step)`）。
2. 扫描循环体内的 `Binop(Mul, i, c)` / `Add`/`Sub` 链，识别 derived IV。
3. 对每个 derived IV：preheader 插 `初值 = a*init + b`，循环体内用新 phi + `add` 替换。
4. 之后紧跟 `Dce` + `Const_fold` 吃掉不再使用的原始 IV。
5. 位置：放在 `Loop_eval` 之后、`Loop_unroll` 之前（对应 LLVM `indvars` 在 unroll 前）。

**难度**：★★★★☆　**预估收益**：大（尤其和已有 Unroll 叠加，unroll 后 mul 数量×N 会爆炸）。

> 注：现有的 `muldiv_opt` 只处理 2 的幂（`i*4 → i<<2`），`loop_eval` 只对**完全可静态求值**
> 的小循环做编译期迭代。**通用的 IV 强度削减（非 2 的幂步长）仍然缺失**，这是独立的大块。

---

### ★★★★★ 3.3 SimplifyCFG — 控制流化简（补全）

**原理**：LLVM 的 `simplifycfg` 是 workhorse，做的事包括：
- 合并只有一个前驱/后继的基本块（消除空块、直通块）；
- **if-conversion**：把 `br` + 两个赋同一变量的分支 → 一条 select/phi；
- 消除单前驱块的 phi；
- 把 `br cond, same, same` 变成无条件跳转；
- 删除只含无条件跳转的块。

**现状**：`Branch_fold` 只做"常量条件折叠 + 删不可达块"，`Jump_thread` 做穿透空块。
但**缺少通用的块合并 + if-conversion + phi 简化**。mem2reg 和 irgen 常产生大量单前驱块
和可合并的 `if/else` 赋值，这些冗余会一直带到 codegen。

**对 ToyC 的收益**：直接减少基本块数量、减少跳转指令、把分支赋值变 select（后端可用
`snez`/条件 move 之类消除分支）。对控制流密集的 benchmark（collatz、is_prime、gcd）收益明显。

**实现要点**（遍历 CFG 反复做局部重写直到不动点）：
1. **合并直通块**：若 `A` 唯一后继 `B` 且 `B` 唯一前驱 `A`，把 `B` 的指令拼进 `A`，改跳转目标。
2. **if-conversion**：两个后继都 `Copy` 到同一 dst（或同一 phi），可合并为 phi + 单一跳转。
3. **phi 简化**：单前驱块的 phi 直接替换为 incoming 值；phi 所有 incoming 同值时删除。
4. **分支化简**：`br cond, L, L` → `jump L`。
5. 位置：作为**常驻清理 pass**，在几乎所有 CFG 变换后跑一遍（LLVM 里 simplifycfg 出现 N 次）。

**难度**：★★★☆☆　**预估收益**：大。

---

### ★★★★☆ 3.4 Loop Unswitching — 循环分支外提

**原理**：若循环体内有 `if (invariant_cond)`，且 `invariant_cond` 在循环中不变，就把循环
**克隆成两个版本**（一个 `cond==true`，一个 `cond==false`），把分支判断挪到循环外。
LLVM 对应 `simple-loop-unswitch`（trivial 版只需处理"条件完全不变"的情况）。

**对 ToyC 的收益**：带 flag 的循环（如 `while (i<n) { ...; if (flag) s+=x; ... }`）里，
每轮都要判断一次 flag。unswitch 后每次迭代省掉一次分支。

**实现要点**：
1. 找循环体里 `Br(cond, t, f)`，其中 `cond` 是循环不变量（用类似 LICM 的不变量判定）。
2. 克隆整个循环两次，一个分支条件置 true、一个置 false，各自化简掉死分支。
3. 在 preheader 前加 `Br(cond, loop_true, loop_false)`。
4. 位置：紧跟 `Licm` 之后（LLVM 顺序：licm → unswitch）。

**难度**：★★★★☆　**预估收益**：中高（仅对含不变量分支的循环有效）。

---

### ★★★★☆ 3.5 Loop Rotate — 循环旋转（do-while 化）

**原理**：把 `while` 循环重排成"先判断、后进体"的 do-while 形式：preheader 里先判断一次，
循环体结尾回跳，消除每轮迭代入口处的额外跳转。

**对 ToyC 的收益**：经典循环每条指令都算分时，每轮少一条 `j`/`bnez` 就是直接收益。对
短循环（collatz、digit_sum 之类）占比可观。

**实现要点**：把 header 里的条件判断下沉到 latch（回边块），入口条件在 preheader 预判一次。
需要配合 `Loop_info` 已有结构。这是 loop 优化的基础规范化步骤，LLVM 里在 licm 前后各做一次。

**难度**：★★★☆☆　**预估收益**：中高（常与 unroll 叠加）。

---

### ★★★★☆ 3.6 后端：图着色寄存器分配（替换线性扫描）

**原理**：当前 `regalloc.ml` 是**线性扫描**，虽然有 leaf/non-leaf 寄存器池的巧思，但线性扫描
在活跃区间密集时会**多余溢出**。图着色（Chaitin/Briggs 简化-着色）利用 RISC-V 的 32 个寄存器，
能显著减少 spill。

**对 ToyC 的收益**：spill 一次 = 一条 `sw` + 一条 `lw`（或多次）。循环体里多 spill 几次，
每轮迭代代价×N。对寄存器压力大的 benchmark（多归约变量的循环）收益直接。

**实现要点**：
1. 已有 `Live_intervals` / `Live_var`，可改造出**干扰图**（活跃区间重叠 → 边）。
2. 实现 Briggs 简化着色：反复找度数 < K 的节点入栈删除，最后回填着色，删不动的 spill。
3. 保留 leaf/non-leaf 寄存器池策略（很聪明，别丢）。
4. 也可折中：先做**局部(块内)图着色 + 跨块线性扫描**，工程上更快见效。

**难度**：★★★★★　**预估收益**：大（但实现成本最高，建议放后期）。

---

### ★★★★☆ 3.7 后端：Peephole + 指令选择打磨（性价比最高）

**原理**：RISC-V 代码生成后直接扫一遍汇编/机器指令，消除本地冗余。这是**投入小、见效快**、
几乎零风险的一类优化，很多队伍靠这块直接涨分。

**具体可做的（按容易程度排序）**：
1. **删冗余 move**：`mv a0, a0`、`mv a0, a1; ...; mv a1, a0` 成对抵消。
2. **删跳转到下一条**：`j .Lnext` 紧跟 `.Lnext:` 直接删。
3. **删 0 偏移访存**：`lw a0, 0(a1)` → `lw a0, (a1)`（若汇编器不自动做）。
4. **比较指令优化**（见 3.8）。
5. **常量加载优化**：`li a0, 0` → `mv a0, zero`；小立即数直接用 `addi a0, zero, n`；能 `lui` 一次解决的别拆两次。
6. **乘/除立即数优化**：`mul a0, a1, imm` 若 imm 是 2 的幂 → `slli`（已有 muldiv_opt 在 IR 层做，但 codegen 里再兜底一次）；`div by small const` 可走乘法逆元（较难，可选）。
7. **尾调用**：`call f; ret` → `tail f`（若 ABI 允许，省一次 jal+ret）。
8. **合并相邻 `addi`**：`addi a0, a0, 1; addi a0, a0, 1` → `addi a0, a0, 2`。

**难度**：★★☆☆☆　**预估收益**：中（累加起来可观，且稳定不翻车）。

---

### ★★★☆☆ 3.8 后端：比较/分支指令选择优化

**原理**：`emit_icmp` 目前生成"比较→写 0/1→bnez"的通用序列。RISC-V 有专门指令可省：

| 场景 | 通用序列 | 优化后 |
|------|---------|--------|
| `a == b` | `sub t,a,b; seqz d,t`（或 slt+slt） | `xor t,a,b; seqz d,t`（更短） |
| `a < b` | `slt d,a,b`（已是好的） | 保持 |
| `a <= b` | `slt t,b,a; xori d,t,1` | 保持 |
| `a == const` | 先 li 常量再比 | 若 const 在 imm12 内用 `addi/xori` 直接比；`==0` 用 `seqz` |
| `a < const` | 先 li 再 slt | const∈[-2048,2047] 用 `slti`；`<0` 用 `sltz` |
| 条件分支 `if(a==0) goto L` | 算 0/1 再 bnez | **直接 `beqz a, L`**（消除中间临时寄存器） |

**关键点**：ToyC 的 `if`/`while` 条件经 irgen 会先 `icmp` 成 i1 再 `Br`，codegen 应**识别
"icmp 结果只被一个 Br 用"**，直接生成 `beq/bne/blt/bge` 而**不物化 0/1**。这是当前最可能
存在的浪费点。

**难度**：★★★☆☆　**预估收益**：中高（条件判断遍布所有 benchmark）。

---

### ★★★☆☆ 3.9 Correlated Value Propagation（值域关联传播）

**原理**：利用分支条件推导值域，进一步折叠比较。例如：

```c
if (x < 5) { if (x < 10) ... }   // 内层 x<10 恒真，可折叠
```

LLVM 用 LVI（lazy value info）做。当前 `Jump_thread` 只做穿透，没做值域推导。

**对 ToyC 的收益**：嵌套条件、边界判断的 benchmark（is_prime、perfect_num）有收益。

**实现要点**：在分支后沿 CFG 传播"真/假"边上的值域约束，对 `Icmp` 用区间/常量判断能否
折叠为常量。与 jump-threading 成对运行。

**难度**：★★★☆☆　**预估收益**：中。

---

### ★★★☆☆ 3.10 完整 InstCombine（扩充 Algebraic）

**原理**：当前 `algebraic.ml` 只有少数 pattern（x+0、x*1、x*0 等）。LLVM instcombine 有数百个
pattern，对整数语言高价值的包括：

- `(x+1)+1 → x+2`、`(x+c1)+c2 → x+(c1+c2)`（常量合并）
- `x - x → 0`、`x + x → x*2`（→ `x<<1`）
- `x*2^k → x<<k`（已有 muldiv）
- `x/1 → x`、`x%1 → 0`、`x/2^k`（除法→算术右移，注意负数，见 muldiv_opt）
- `(x & c) 当 c 全 1 → x`、`x & 0 → 0`、`x | 0 → x`
- 比较恒等：`x == x → true`、`x < x → false`
- `!x` 双否定、`x && x → x` 等逻辑化简（若 IR 里 LAnd/LOr 未 lower）
- 移位合并：`(x<<a)<<b → x<<(a+b)`（溢出情况小心）

**实现要点**：把 `algebraic.ml` 扩展成一个 **worklist 驱动**的 pattern 匹配器（匹配→替换→把
新指令的 uses 再入队），而不是现在的单遍 `IntMap` 收集。因为一个替换会暴露下一个替换。

**难度**：★★☆☆☆（逐条加 pattern 很机械）　**预估收益**：中（每条不大，累积可观，且作为胶水
提升其他 pass 效果）。

---

### ★★☆☆☆ 3.11 其他低优先但廉价的 Pass

| Pass | 说明 | 收益 |
|------|------|------|
| **adce (aggressive dce)** | 当前 DCE 只删单条死指令；adce 还能删**无限循环**、无副作用死循环块 | 中 |
| **loop-deletion** | 删除"算完结果没人用"的循环（配合 indvars 后 IV 不再被外部使用） | 中 |
| **tailduplicate** | 复制后继块来拉直 CFG、消除无条件跳转，为其他 opt 开路 | 中 |
| **sink (代码下沉)** | 把指令下沉到后继，避免在不需要的路径上执行 | 中 |
| **deadargelim** | 删掉未使用的函数参数（几乎免费） | 低 |
| **globaldce / globalopt** | 删未用函数/全局变量；把只存不读的全局删掉 | 低 |

---

## 4. 后端总览（补充 3.6–3.8）

当前后端管线：`Live_intervals → Regalloc(线性扫描) → Codegen`。缺的标准后端阶段：

| 阶段 | 现状 | 建议 |
|------|------|------|
| 指令选择 | 直接 match IR 逐条 emit | 加 pattern 匹配（比较→分支融合、立即数折叠） |
| 寄存器分配 | 线性扫描 | 升级图着色（或局部着色+全局线性） |
| **Peephole** | ❌ 无 | **先加**（性价比最高） |
| 指令调度 | ❌ 无 | 低优先（qemu 简单核上收益有限） |
| 延迟槽/寄存器压力感知 | ❌ 无 | 低优先 |

---

## 5. 建议实施路线图（分四期）

### 第一期（快速拿分，1-2 天）
1. **后端 Peephole**（3.7）：删冗余 `mv`、删跳下一条的 `j`、`li 0`→`mv zero`、相邻 `addi` 合并。
2. **比较/分支指令选择优化**（3.8）：icmp 结果只被 Br 用时直接 `beq/bne/blt/bge`，不物化 0/1。
3. **扩充 Algebraic**（3.10）：常量合并、`x-x`、`x*2^k` 等高频 pattern。

> 这期几乎零风险、纯删冗余，先稳稳涨一波。

### 第二期（中端大头，2-3 天）
4. **SimplifyCFG 补全**（3.3）：块合并 + if-conversion + phi 简化。
5. **GVN**（3.1）：跨块/跨循环值编号 + 部分冗余消除。
6. **Loop Rotate**（3.5）：循环 do-while 化。
任务 4：SimplifyCFG 补全（3.3）
                                                                                
  当时的意思：LLVM 的 simplifycfg                                             
  是"打杂王"，反复做控制流局部重写直到不动点。当前 Branch_fold 只做"常量条件折叠
   + 删不可达块"，Jump_thread 只做"穿透空块"。缺三样：
                                                                                
  1. 块合并——A 唯一后继 B 且 B 唯一前驱 A 时，把 B 的指令拼进 A、改 A           
  的跳转目标。                                 
  2. if-conversion——if (c) r = x; else r = y; 两个分支都 Copy 到同一 dst，合并成
   phi（本语言没有 select 指令，只能用 phi）。                                  
  3. phi 简化——单前驱块的 phi 直接替换成 incoming 值；所有 incoming 同值的 phi
  删除。                                                                        
                           
  现在需要改什么（新建文件 lib/Mid/Opt/simplifycfg.ml）：                       
  - 实现 run_on_func + run，接口照 CLAUDE.md 里的统一模式。                   
  - 反复做局部重写直到不动点（参考 branch_fold.ml:126 的 fixpoint 写法）。      
  - 用 Dominance.analyze 拿前驱/后继信息（branch_fold.ml 里已有               
  compute_preds/compute_reachable 可以直接抄）。                                
  - 改 main.ml：在 Branch_fold/Jump_thread 之后插入 let ir = Simplifycfg.run ir 
  in，循环变换后再跑一遍（文档 6 节也建议这样，作为"胶水"常驻）。               
                                                                                
  ▎ 注意：branch_fold.ml:79 的 rewrite_targets_through_empty_jumps 
  ▎ 其实已经做了一部分"空块压平"，jump_thread.ml                                
  ▎ 也做了穿透。所以这块不是从零开始，是把"合并直通块 / if-conversion / phi   
  ▎ 简化"这三块补上，不要和已有的重复。                                         
                                                                              
  ---                                          
  任务 5：GVN（3.1）                                                          
                                                                                
  当时的意思：当前 Cse 只做"块内"去重，GVN 把值编号扩展到整个函数——沿支配树传播
  ，识别跨块/跨合并点/跨循环的冗余计算，并做部分冗余消除(PRE)（把只在某条路径上 
  重复算的表达式提到共同前驱只算一次）。典型收益是 if/else 合并点后重复计算
  a*b。                                                                         
                                                                              
  现在需要改什么（新建文件 lib/Mid/Opt/gvn.ml）：                               
  - 走支配树 DFS（Dominance.analyze 已有 idom/children，直接可用）。          
  - 哈希表 (op, vn(lhs), vn(rhs)) → vreg，遇同值编号就 Copy 到已算结果（或替换  
  dst）。                                                                     
  - phi 节点：incoming 先编号，处理不了 backedge 就给新编号（Briggs GVN 算法）。
  - 可选做 PRE（在合并点插表达式），难度较高，文档标为"可选"。                  
  - 位置：文档建议放循环之后、Sccp 之前。                                       
                                                                                
  一个需要你先确认的点：我读了 cse.ml:101-130，它已经是沿支配树 DFS 并向下继承  
  env 的——也就是它其实已经做了跨块的值编号（不只是文档当时说的"块内"）。所以 GVN
   的边际收益主要在 PRE + phi 同余处理，而不是简单的跨块去重。开工前建议先确认
  Cse 现在的实际覆盖范围，避免和它重复造轮子。                                  
                                                                              
  ---                                          
  任务 6：Loop Rotate（3.5）                                                  
                            
  当时的意思：把 while 循环重排成 do-while 形式——preheader 先判断一次，循环体结
  尾回跳，消除每轮入口处那条额外跳转。对短循环（collatz、digit_sum）每轮省一条  
  j/bnez。
                                                                                
  现在需要改什么（新建文件 lib/Mid/Opt/loop_rotate.ml）：                       
  - 复用 Loop_info.analyze（loop_info.ml 已有 header/preheader/latches/blocks
  等完整结构）。                                                                
  - 变换：把 header 里的条件判断下沉到 latch（回边块），入口条件在 preheader
  预判一次。                                                                    
  - 这是 CFG 变换，涉及创建新基本块、改 phi incoming 边、改终结指令目标——对应   
  CLAUDE.md 里的模式 C（参考 tail_call_elim.ml/loop_unroll.ml 的新 label / block
   map / phi 重写写法）。                                                       
  - 位置：文档 6 节参考顺序是 Licm → Loop_rotate → Loop_unswitch → Loop_eval → 
  ...，即插在 Licm 之后、Loop_eval/Loop_unroll 之前。
### 第三期（循环优化深化，3-4 天）
7. **Indvars + Loop Strength Reduction**（3.2）：派生 IV 的 mul→add。
8. **Loop Unswitching**（3.4）：不变量分支外提。
9. **CVP**（3.9）：值域关联传播，配合现有 JumpThread。

### 第四期（后端深化，可选，4-5 天）
10. **图着色寄存器分配**（3.6）：替换线性扫描。
11. 廉价清理 pass：adce、loop-deletion、deadargelim、globaldce。

---

## 6. 更新 `main.ml` 的参考顺序（对齐 LLVM）

在现有链路上，建议最终调整为（新增用 **粗体** 标出）：

```
Const_fold → Reassociate → Const_fold
Tail_call_elim → Inline
**deadargelim / globaldce**（廉价清理）
Algebraic(instcombine) → Muldiv_opt → Copy_prop → Cse(early-cse) → Dce
Const_prop → Sccp → Branch_fold → Dce → Jump_thread → **SimplifyCFG**
Dead_store_elim
Licm → **Loop_rotate** → **Loop_unswitch** → Loop_eval → **Indvars(LSR)** → Loop_unroll
→ **SimplifyCFG** → Const_fold → Copy_prop → Sccp → Branch_fold → Dce
**GVN** → Sccp → **adce** → Algebraic → Jump_thread → **SimplifyCFG**
```

> 原则：**instcombine(Algebraic) 和 simplifycfg 是胶水，穿插在每次 CFG/循环变换之后**；
> **GVN 放循环之后**（吃跨块冗余）；**indvars 放 unroll 之前**（先归一化 IV）。

---

## 7. 参考来源

- LLVM 官方 Passes 文档：https://llvm.org/docs/Passes.html
- nikic《LLVM: The middle-end optimization pipeline》：https://www.npopov.com/2023/04/07/LLVM-middle-end-pipeline.html
- LLVM `-O3` 管线反推（issue #89012）：https://github.com/llvm/llvm-project/issues/89012
- Briggs GVN / CS6120 全局值编号：https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/global-value-numbering
- CS6120 强度削减：https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/strength-reduction-pass-in-llvm
- 图着色寄存器分配：https://www.lighterra.com/papers/graphcoloring
