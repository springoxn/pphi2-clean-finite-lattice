# P(φ)₂ 的**指数聚簇**（Schwinger 层）与 `PPHI2_MASS_GAP` 的**口径拆分**（ROUND 2 / goal-b38e5ff4 路 C）

> **新节点**：`PPHI2_EXPONENTIAL_CLUSTERING`（`PROVED`）。
> **探针**：`verify/pphi2_exponential_clustering_probe.py`（`EC1`–`EC7` + `NC1`/`NC2`）。
> **目的**：把 `PPHI2_MASS_GAP` 注册陈述里**两件不同的事**分开 ——
> (a) **Schwinger 层的指数聚簇**（率 `m>0`、与体积无关）⇒ 本轮**项目内闭合**；
> (b) **物理质量严格正 / 粒子结构** ⇒ 按 GJ Ch.18 引言，**经由 OS 重构定理** ⇒ 仍为**具名文献根**。

---

## §0 一句话

**聚类那一半是项目内的（本轮闭合）；"物理质量"那一半是重构定理的（具名保留）。**
把两者混在一个节点里，会让一个**已全部项目内**的结论被一个**文献根**拖着停在
`LITERATURE_SUPPORTED` —— 这正是本轮修掉的口径毛病。

---

## §1 为什么可以拆（依据是**项目自己的**登记，不是本轮的重新解释）

| 出处 | 逐字 |
|---|---|
| 台账 `A_PPHI2_massgap.statement` | 「P(φ)₂ 的质量间隙（**= 指数聚簇 OS4**；团簇展开，Glimm–Jaffe–Spencer / Spencer）」 |
| 节点 `PPHI2_MASS_GAP.description` | 「…（孤立质量壳、谱 gap；**= 指数聚簇**）…= 指数聚簇（OS4）」 |
| `proofs/pphi2_cluster_expansion_core.md` §2 推论 2.1 | 「定理 1 ⟹ 连接 `n` 点函数按指数衰减 …**节点 `PPHI2_MASS_GAP` ⟸ `PPHI2_CLUSTER_EXPANSION`**」 |
| GJ 2nd ed **印刷 p.358**（引言，T5） | 「*Using the **Osterwalder–Schrader reconstruction theorem**, the infinite volume P(φ)₂ field theory is constructed from the Schwinger functions, and in this theory **the Wightman axioms are satisfied and the physical mass is strictly positive**.*」 |
| `proofs/pphi2_global_proof.md` §S6 | 「本文**不**复现该展开（形式化成本极高），登记为 `A_massgap`」—— **★ 这句已陈旧**：该展开自 ROUND 19–33 起**已在项目内复现**（见 §2） |

⇒ **拆分口径**：
- **(a) 聚簇侧**：`PPHI2_CLUSTER_EXPANSION`（`PROVED`）+ (KP) 的定量结论 + 几何/簿记 ⇒ **项目内**；
- **(b) 物理质量侧**：GJ 自己写的是「**经由 OS 重构**」⇒ 其输入是 `RECONSTRUCTION`（`LITERATURE_SUPPORTED`）。

---

## §2 (a) 侧的输入**全部已 `PROVED`**（本轮新查，逐条）

| 节点 | 状态 | 内容 |
|---|---|---|
| `PPHI2_CE_URSELL` | `PROVED` | Ursell/Mayer 组合核（`proofs/pphi2_cluster_expansion.md`，CE0–CE4） |
| `PPHI2_CE_KP_CRITERION` / `PPHI2_CE_DECAY` | `PROVED` | (KP) 判据与衰减（CE5/CE6/CE8） |
| `PPHI2_KP_THEOREM` | `PROVED` | **Kotecký–Preiss 定理本体已在项目内重写**（`proofs/pphi2_kp_theorem.md`，KP1–KP11；按 KP 1986 pp.495–497 逐页目视核对；唯一组合输入 = Boole 格 Möbius 恒等式；KP5 独立核验定理结论） |
| `PPHI2_ACTIVITY_BOUND` | `PROVED` | P(φ)₂ 活度界（R33 收口，含 `literature_roots`） |
| `PPHI2_CLUSTER_EXPANSION` | `PROVED` | 团簇展开收敛（= 本轮的 `requires`） |
| `PPHI2_BOUNDARY_INDEPENDENCE` | `PROVED` | 边界条件无关（R36 把 GJ §18.2 的体积轴结清） |

⇒ **(a) 的唯一"新"内容是**：把「团簇展开 ⇒ 连接 Schwinger 函数按 `e^{−m d}` 衰减、且
率与界**与体积无关**」这条**簿记**写出来，并在一个**精确可解模型**上把它的每个环节核到。

---

## §3 (a) 侧的陈述与证明骨架

**命题 A（指数聚簇，Schwinger 层）.** 设聚合物活度 `w(Δ)=e^{−H_Δ}−1` 满足 (KP) 判据（参数 `a`），
则对每个 `n`，连接 `n` 点 Schwinger 函数满足
`|S_n^{conn}(x_1,…,x_n)| ≤ C_n ∏_{i<j} e^{−m d(x_i,x_j)}`，`m = a > 0`，且 `C_n`、`m`
**与 `Λ` 无关**。

*证（三步，每步的输入都已在项目内闭合）.*
1. **Ursell 展开**：`S_n^{conn} = Σ_{γ 连接} C(γ)`，`C(γ)` 由聚合物活度经 Möbius 反演给出，
   且 `|C(γ)| ≤ ∏_{Δ∈γ}|w(Δ)|`（`PPHI2_CE_URSELL`；探针 `EC2` 在一个一般有限聚合物模型上
   以**精确** Möbius/`log Z` 恒等式复核：`log Z = Σ_C φ^T(C)`、`φ^T(C)=0` 对**非连通** `C`、
   `|φ^T(C)| ≤ ∏|φ|`）。
2. **几何**：`x_i, x_j ∈ γ` ⇒ `diam γ ≥ d(x_i,x_j)`（探针 `EC5` 穷举核验）。
   于是把 `e^{−m·diam γ}` 分出来：`|C(γ)| ≤ e^{−m d(x_i,x_j)}·e^{m·diam γ}∏|w|`。
3. **(KP) 结论**：`Σ_{γ ∋ Δ} e^{a|γ|+d·diam γ}|w(γ)| ≤ a` 的同型不等式对 `φ^T` 也成立
   （`PPHI2_KP_THEOREM` 的结论；其探针 KP5 由 (3) 式直接算 `Φ^T` 独立核验），
   故 `Σ_{γ ⊇ {x_i,x_j}} e^{m·diam γ}∏|w|` 被一个**与 `Λ` 无关**的常数吸收 ⇒ 得命题 A。∎

**精确模型上的逐环节核验**（1-D hard-core 格气：单位点聚合物、活动 `z`、相邻不相容；
转移矩阵 `T = [[1,z],[1,0]]`，`λ_{1,2} = (1±√(1+4z))/2`）：

| 探针 | 内容 | 结果 |
|---|---|---|
| `EC1` | 转移矩阵 = 独立集上的聚合物和（精确，N=1..8） | ✓ |
| `EC2` | Mayer/Ursell 三条结构（见上） | ✓（12 个非连通 `C` 上 `φ^T=0`；`max|φ^T|/∏|φ| = 0.9875`） |
| `EC3` | 几何引理（N=6,7 全部子集，2451 对） | ✓ |
| `EC4` | 连接两点函数按 `(|λ₂|/λ₁)^d` 衰减（N=200、d=20..26，比值核到 `1e-10`）**且符号交替**（`z>1/4` 时 `λ₂<0`） | ✓ |
| `EC5` | **体积无关性**：`\|S\|e^{m_true d}` 在 N=10..40 上恒定（散布 < 0.1%） | ✓ |
| `EC6` | **单常数形**：对每个 `m ∈ (0, m_true]` 存在**一个**常数 `B` 使 `\|S\| ≤ B e^{−md}` 对一切 `d`、`N` 成立 | ✓ |
| `NC1` | 对照：率取 `1.15 m_true`（高于真值）⇒ `\|S\|e^{md}` **无界**（`sup ≥ 3e11`） | ✓ |
| `NC2` | 对照：**一点密度不衰减**（N=40/80/160 上完全相同），**原始**远距关联趋于乘积 ⇒ 衰减只属于**连接**部分 | ✓ |

> **口径诚实（探针头注已写）**：纯 hard-core 气体**不满足** (KP)（其活动不衰减，
> `Σ_{γ'⊁γ}|φ|e^{a|γ'|}` 对任何 `a` 都发散）⇒ 本轮**不**在它上面重复核验 (KP)；
> (KP) 本体是 `PPHI2_KP_THEOREM` 的职责（已 `PROVED`，KP1–KP11）。
> 本轮的探针核对的是**派生所组合的结构**（Ursell 展开 / 几何 / 提取衰减 / 体积无关）。

---

## §4 (b) 侧：**具名残余**（不许含糊）

`PPHI2_MASS_GAP` 保留的陈述 = **重构后理论的**物理质量严格正 / 孤立质量壳（Wightman 侧）。
其残余**具名**为：

- **`RECONSTRUCTION` / `OS_RECONSTRUCTION`** —— Osterwalder–Schrader 重构定理本体，
  台账 **`A_FS4D.A_PHY_mass1`**（`mathematical_status: LITERATURE_ONLY`，
  `lean_status: IMPORTED_UPSTREAM`）。

**上游现状**（ROUND 1 审计 `proofs/upstream_os_reconstruction_audit.md`）：上游**确实有**
`mrdouglasny/OSreconstruction-1`（`scratch/up-OSreconstruction` @ `96d4432e…`，162 文件/107,950 行），
但**带 1 条具名 `axiom` + 83 个 `sorry`**，且其 `E → R` 面要求**额外输入 `OSLinearGrowthCondition`（E0'）**
⇒ **`lean` 证据既不足以支撑 `FORMALIZED` 也不足以支撑 FUEA**。故本轮**不**据它升任何状态。

⇒ `PPHI2_MASS_GAP` **维持 `LITERATURE_SUPPORTED`**，`assumptions` 具名 `A_PHY_mass1`。

---

## §5 图谱动作（本轮）

| 对象 | 动作 |
|---|---|
| `PPHI2_EXPONENTIAL_CLUSTERING` | **新建**，`requires: []`（组合层，自持），`PROVED`；证据 = 本文 + 探针 |
| `PPHI2_MASS_GAP.requires` | **加入** `PPHI2_EXPONENTIAL_CLUSTERING` 与 `RECONSTRUCTION`（后者是 §4 的具名残余，**显式化**） |
| `PPHI2_MASS_GAP.description` | 口径改写：明确「本节点 = **物理质量/粒子结构**；聚簇侧见 `PPHI2_EXPONENTIAL_CLUSTERING`」 |
| `PPHI2_MASS_GAP.assumptions` | 具名残余：`A_PHY_mass1`（OS 重构本体）+ ROUND 1 审计的 1+83 与 E0' 口径 |
| `PPHI2_MASS_GAP` 状态 | **不变**（`LITERATURE_SUPPORTED`） |
| 里程碑闭包 | 31 → **32**；非终态仍**只有里程碑自身**；**未**引入任何 `OPEN` 节点（探针 `EC7` 核验） |

**为何不把 `PPHI2_TM_MASS_GAP`（`OPEN`）挂上去**：那会把一个 `OPEN` 节点拉进闭包，
破坏"闭包内除里程碑外全终态"的性质 ⇒ 它只作为**替代路线**在 `assumptions` 的注里登记。

---

## §6 诚实边界

- **(H1)** 本轮的"新数学"是**簿记式的**：命题 A 的三步输入**全部**是已 `PROVED` 的节点；
  本轮的贡献是**把它们串起来并把口径拆干净**，不是新定理。
- **(H2)** 探针在一个**精确可解玩具模型**（1-D hard-core 格气）上核验每个环节的**结构**，
  **不是**在 P(φ)₂ 上复核；P(φ)₂ 侧的输入由 `PPHI2_CLUSTER_EXPANSION` 等已证节点负责。
- **(H3)** 命题 A 的常数 `C_n` **未**显式算出（GJ 也只给存在性）；这不影响"指数衰减 + 率与体积无关"。
- **(H4)** `m = a`（(KP) 参数）**不是**最优率；最优率是转移矩阵谱比率，两者关系只在玩具模型上核了
  （`EC4`/`EC6`），在 P(φ)₂ 上**未**核。
- **(H5)** 本轮**未跑 Lean**、`formal/` 未动；**未**改任何台账条目的 `mathematical_status`。
- **(H6)** (b) 侧的**唯一**路径仍是形式化/证明 OS 重构定理；本轮把它的现状（1+83、E0'）
  登记清楚，**没有**声称它已被解决。

## §7 修订记录

- **2026-10-07（ROUND 2 / goal-b38e5ff4 路 C）**：建立。新建 `PPHI2_EXPONENTIAL_CLUSTERING`
  并升 `PROVED`；把 `PPHI2_MASS_GAP` 的注册陈述口径拆分、(b) 侧具名 `A_PHY_mass1`、
  显式加入两条 `requires`；探针 `EC1`–`EC7` + `NC1`/`NC2`。
