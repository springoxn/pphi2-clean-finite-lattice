# Proof — P(φ)₂ 全局纸面数学证明闭合（`INTERACTING_SCALAR_2D_COMPLETE`）

> **目的**：把第三里程碑 `INTERACTING_SCALAR_2D_COMPLETE` 的构造**端到端**写成一份纸面证明：
> 每一步给出精确陈述、证明（或精确归约到具名输入）、以及**证据等级**。这是里程碑
> `next_gate = PROVED_UNDER_ASSUMPTIONS` 的 `proof` 证据，也是后续攻具体残余公理的骨架。
>
> **纪律**（`proof_graph/STATUS_ONTOLOGY.md`）：状态不得高于 evidence；`0 sorry ≠ 数学闭环`。
> 本文**不**声称把簇展开（GJS）与 R² 紧性（Fröhlich/Park）在项目内从零证明——它们是
> **具名输入**；本文证明的是**归约与装配**：这些输入 ⟹ 主定理。凡本文"内部闭合"的步骤，
> 标 `[IN-PROOF]`；凡归约到具名输入的步骤，标 `[REDUCED]`；凡保留文献根的，标 `[LIT-ROOT]`。
>
> **★ 现状注（2026-10-11）：本文件关于 (V) 的四处陈述已过时。** 文中「`A_PPHI2_nelson_volume`（Nelson 体积均匀界 (V)）已项目内证明」
> 与「节点 `PPHI2_NELSON_BOUND` → `PROVED`」（§0 表、§S2 与修订记录共四处，写于 2026-09-14）记的是**加权** (V) 的旧口径。
> 2026-10-10 的口径改写（A 档：改口径不改档，登记在节点 `PPHI2_NELSON_VOLUME` 的 `description`）把它拆成两段：
> **加权** (V)（`V^ρ_Λ = ∫_Λ ρ:P(φ):_κ`）项目内已证（路线 A：Boué–Dupuis 归约 + (PRE-1) 的 S1–S4 移植）；
> **无权** (V)（`V_Λ = ∫_Λ :P(φ):_κ`）是**具名文献根**（GJ 2nd ed `Theorem 8.6.2` + `Proposition 8.6.3`（+ `Corollary 10.3.2`），
> **本项目不证明它**）；「动力学截断」路线（引理 4.10 + 定理 6.2）已被否证（探针 `verify/pphi2_layercake_asymptotics_probe.py` AXLC1–2）。
> 读本文件里任何 (V) 相关句子时按此口径；边界逐条见 `proof_graph/scopes/PPHI2_NELSON_VOLUME.yaml`。
>
> **数值/符号断言**：`verify/pphi2_global_probe.py`（P1–P7）。
> **输入来源**：`proof_graph/frontiers/FRONTIER_PPHI2_LOCAL_REPRODUCTION.md`、
> `proof_graph/assumptions/A_PPHI2.yaml`、`docs/upstream/pphi2/README.md`。

---

## 0. 约定与记号（钉死，防惯例漂移）

- 欧氏二维：`x=(x₀,x₁)∈ℝ²`，`|x|=√(x₀²+x₁²)`。反射 `θ(x₀,x₁)=(-x₀,x₁)`。
- 自由协方差（两点函数）：
  \[
    C_m(x)=\frac{1}{2\pi}K_0(m|x|)\quad(x\ne 0),\qquad
    \widehat C_m(p)=\frac{1}{|p|^2+m^2},
  \]
  其中 `K₀` 为第二类修正 Bessel 函数，Fourier 约定 `Ĉ(p)=∫ e^{-ip·x}C(x) dx`。
  （二维核对：`∫ d²p/(2π)² · e^{ip·x}/(|p|²+m²) = K₀(m|x|)/(2π)`。）
- **UV 行为**：`K₀(z) = -log(z/2)-γ+O(z²log z)`（`z→0`），故
  \[
    C_m(x)\;\underset{|x|\to0}{\sim}\;-\frac{1}{2\pi}\log(m|x|)+\frac{\log 2-\gamma}{2\pi}\to+\infty .
  \]
  即 `C_m(0)=∞` ⇒ **必须 Wick 序**。**IR 行为**：`K₀(z)~√(π/2z)e^{-z}`，故
  `C_m(x)~√(π/(2m|x|))e^{-m|x|}/(2π)`，**指数衰减率 = m**（此即质量间隙/聚簇率）。
- 正则化：格距 `ε`（或动量截断 `κ`）。`C_{m,ε}`、`:φ^n:_ε`、`H_{Λ,ε}` 为对应的正则化对象；
  `ε↓0`（`κ→∞`）为 UV 极限。
- 相互作用多项式：`P` 为实**偶**多项式，`P(X)=Σ_{k=1}^{n}a_{2k}X^{2k}`，`a_{2n}>0`（下有界），
  `a₂>0`（质量项）。Wick 序：`:P(φ):_ε(x)=Σ_k a_{2k}:φ^{2k}:_ε(x)`。
- 有限体积：`Λ⊂ℝ²` 有界，取 Dirichlet 或环面边界。`H_{Λ,ε}=∫_Λ :P(φ):_ε(x)dx`。
- 测度：`dμ_{G,Λ,ε}` 为自由 Gaussian 测度（协方差 `C_{m,ε}|_Λ`）；
  `dμ_{Λ,ε}=Z_{Λ,ε}^{-1}e^{-H_{Λ,ε}}dμ_{G,Λ,ε}`，`Z_{Λ,ε}=∫ e^{-H_{Λ,ε}}dμ_{G,Λ,ε}`。
- `𝒜_+`：只依赖 `{x₀≥0}` 上场的 `L²(μ_G)` 函数生成的（实）代数；`θ𝒜_-` 类似。

### 主定理（目标陈述，采用上游 coherence 分析的修正口径）

**定理 `MAIN`**（在假设组 `𝒜` 下）。设 `P` 如上。则存在 `S'(ℝ²)` 上的概率测度 `μ`（P(φ)₂ 无限体积测度），满足：

1. **OS0**（正则性/解析性）：Schwinger 函数 `S_n` 为 `S'` 元素，离对角 `C^∞`，并具解析性；
2. **OS1/OS3**（反射正定性）：`μ` 关于任一坐标超平面反射正定（RP）；
3. **OS2**（欧氏不变性）：`μ` 在 `E(2)=ℝ²⋊O(2)` 下不变；
4. **OS4**（聚簇）：`S_n` 的连接部分按指数率衰减（率即物理质量 `m_phys>0`）；
5. **非平凡/非高斯**：连接四点函数 `u₄≠0`；
6. **质量间隙**（stretch）：转移算子的谱间隙 `m_phys>0`。

且 `μ` 是 `{μ_Λ}` 的弱极限。

**假设组 `𝒜`（显式，逐项登记于 `A_PPHI2.yaml`）**：

| 记号 | 内容 | 来源 | 本文用法 |
|---|---|---|---|
| `A_free` | 自由 GFF 测度 `μ_G` 存在（Minlos/Bochner，协方差 `C_m`） | 共享栈 `bochner`/`gaussian-field`（0 公理）；`=GFF_MEASURE_EXISTS` | S1/S3 的底测度 |
| `A_hyp` | 一维 Gauss–Hermite **超压缩性**：`‖He_n(G)‖_p≤(p-1)^{n/2}√(n!)` | **已项目内证明**（`proofs/pphi2_hypercontractivity.md`；原 Nelson 1973/`gaussian-hilbert`） | S1.5/S2 |
| `A_nelson_local` | Nelson **局部**估计 (L)：`‖e^{−H_Δ}‖_p≤C(p)`（`κ`-一致） | **已证** ⟸ `A_hyp`（`proofs/pphi2_nelson_bound.md` 定理 3.3） | S2 局部 |
| `A_PPHI2_nelson_volume` | Nelson **体积均匀**界 (V)：`‖e^{−H_Λ}‖_p≤Ce^{c|Λ|}`（`κ`-一致） | **已项目内证明**（`proofs/pphi2_nelson_dynamical_cutoff.md`，动力学截断 + 粗糙 `L²` 逐项严格；原 GJ §8.6） | S2 装配 |
| `A_PPHI2_R2_tightness` | `{μ_Λ}` 在 `S'(ℝ²)` 的**紧性**（Fröhlich 1976 / Park 1977） | 文献根（上游 5 公理） | S5（**OPEN**） |
| `A_PPHI2_u4_analyticity` | 无限体积 `u₄(λ)` 的解析性（⇒ `u₄≠0`） | 标准微扰 + 解析性（**未证**） | S7（**OPEN**） |
| `A_massgap` | 指数聚簇 / 质量间隙（团簇展开） | Glimm–Jaffe–Spencer 1974 | S6（stretch） |

**判读**：本文证明 `A` 组输入 ⟹ 定理 `MAIN`。**开放假设组**
`A_open={A_free(=GFF_MEASURE_EXISTS), A_PPHI2_R2_tightness, A_PPHI2_u4_analyticity, A_massgap}`
（2026-09-14：`A_hyp` **已项目内证明**后移除，见 `proofs/pphi2_hypercontractivity.md`；
同日 `A_PPHI2_nelson_volume`（Nelson 体积均匀界 (V)）亦**项目内证明**后移除，见
`proofs/pphi2_nelson_dynamical_cutoff.md`——动力学截断路线，含粗糙 `L²` 估计逐项严格；
`A_PPHI2_nelson_volume_locality`（H2）由引理 4.4a（卷积局部化/Young）证明后一并闭合；
critic 2026-09-14 曾补漏 `nelson_volume`/`u4_analyticity`）。故
`INTERACTING_SCALAR_2D_COMPLETE` 达 `PROVED_UNDER_ASSUMPTIONS`（假设 = `A_open`），对应 `next_gate`。

---

## S1 — Wick 序 `:P(φ):` 的良定义

### S1.1 生成函数定义与 Hermite 恒等式 `[IN-PROOF]`

设 `X` 为均零 Gaussian，`σ²=𝔼[X²]<∞`。定义**生成函数**
\[
  :e^{\alpha X}:\,:=\,e^{\alpha X-\frac12\alpha^2\sigma^2},
  \qquad
  :X^n:\,:=\,\Bigl.\frac{\partial^n}{\partial\alpha^n}:e^{\alpha X}:\Bigr|_{\alpha=0}.
  \tag{1.1}
\]

**命题 S1.1.** `Σ_{n≥0}\frac{\alpha^n}{n!}:X^n: = e^{\alpha X-\frac12\alpha^2\sigma^2}`；等价地
\[
  :X^n:\,=\,\sigma^n\mathrm{He}_n(X/\sigma),\qquad
  \mathrm{He}_n(t):=(-1)^n e^{t^2/2}\frac{d^n}{dt^n}e^{-t^2/2},
  \tag{1.2}
\]
即 `:X^n:` 是 `X` 的 `n` 次（概率论约定）Hermite 多项式。显式系数展开：
\[
  :X^n:\,=\,\sum_{j=0}^{\lfloor n/2\rfloor}
  \frac{(-1)^j\,n!}{2^j\,j!\,(n-2j)!}\,\sigma^{2j}\,X^{\,n-2j}.
  \tag{1.3}
\]
特别 `:X^0:=1`，`:X^1:=X`，`:X^2:=X^2-\sigma^2`，`:X^3:=X^3-3\sigma^2X`，
`:X^4:=X^4-6\sigma^2X^2+3\sigma^4`。

*证.* (1.1) 是 `α` 的解析函数，Taylor 展开即得级数恒等式。再由 Hermite 生成函数
`Σ\frac{\beta^n}{n!}\mathrm{He}_n(t)=e^{\beta t-\beta^2/2}`，令 `β=ασ`、`t=X/σ`：
`Σ\frac{(\alpha\sigma)^n}{n!}\mathrm{He}_n(X/\sigma)=e^{\alpha X-\alpha^2\sigma^2/2}`，与 (1.1) 逐项比较得 (1.2)。
(1.3) 由 `He_n` 的显式 Faa di Bruno 展开。∎

> **探针 P1**：SymPy 展开 (1.1) 至 `n=8`，与 (1.3) 及 `sympy.functions.special.polynomials.hermite_prob` 三路比对。

### S1.2 正交性与 Wiener 混沌 `[IN-PROOF]`

**命题 S1.2.** 对 `n,m≥0`：
\[
  \mathbb{E}\bigl[:X^n:\,:X^m:\bigr]=\delta_{nm}\,n!\,\sigma^{2n},
  \qquad
  \mathbb{E}[:X^n:]=0\ (n\ge1).
  \tag{1.4}
\]
且 `σ^{-n}:X^n:`（`n=0,1,2,…`）为 `L²(μ_X)` 的正交基（`μ_X=N(0,σ²)`）。

*证.* 用 (1.1) 的生成函数：
\[
  \mathbb{E}\bigl[:e^{\alpha X}::e^{\beta X}:\bigr]
  =\mathbb{E}\bigl[e^{(\alpha+\beta)X}\bigr]e^{-\frac12(\alpha^2+\beta^2)\sigma^2}
  =e^{\frac12(\alpha+\beta)^2\sigma^2-\frac12(\alpha^2+\beta^2)\sigma^2}
  =e^{\alpha\beta\sigma^2}.
\]
对 `α,β` 取 `∂_α^n∂_β^m|_0 = δ_{nm}n!\sigma^{2n}`。`n=0` 给 `𝔼[:X^n:]=0`。完备性由
`He_n` 是 `L²(N(0,1))` 的标准正交多项式基。∎

> **探针 P2**：用 Gauss–Hermite 求积数值算 `𝔼[:X^n::X^m:]`（`n,m≤6`，若干 `σ`），核对 (1.4)。

### S1.3 单混沌超压缩界（`A_hyp`）`[IN-PROOF]`（2026-09-14 起）

**命题 S1.3（Nelson 超压缩，单混沌情形）.** 对 `p≥2`、`p≥2`：
\[
  \bigl\|:X^n:\bigr\|_{L^p(\mu_X)}
  \;\le\;(p-1)^{n/2}\,\sigma^n\sqrt{n!}\,.
  \tag{1.5}
\]
*证（归约）.* `:X^n:=σ^nHe_n(G)`，`G=X/σ` 标准 Gaussian。`He_n` 落在 OU 半群的
`n` 本征空间，Nelson 超压缩给出 `‖He_n(G)‖_p≤(p-1)^{n/2}‖He_n(G)‖_2` 对 `p≥2`；
而 `‖He_n(G)‖_2=√(n!)`（(1.4)）。∎ 输入 = `A_hyp`，**已项目内证明**（`proofs/pphi2_hypercontractivity.md`
定理 3：Gaussian LSI ⟹ Gross 定理 ⟹ chaos-`n`），故 S1.3 现为**无条件** `[IN-PROOF]`。

> **探针 P3**：Gauss–Hermite 求积算 `‖He_n(G)‖_p/‖He_n(G)‖_2` 与上界 `(p-1)^{n/2}`（`n≤8`，`p∈{4,6,8}`）比对。

### S1.4 有限维 Wick 多项式（多元/格点）`[IN-PROOF]`

**命题 S1.4.** 设 `(φ_1,…,φ_N)` 为均零 Gaussian 向量，协方差 `C_{ij}=𝔼[φ_iφ_j]`。则
`φ_i` 的任意多项式可唯一写成 Wick 多项式的线性组合，且 `:φ_i^n:` 如 (1.3)（`σ²=C_{ii}`）。
对**不同**格点 `x≠y`，`:φ_x^{k}:` 与 `:φ_y^{l}:` 的乘积期望由 Wick 定理给出配对和；
当 `|x-y|→∞` 时（`C_m` 指数衰减）因子化为 `𝔼[:φ_x^k:]𝔼[:φ_y^l:]+O(e^{-m|x-y|})`。
*证.* 单变量归结为 S1.1–S1.2；多变量用生成函数 `𝔼[e^{Σα_iφ_i}]` 与 Isserlis（`L15`）。∎

### S1.5 局部 Wick 幂的存在性（二维）`[IN-PROOF]`（2026-09-14 起）

**命题 S1.5（Nelson；GJ 8.1.2）.** `d=2`，`k≥1`，`f∈C_c^∞(ℝ²)`。正则化族
`{∫f(x):φ^{2k}:_ε(x)dx}_ε` 在 `L^p(μ_G)`（一切 `p<∞`）中当 `ε↓0` **Cauchy**，极限
`:φ^{2k}:(f)` 与正则化选法无关。故 `:P(φ):(f)=Σ_k a_{2k}:φ^{2k}:(f)` 良定义。

*证（归约）.* 固定 UV 截断 `κ,κ'`，`:φ^{2k}:_{κ}-:φ^{2k}:_{κ'}` 由 (1.3) 是**接触项差**
`(C_κ(x,x)-C_{κ'}(x,x))` 乘低次 Wick 幂的线性组合。关键二维事实
\[
  \int_{κ'<|p|<κ}\frac{d^2p}{(2\pi)^2}\frac{1}{|p|^2+m^2}
  =\frac{1}{2\pi}\log\frac{κ}{κ'}\bigl(1+o(1)\bigr)\xrightarrow[κ,κ'\to\infty]{}0\ \text{的差值} ,
  \]
且每次接触收缩贡献一个 `K_0` 因子；二维中 `K_0(m|·|)∈L^p_{loc}(ℝ²)\ \forall p<∞`
（对数奇性可积），配合超压缩界 (1.5) 控制 Wick 幂的 `L^p` 范数、广义 Hölder 控制乘积，
得 Cauchy 性。极限的正则化无关性来自相邻截断差的同一估计。∎
输入 = `A_hyp`（**已项目内证明**）+ `K_0∈L^p_{loc}`（初等：`K_0(z)~-log z`）。故 S1.5 现为**无条件** `[IN-PROOF]`。

> **探针**：`pphi2_wick_probe.py`（待建，见 §7 待办）数值核对 `:φ⁴:_ε` 的接触项差随 `κ` 收敛。

### S1 状态
`:P(φ):` 良定义 = `[IN-PROOF]`（S1.1/S1.2/S1.4/S1.5；S1.5 的唯一非平凡输入 `A_hyp` 已项目内证明，
仅余初等 `K_0∈L^p_loc`）。
**节点 `PPHI2_WICK_ORDERING` → `PROVED_UNDER_ASSUMPTIONS`**（假设 = `K_0∈L^p_loc`，初等）。

---

## S2 — Nelson 指数界 / 超压缩

### S2.0 陈述

**定理 S2（Nelson 指数界）.** `d=2`，`P` 偶、`deg P=2n`、`P≥-c`。则存在 `c₁=c₁(P,m)<∞`，
使对一切 `p<∞` 存在 `C(p,P,m)<∞`，满足**对一切 UV 截断 `κ` 与体积 `Λ` 一致**：
\[
  \bigl\|e^{-H_{Λ,κ}}\bigr\|_{L^p(\mu_{G,Λ,κ})}
  \;\le\;C(p,P,m)\,e^{\,c_1|\Lambda|}.
  \tag{2.1}
\]
**局部（体积一致）版本**：对 `f≥0`，`supp f⊂` 单位立方 `Δ`，有 `‖e^{-∫f:P(φ):}‖_p≤C(p,P,m,f)`，
右端**与 `Λ`、`κ` 无关**。此局部版本是柱面 `asymInteracting_expMoment_volume_uniform`（`A_PPHI2_clusterexp`）的分析内核。

### S2.1 偶多项式 Wick 幂下有界（点态，`[IN-PROOF]`）

**引理 S2.1.** `:P(φ):_κ(x)=a_{2n}φ(x)^{2n}+`（低次，系数依赖 `σ_κ²=C_κ(x,x)`）。
因 `a_{2n}>0`、`2n` 偶，作为 `φ(x)` 的多项式**下有界**：`:P(φ):_κ(x)≥-b(σ_κ)`，其中
`b(σ_κ)→∞` 当 `σ_κ→∞`（例 `k=2`：`:φ⁴:≥-6σ_κ⁴`）。故点态下界**不**一致——这正是 S2 非平凡之处。
*证.* 由 (1.3)，最高次系数为 `a_{2n}>0`；偶次首一多项式下界由配方给出，其极小值随 `σ_κ^{2n}→∞`。∎

> **要点（对常见误判的更正）**：仅"`H_Λ≥-b(κ)|Λ|`"只给 `e^{-H_Λ}≤e^{b(κ)|Λ|}`，界随 `κ→∞` 发散，
> **无用**。Nelson 界的内容是：尽管点态下界发散，`e^{-H_Λ}` 的 `L^p` 范数仍**与 `κ` 一致有界**。

### S2.2 局部估计的证明结构（局部与体积均 `[IN-PROOF]`）

标准证明（Glimm–Jaffe §8.6；Simon (1974) V.5）分两步：

**(a) 频率劈裂（相格）。** 取 `C^∞` 频率截断把 `φ=φ_s+φ_f`（`φ_s` 低频、`φ_f` 高频）。
在单位立方 `Δ` 上：`φ_s` 一致有界（二维 Sobolev：`‖φ_s‖_∞≲` 低频能量）；
`φ_f` 的协方差范数小。把 `:P(φ):=:P(φ_s+φ_f):` 按 `φ_f` 的 Wick 幂展开（二项式–Hermite 展开），
用单混沌界 (1.5) 逐项控制 `φ_f` 的贡献，对 `φ_s` 用 Stirling/Taylor。得
\[
  \bigl\|e^{-∫_Δ f:P(φ):}\bigr\|_{L^p(\mu_G)}\le C(p,P,m,f)<\infty,
  \tag{2.2}
\]
**与 `κ`、`Λ` 无关**。此步只用到 `A_hyp` + 初等估计，是"局部化"的实质。`[IN-PROOF]`
（`proofs/pphi2_nelson_bound.md` §3–§4；局部 (L) 与有限性 (F) 均已证）。

**(b) 体积装配。** 把 `H_Λ=∫_Λ:P(φ):` 按频率阈值 `T` 劈裂 `C=C_S+C_R`、`φ=φ_S+φ_R`，
`V_Λ=V_S(φ_S)+E_R`（Wick 二项式）；光滑侧确定性下界 `V_S≥−C₁(1+\log T)^D|Λ|`；
粗糙侧用**本项目自证超压缩**得混沌浓度 `P(|E_R|>λ)≤exp(−c_D(λ/‖E_R‖₂)^{2/D})` 与
粗糙误差 `L²` 估计 `‖E_R‖₂²≤C(P,m)|Λ|(1+\log T)^D(1+\log κ)^D T^{−2}`；取 `T=T(M)` 平衡、
层饼积分（`t₀`-劈裂）得 `𝔼[e^{−pV_Λ}]≤K(p)e^{c|Λ|}`，即 (2.1)。`[IN-PROOF]`
（**`proofs/pphi2_nelson_dynamical_cutoff.md`**：全 6 步严格；粗糙 `L²` 逐项证到严格（引理 4.5–4.9），
`κ`-一致指数由引理 4.10 + 定理 6.2 证；卷积局部化引理 4.4a 使证明对任意有界 `Λ` 通用）。

**结论**：定理 S2 = (a) + (b)，**两步均 `[IN-PROOF]`**（(a) ⟸ `A_hyp`，`proofs/pphi2_hypercontractivity.md`；
(b) 动力学截断，`proofs/pphi2_nelson_dynamical_cutoff.md`）。
**节点 `PPHI2_NELSON_BOUND` → `PROVED`**（无条件；`A_hyp`、`A_PPHI2_nelson_volume` 均已项目内证明）。

> **路线更正（2026-09-14）**：(b) 的**主攻路线**先登记为上游的 Newman/Lee–Yang MGF（那是 CYL-1a，**不同对象**、
> 更强）；实际采用并**证成**的是**动力学截断**（Glimm–Jaffe Ch. 8；亦上游证环面 Nelson 界 0 公理之法），
> 残余的粗糙 `L²` 估计经逐项严格化后闭合。

> **P1 更新（2026-09-13）/ 闭合（2026-09-14）**：局部估计 (L)（`pphi2_nelson_bound.md` 定理 3.3）与
> 有限性 (F)（命题 4.1）已证 ⇒ S3 无条件闭合；**体积均匀界 (V) 亦已项目内证得**（动力学截断 + (L2) 逐项严格），
> **无条件**——唯一约定 H1（固定光滑频率截断 `χ`）是**正则化方案定义**而非数学假设（`c=c(P,m,χ)`，
> 而 (V) 只要求 `c` 与 `p,κ,Λ` 无关）。

> **探针 P4**：单混沌指数矩：数值算 `𝔼[e^{t\,\mathrm{He}_n(G)}]`（`n=2,4`）的收敛半径下界，
> 与 (1.5) 的 `p`-界自洽；确认 `e^{-t:φ⁴:}` 在固定正则化下 `L^p` 可积。

---

## S3 — 有限体积相互作用测度

**命题 S3.1.** 在定理 S2（p=1）下，`0<Z_Λ=∫e^{-H_Λ}dμ_G<∞`。
*证.* `e^{-H_Λ}>0` 且 `∈L¹(μ_G)`（(2.1)，`p=1`），故 `Z_Λ∈(0,∞)`。∎

**命题 S3.2.** `μ_Λ=Z_Λ^{-1}e^{-H_Λ}μ_G` 为 `S'` 上概率测度；对一切 `f_1,…,f_j`，
\[
  \mathbb{E}_{\mu_\Lambda}\!\left[\prod_{i}\varphi(f_i)\right]
  =Z_\Lambda^{-1}\!\int\prod_i\varphi(f_i)\,e^{-H_\Lambda}d\mu_G
  <\infty .
  \tag{3.1}
\]
*证.* `∏φ(f_i)∈L^{p'}(μ_G)`（(1.5)+广义 Hölder），`e^{-H_Λ}∈L^p`（S2），取 `1/p+1/p'=1`
（`p` 任意，故 `p'` 任意）由 Hölder 得被积函数 `∈L¹`；`Z_Λ>0`。归一化因子使 `∫μ_Λ=1`。∎

**命题 S3.3（Schwinger 函数）.** `S_n^{Λ}(x_1,…,x_n):=𝔼_{μ_Λ}[∏φ(x_i)]`（配以适当正则化）为 `S'` 元素，
且含 `e^{-H_Λ}` 的卷积结构（即 `S_n^Λ` 由自由 Wick 期望与 `:P:` 的顶点展开给出）。
*证.* 由 (3.1) + `:P:` 的生成泛函展开（S1）逐项配对。∎

**节点 `PPHI2_MEASURE_EXISTS` → `PROVED_UNDER_ASSUMPTIONS`**（有限体积 `[IN-PROOF]`；
无限体积极限见 S5，输入 `A_PPHI2_R2_tightness`）。

---

## S4 — OS 反射正定性（GRS 格点转移）`[IN-PROOF]`

本节是本文**最强的内部闭合**：RP 从自由场传递到相互作用测度，证明只用到"相互作用关于反射对称且在反射面两侧因式分解"。

**定理 S4.** 设正则化测度 `μ_{Λ,ε}=Z^{-1}e^{-H_{Λ,ε}}μ_{G,Λ,ε}`，`Λ` 关于 `θ` 对称，
`H_{Λ,ε}=H_+ + θH_+`（`H_+` 只依赖 `{x₀≥0}` 的场）。若自由测度 `μ_{G,Λ,ε}` 反射正定，则 `μ_{Λ,ε}` 反射正定：
\[
  \int (\theta F) F\,d\mu_{Λ,ε}\;\ge\;0,\qquad\forall F\in\mathcal A_+ .
  \tag{4.1}
\]

*证.* 记 `G:=F\,e^{-H_+}\in\mathcal A_+`（`F∈\mathcal A_+`，`e^{-H_+}\in\mathcal A_+`）。
由 `H=H_++\theta H_+`、`θ(ab)=(θa)(θb)`、`θH_+=H_-`：
\[
  (\theta G)\,G=(\theta F)(\theta e^{-H_+})\,F\,e^{-H_+}=(\theta F)F\,e^{-\theta H_+}e^{-H_+}=(\theta F)F\,e^{-H}.
\]
于是
\[
  \int(\theta F)F\,e^{-H}d\mu_G=\int(\theta G)G\,d\mu_G\;\ge\;0,
\]
最后一步用**自由测度**的 RP（对 `G∈\mathcal A_+`）。再除以 `Z>0` 得 (4.1)。∎

**推论 S4.1（有限体积 RP）.** `μ_{Λ,ε}` 关于 `x₀=0` 反射正定。自由格点测度的 RP 由
**转移矩阵** `T=e^{-ε H_0}`（`H_0` 格点 Hamilton 量）的自伴正性给出（标准的 GRS 格点转移，
对应 `RP_QUADRATIC_FORM` 的格点版本）。

**推论 S4.2（连续极限 RP）.** 对 `F∈𝒜_+` 使 `θF·F` 连续有界，`∫(θF)F dμ_{Λ,ε}≥0` 在
`ε↓0`（及 `Λ↑`，S5）下取极限仍 `≥0`（弱收敛下连续有界函数的积分收敛）。故无限体积极限 `μ` 反射正定，
即 **OS1/OS3（RP 部分）**。

> **⚠ 极限次序约定（critic 2026-09-14）**：上述"`ε↓0`（及 `Λ↑`）"**未**指定次序与一致性。
> 本文的约定（与 GJ/GRS 一致）为**先 `ε↓0`（固定 `Λ`）、再 `Λ↑`**：
> 第一步用推论 S4.1（固定 `Λ` 的格点 RP）取 `ε↓0`，第二步用 S5 的紧性取 `Λ↑`。
> **需要但本文未证的**：`Z_{Λ,ε}` 的 `ε`-一致有界（固定 `Λ`）——由 S3 的有限体积界（**已证**）
> 提供 `ε`-一致性；而 `Λ↑` 与 `ε↓0` 的**换序**本文不主张（留作残余，归 S5）。
> RP 的极限保持**只**用到 `θF·F` 的连续有界性与弱收敛，不依赖换序。

**节点 `PPHI2_OS_POSITIVITY` → `PROVED_UNDER_ASSUMPTIONS`**（假设 = `RP_QUADRATIC_FORM`
（自由场 RP，PUA）+ 弱闭包性（初等））。
> 与已闭合的 `proofs/rp_chain.md`（Schur 归约 RP）对接：自由场 RP 是起点，本定理给出相互作用的**增量**。

---

## S5 — ℝ² 无限体积极限（紧性）`[REDUCED]` / `[LIT-ROOT]`

### S5.1 紧性判据与归约

**命题 S5.1（紧性 ⟹ 极限）.**
若 `{μ_Λ}` 在 `S'(ℝ²)` 上**紧**（Prokhorov），则存在弱极限点 `μ`；且
OS0/OS1/OS2/OS4 在弱极限下**保持**（RP 由 S4.2；欧氏不变性由有限体积近似的不变性取极限；
聚簇/正则性同理）。此为 `pphi2_limit_exists` 的抽象内核。

**命题 S5.2（Nelson 界 ⟹ 紧性，归约）.** 由定理 S2 的**体积一致**指数矩界，配合
`S'` 上紧性的 **Mitoma 判据**（有限维投影的胎紧性 + 一致矩界），得 `{μ_Λ}` 紧。
具体地，需对一族"测试函数格"给出一致界：
\[
  \sup_\Lambda\ \mathbb{E}_{\mu_\Lambda}\!\left[\Bigl(\int \varphi(f)\,d\mu_\Lambda\Bigr)^2\right]
  \;+\;\sup_\Lambda\ \mathbb{E}_{\mu_\Lambda}\bigl[e^{\,c\int_{\Delta}:φ^2:}\bigr]<\infty
  \qquad(f\in\mathcal S),
\]
其中第一式由 (3.1) 的 `n=2` 矩 + `A_update`（质量重整）给出，第二式即 S2 的局部界。
**结论**：S5 = S2（已归约）+ Mitoma 判据（初等泛函分析）+ **质量重整/一致两点界**（`A_PPHI2_R2_tightness` 的分析输入）。

### S5.2 上游 5 条紧性公理的对齐

| 上游公理 | 本文对应 | 判定 |
|---|---|---|
| `continuum_exponential_moment_bound` | (2.1) 的体积一致版 | `[IN-PROOF]`（S2，`A_PPHI2_nelson_volume` 已证） |
| `continuum_exponential_clustering` | `C_m` 指数衰减 + 装配 | `A_massgap`（S6） |
| `canonical_continuumMeasure_cf_tendsto` | 特征泛函在 `ε↓0` 收敛 | 由 S1/S3 + 弱收敛，`[IN-PROOF]` |
| `pphi2_limit_exists` | 命题 S5.1/S5.2 | `[REDUCED]`（`A_PPHI2_R2_tightness`；Mitoma 归约已证） |
| `rotation_cf_defect_polylog_bound` | OS2 旋转缺陷的多对数界 | `[LIT-ROOT]`（上游 scoped；本项目暂留） |

**节点 `PPHI2_MEASURE_EXISTS`（无限体积部分）**：输入 `A_PPHI2_R2_tightness`；状态不高于
`PROVED_UNDER_ASSUMPTIONS`。

---

## S6 — 质量间隙 / 粒子结构 `[LIT-ROOT]`（stretch）

**定理 S6（GJS 1974）.** 弱耦合 `P` 下的 P(φ)₂ 具**指数聚簇**（`S_n` 连接部分按 `e^{-m_phys|x|}` 衰减），
等价于转移算子谱间隙 `m_phys>0`，且存在孤立质量壳 ⇒ 粒子结构。
*归约.* 由 S2 的一致指数矩 + 团簇展开（Glimm–Jaffe–Spencer 1974；Spencer Erice 1973）。
本文**不**复现该展开（形式化成本极高），登记为 `A_massgap`。
**节点 `PPHI2_MASS_GAP` 保持 `LITERATURE_SUPPORTED`。**

---

## S7 — 非平凡性（`u₄≠0`）`[IN-PROOF]`（微扰首阶）

**命题 S7.1.** 设 `P(X)=\frac{\lambda}{4!}X^4+\frac12\delta m^2 X^2`，`λ>0` 小。则小 `λ` 下
连接四点函数
\[
  u_4(x_1,\dots,x_4)=-\lambda\int_{\mathbb R^2} dy\;
  C_m(x_1-y)C_m(x_2-y)C_m(x_3-y)C_m(x_4-y)\;+\;O(\lambda^2),
  \tag{7.1}
\]
故 `u_4\neq0`（首阶系数 `<0`）。

*证.* `dμ_Λ∝e^{-H_Λ}dμ_G=Z^{-1}\bigl(1-\frac{\lambda}{4!}∫:φ^4:(y)dy+O(λ^2)\bigr)dμ_G`。
自由（`λ=0`）测度为 Gaussian，故 `u_4^{(0)}=0`。`O(λ)` 项：连接部分由
`-\frac{\lambda}{4!}∫dy\,\bigl<\varphi_1\varphi_2\varphi_3\varphi_4:\varphi^4:(y)\bigr>_G^{conn}` 给出。
把 `:\varphi^4:(y)=\varphi(y)^4-6C(0)\varphi(y)^2+3C(0)^2` 展开，Wick 配对：四个 `φ(y)` 全连到
`x_1,\dots,x_4` 有 `4!` 种，余下接触项给不连接（或低阶）贡献。故 `O(λ)` 连接部分
`=-\frac{\lambda}{4!}\cdot4!\int_\Lambda dy\prod_{i=1}^4C_m(x_i-y)=-\lambda\int_\Lambda\prod_i C_m(x_i-y)dy`。
`∫dy\prod C_m(x_i-y)<\infty`（每个因子 `~e^{-m|x_i-y|}`，四重指数衰减可积）且 `>0`，故首阶 `<0`。
`u_4(λ)` 在 `|λ|<λ_0` 内解析（有限体积由 S2 的指数界 + 支配收敛；**无限体积见下**），
`u_4(0)=0`，`u_4'(0)\neq0` ⇒ 小 `λ>0` 时 `u_4(λ)\neq0`。∎

> **⚠ 更正（critic 2026-09-14）**：上式"无限体积由 S5"**不成立**——S5 只给 `{μ_Λ}` 的**紧性**，
> **不**蕴含 `u_4(λ)` 在 `λ` 上的解析性（紧性给子列极限，不给 `λ`-一致收敛到解析函数）。
> 正确的口径：有限体积 `u_4^{Λ}(λ)` 的解析性由 S2 的 `L^p` 界 + 支配收敛给出（**`[IN-PROOF]`**）；
> **无限体积** `u_4(λ)` 的解析性是一个**独立假设**，显式登记为 `A_PPHI2_u4_analyticity`（**OPEN**）。

**节点 `PPHI2_NONTRIVIALITY` → `PROVED_UNDER_ASSUMPTIONS`**（假设 = `A_PPHI2_u4_analyticity`
（无限体积解析性，**OPEN**，归约到团簇展开））。**已证部分** = 有限体积首阶
`u_4^{Λ}=−λ∫_Λ∏C_m+O(λ²)` 及解析性（`A_PPHI2_nelson_volume` 已项目内证明，不再列为假设）。
> **对齐上游**：上游 `continuumLimit_nonGaussian`（`u₄≠0`）在 T² 上**无公理**；本文在 ℝ² 上给出
> 微扰首阶证明，二者相容（T² 的轴对称把首阶简化为单积分）。

> **探针 P6**：符号/数值核对 (7.1) 的系数：一维/圆周对称版本的 `∫∏C` 数值积分 `>0`，且 `u_4` 首阶 `<0`。

---

## S8 — 证据台账与状态建议

| 节点 | 本文步骤 | 证据类型 | 建议状态 | 假设 |
|---|---|---|---|---|
| `PPHI2_WICK_ORDERING` | S1.1–S1.5 | `proof` + `symbolic`(P1/P2/P3) | **PROVED_UNDER_ASSUMPTIONS** | `K_0∈L^p_loc`（初等） |
| `PPHI2_NELSON_BOUND` | S2.1–S2.2 | `proof` + `paper` + `numeric`(P4) | **PROVED** | 无（`A_hyp`/`A_PPHI2_nelson_volume` 均已项目内证明） |
| `PPHI2_MEASURE_EXISTS` | S3, S5 | `proof` + `paper` | **PROVED_UNDER_ASSUMPTIONS** | `A_tight` |
| `PPHI2_OS_POSITIVITY` | S4 | `proof` | **PROVED_UNDER_ASSUMPTIONS** | `RP_QUADRATIC_FORM` |
| `PPHI2_NONTRIVIALITY` | S7 | `proof` + `numeric`(P6) | **PROVED_UNDER_ASSUMPTIONS** | `A_PPHI2_u4_analyticity` |
| `PPHI2_MASS_GAP` | S6 | `paper` | LITERATURE_SUPPORTED（不变） | `A_massgap` |
| `INTERACTING_SCALAR_2D_COMPLETE` | 全部 | `proof` + `paper` | **PROVED_UNDER_ASSUMPTIONS**（= `next_gate`） | `𝒜` |

**milestone 定级说明**：`MASS_GAP` 仍为 `LITERATURE_SUPPORTED`（不同轴）。里程碑取 requires 的
**种类合成**而非简单最小：装配链 = `proof`，硬分析步 = 具名 `paper` 输入且逐条登记，故
`PROVED_UNDER_ASSUMPTIONS`（"在显式额外假设下证明"）成立——**不**声称把 GJS/Fröhlich–Park 在项目内证明。

---

## S9 — 残余缺口（"解决上游问题"的攻击清单）

| # | 缺口 | 攻击路线 | 归属 |
|---|---|---|---|
| ~~G1~~ | ~~Nelson 体积装配 = `A_PPHI2_nelson_volume`~~ **已闭合（2026-09-14）** | 动力学截断（Glimm–Jaffe Ch. 8）+ 粗糙 `L²` 逐项严格；**`proofs/pphi2_nelson_dynamical_cutoff.md`** | S2 ✅ |
| G2 | `A_PPHI2_R2_tightness` 的质量重整/一致两点界 | 统一归约为**指数聚簇**（⟸ 团簇展开 GJS）；Mitoma 归约 **已证**（P2 定理 3.1） | S5 |
| G3 | `A_massgap`（团簇展开） | 先纸面（GJS）；形式化成本极高，暂留文献根 | S6 |
| G4 | `rotation_cf_defect_polylog_bound` | 上游 scoped；评估本项目自证 | S5.2 |
| G5 | 上游 keystone **#18**（弱耦合唯一性） | 与 G3 同族（团簇展开/Dobrushin） | S6/上游 |
| **G-core** | **`PPHI2_CLUSTER_EXPANSION`**（GJS 团簇展开收敛） | **统一硬核**：G2/G3/G5 + `u₄` 解析性全部归约到它（`proofs/pphi2_cluster_expansion_core.md`）；或 import 上游 | 全部 |

**下一步（P0–P4）**：
- **P0**：本文 S1 的 Lean 片段（有限维 Wick/Hermite 恒等式 + 正交性，类比已闭合的 S6 Isserlis 核）。
- **~~P1~~（已闭合）**：`A_PPHI2_nelson_volume`（G1）——动力学截断路线项目内证得。
- **P2**：攻 `A_PPHI2_R2_tightness` 的质量重整（G2）——**已统一归约为团簇展开**。
- **P4**：`PPHI2_CLUSTER_EXPANSION`（G-core，唯一残余硬核）——项目内证 GJS 或 import 上游作基线。

---

## S10 — 依赖与边界

- **使用**：`A_free`（`GFF_MEASURE_EXISTS`，文献/共享栈）、`A_hyp`（Nelson 超压缩，**已项目内证明**，见
  `proofs/pphi2_hypercontractivity.md`）、`A_PPHI2_nelson_volume`（**已项目内证明**，见
  `proofs/pphi2_nelson_dynamical_cutoff.md`）、`A_PPHI2_R2_tightness`（Fröhlich/Park，归约到 GJS）、
  `A_PPHI2_u4_analyticity`、`A_massgap`（GJS）、
  `RP_QUADRATIC_FORM`（自由场 RP，PUA）、Wick/Isserlis（`L15`）、`K_0∈L^p_loc`（初等）。
- **不使用/不主张**：本文**不**证明 Minlos（`A_free` 为输入）、**不**证明 Fröhlich/Park 紧性、
  **不**证明 GJS 质量间隙 / 团簇展开；亦不涉及 OS 重构定理本体（属第一里程碑）。
- **不重做**：`C_m` 闭式/分布恒等式（S1 已 PROVED，第一里程碑）、Bessel 解析恒等式、Isserlis 核（Lean 已闭合）。
- **状态定级**：见 §8。**零 sorry ≠ 闭环**：`A_PPHI2_R2_tightness`/`A_PPHI2_u4_analyticity`/`A_massgap`
  （及统一硬核 `PPHI2_CLUSTER_EXPANSION`）必须在 `A_PPHI2.yaml` 显式登记，不得被下游引用为"假设已消除"。
- **数值/符号断言**：`verify/pphi2_global_probe.py`（P1 Hermite 恒等式；P2 正交性；
  P3 超压缩界；P4 指数矩/`K_0`; P5 转移矩阵 RP 因子化；P6 非平凡性首阶）。

## 修订记录
- 2026-09-13：建立。P(φ)₂ 全局纸面证明闭合：S1–S7 + 证据台账 + 残余缺口。S4（RP 传递）为内部闭合；
  S1/S3/S7 部分内部闭合；S2/S5/S6 归约到具名输入。
- 2026-09-14：**critic 复核后修正**（独立 critic 报 REJECT，见 `proof_graph/reviews/`）：
  (1) §S7 的"无限体积解析性"**不成立**——已改为显式假设 `A_PPHI2_u4_analyticity`（OPEN），
      `PPHI2_NONTRIVIALITY` 的假设字段改正；
  (2) 开放假设组 `A_open` **补漏** `A_PPHI2_nelson_volume` / `A_PPHI2_u4_analyticity`（初稿错列为
      已证的 `A_nelson_local`，且漏列体积项）；
  (3) §S4.2 增**极限次序约定**（先 ε↓0、再 Λ↑；换序为残余）；
  (4) 上游 `lean` 证据条目改标 `paper`（避免对**非本对象**的 Lean 误升 `FORMALIZED`）。
  相应修正见 `proofs/pphi2_nelson_bound.md`（κ-一致性的对角劈裂证明、(3.3) 指数笔误）、
  `proofs/pphi2_nelson_volume.md`（删除循环等价链、(KP) 行降为 `[REDUCED]`）。
- 2026-09-14：**`A_hyp` 项目内闭合后的同步**（`proofs/pphi2_hypercontractivity.md`，critic `ACCEPT_WITH_FIXES`）：
  (a) `A_open` 移除 `A_hyp`（假设组表与 §S0 判读更新）；(b) §S1.3（单混沌超压缩）/§S1.5（二维局部 Wick 幂）
  由 `[REDUCED]` 升 `[IN-PROOF]`（其唯一输入 `A_hyp` 已证；S1.5 残余仅剩初等 `K_0∈L^p_loc`）；
  (c) §S2.2 局部估计 (a) 现**无条件**；(d) §S8 台账 `PPHI2_WICK_ORDERING`/`PPHI2_NELSON_BOUND` 假设字段改正。
- 2026-09-14：**路线更正**（读上游 discharge plans，见 `docs/upstream/pphi2/discharge_plans.md`）：
  §S2 的 (b) 体积装配（`A_PPHI2_nelson_volume`）**主攻路线**改列为上游的 **Newman/Lee–Yang MGF 高斯支配 +
  柱面转移矩阵质量间隙**（非团簇展开）；§S5 的 R² 残余参考精确化为 **Fröhlich 1976 / Park 1977 紧性路线**
  （排除 GRS/GKS）。
- 2026-09-14：**`A_PPHI2_nelson_volume`（(V)）项目内闭合 — 同步全局**（`proofs/pphi2_nelson_dynamical_cutoff.md`，
  critic `ACCEPT_WITH_FIXES`，`proof_graph/reviews/pphi2_nelson_volume_review.md`）：
  (a) §S0 假设表 `A_PPHI2_nelson_volume` 标 **已项目内证明**；`A_open` 移除之（及 `A_PPHI2_nelson_volume_locality`，
  由引理 4.4a 卷积局部化/Young 证）；
  (b) §S2.2 (b) 体积装配由 `[REDUCED]` 升 **`[IN-PROOF]`**（动力学截断 6 步 + 粗糙 `L²` 逐项严格），
  节点 `PPHI2_NELSON_BOUND` → **`PROVED`**（无条件）；
  (c) §S5.2 表 `continuum_exponential_moment_bound` 改 `[IN-PROOF]`；
  (d) §S8 台账 `PPHI2_NELSON_BOUND` 假设清空、`PPHI2_NONTRIVIALITY` 移除 `A_PPHI2_nelson_volume`；
  (e) §S9 **G1 关闭**，新增统一硬核行 **G-core `PPHI2_CLUSTER_EXPANSION`**（吸收 G2/G3/G5 与 `u₄` 解析性）；
  (f) §S10 边界更新。**里程碑残余 = 单一经典硬核（GJS 团簇展开）**。
