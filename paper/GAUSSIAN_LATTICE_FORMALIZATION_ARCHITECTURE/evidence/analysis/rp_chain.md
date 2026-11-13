# Proof — RP 链：Schur 归约下的反射正性（FRONTIER_RP_CHAIN）

> 对应前沿：`FRONTIER_RP_CHAIN`。对应节点：`RP_COVARIANCE` / `RP_QUADRATIC_FORM` /
> `RP_GRAM_PSD` / `SCHUR_PRODUCT_PSD` / `GAUSSIAN_RP_FROM_COVARIANCE`。
> 输入：`proofs/os1_reflection_positivity.md`（RP-COV/RP-QUAD，命题 1–3）、
> `proofs/schwinger_bessel.md`（Schwinger 参数化绝对可积性）、`S1_DISTRIBUTION_IDENTIFICATION`（PROVED）、
> `GFF_MEASURE_EXISTS`（Minlos 测度存在 + Gaussian 特征函数公式，文献/IMPORTED_UPSTREAM）。
> 不使用 S3/S6 `green_identity` 反向回灌；不把数值 Gram 探针（`verify/osc_os1_probe.py`）当证明。
> 上游依据：arXiv:2603.15770 B.4(i)（B.19）–（B.26）；OS (1975) 重构定理。

本文件的作用有两点：
1. 把论文 B.4(i) 的 **Schur–Hadamard 归约**（"协方差反射正性 ⇒ 生成泛函反射正性"）
   落成项目内可审计的**无条件步骤**，并给出两个独立的线性代数引理；
2. 把 `RP_GRAM_PSD` 从数值必要条件**升级为纸面证明**（它是 `RP_QUADRATIC_FORM` 的推论），
   并核对 AImath 空间 Fourier 路线与论文（B.19）–（B.26）的**常数/测度约定**（前沿卡 N3）。

---

## 0. 约定与两条路线的等价

沿用 `proofs/os1_reflection_positivity.md` §0：`m>0`，`C_m` 为四维大质量自由标量协方差，
时间反射 `\theta(t,\mathbf x)=(-t,\mathbf x)`，正时间测试空间 `\mathcal S_+`（支集含于 `\{t\ge0\}`），
`\omega_{\mathbf p}=\sqrt{|\mathbf p|^2+m^2}\ge m`。对复测试函数用**共轭线性**配对
\[
 \langle f,g\rangle_C:=\int_{\mathbb R^4}\!\!\int_{\mathbb R^4}
 \overline{f(x)}\,C_m(x-y)\,g(y)\,dx\,dy,
\]
它 Hermitian（`C_m` 实值偶）且满足反射不变性 `\langle\theta f,\theta g\rangle_C=\langle f,g\rangle_C`。
`C_m` 的 Bessel 闭式 `C_m(x)=mK_1(m|x|)/(4\pi^2|x|)` 来自 `S1_DISTRIBUTION_IDENTIFICATION`（PROVED）。

**N3 核对（AImath 空间 Fourier 路线 vs 论文 B.24–B.26）**。

论文（B.24）取协方差
`K(x,y)=\int d^3k\,dk_0\,(k^2+m^2)^{-1}e^{-ik_0(x^0+y^0)+i\vec k\cdot\vec x}`（**无** `(2\pi)` 因子），
（B.25）用 `\int_{\mathbb R}dk_0/(k_0^2+\omega^2)\,e^{-ik_0\tau}=(\pi/\omega)e^{-\omega|\tau|}`，
（B.26）得 `\int d^3k\,(\pi/\omega_k)\,\bigl|\int dt\,f(t,\vec k)e^{-\omega_k t}\bigr|^2\ge0`。
AImath `proofs/os1_reflection_positivity.md`（1）–（7）取
`C_m=\int d^4p/(2\pi)^4\,e^{ip\cdot(x-y)}/(p^2+m^2)`，得
`Q_m(f)=\int d^3p/(2\pi)^3\,|F_f(\mathbf p)|^2/(2\omega_{\mathbf p})`。

逐项核对：
- 一维时间积分：`(\pi/\omega)/(2\pi)=1/(2\omega)`，与 AImath（2）一致；✓
- 四维核归一化：论文 `K` 与 AImath `C_m` 相差因子 `(2\pi)^4`；
- 二次型：每 `d^3k` 的权重比 `(\pi/\omega)\big/\big[(2\omega)^{-1}(2\pi)^{-3}\big]=(2\pi)^4`，
  与核归一化因子一致；
- 时间变量：论文 `|x^0+y^0|`，在 `f\in\mathcal S_+`（正时间）时 `x^0,y^0\ge0`，
  故 `|x^0+y^0|=x^0+y^0`，与 AImath 的 `e^{-\omega(t+s)}` 一致。✓

**结论**：两路线**只差一个正的常数因子 `(2\pi)^4`**；由于反射正性是正齐次的（`Q\ge0`
在正标量下不变），两式等价。前沿卡 N3（"核对常数约定"）由此**判定为纯约定差异，无实质缺口**：
AImath 的 `Q_m(f)=\int|F_f|^2/(2\omega)\ge0` 即论文（B.26）的同一定理。

---

## 1. 引理 A（Schur 乘积定理）

**引理 A**：设 `A,B\in M_n(\mathbb C)` 为 Hermitian 半正定（PSD）。
则其 Hadamard（逐项）乘积 `A\circ B`（`(A\circ B)_{ij}=A_{ij}B_{ij}`）PSD。

**证明**：由 Hermitian 矩阵谱定理，
`A=\sum_{r}\lambda_r\,a_r a_r^*`（`\lambda_r\ge0`，`a_r\in\mathbb C^n`），
`B=\sum_{s}\mu_s\,b_s b_s^*`（`\mu_s\ge0`）。对任意向量 `u,v` 记逐项乘积向量
`u\circ v:=(u_kv_k)_k`。直接计算
\[
 \bigl[(u\circ v)(u\circ v)^*\bigr]_{kl}
 =(u_kv_k)\overline{(u_lv_l)}
 =(u_k\overline{u_l})(v_k\overline{v_l})
 =[uu^*]_{kl}\,[vv^*]_{kl},
\]
即 `(u\circ v)(u\circ v)^*=(uu^*)\circ(vv^*)`。于是
\[
 A\circ B=\sum_{r,s}\lambda_r\mu_s\,(a_ra_r^*)\circ(b_sb_s^*)
 =\sum_{r,s}\lambda_r\mu_s\,(a_r\circ b_s)(a_r\circ b_s)^* .
\]
每个 `(a_r\circ b_s)(a_r\circ b_s)^*` 是秩一 PSD，系数 `\lambda_r\mu_s\ge0`，
故 `A\circ B` 为 PSD 的非负组合。\(\square\)

**推论 A.1（Hadamard 幂）**：`A` PSD ⇒ 对每个整数 `k\ge1`，`A^{\circ k}`（逐项 `k` 次幂）PSD。
（对 `k` 归纳：`A^{\circ k}=A^{\circ(k-1)}\circ A`，用引理 A；`A^{\circ1}=A`。）

**推论 A.2（对角相似）**：`A` PSD，`D=\operatorname{diag}(d_i)` 实对角 ⇒ `DAD` PSD。
（`(DAD)_{ij}=d_iA_{ij}d_j`；`u^*DADu=(Du)^*A(Du)\ge0`。）

**注 A.3（Lean 覆盖度）**：核对的 `scratch/up-bochner/Bochner/PositiveDefinite.lean`
含**函数级** Schur 引理（正定函数逐点乘积，`IsPositiveDefinite.mul`），
不是矩阵级 Hadamard 定理。本项目按引理 A 自证（纸面）；Lean 形式化可自证或移植该
函数级引理（见 §5 状态与缺口说明）。

---

## 2. 引理 B（PSD 矩阵的逐项指数仍 PSD）

**引理 B**：设 `A\in M_n(\mathbb C)` Hermitian PSD。定义逐项指数
`(\exp\circ A)_{ij}:=e^{A_{ij}}`。则 `\exp\circ A` PSD。

**证明**：由 `e^{z}=\sum_{k\ge0}z^k/k!` 逐项应用，
\[
 (\exp\circ A)_{ij}=e^{A_{ij}}=\sum_{k=0}^\infty\frac{A_{ij}^k}{k!}
 =\sum_{k=0}^\infty\frac{(A^{\circ k})_{ij}}{k!},
\]
即 `\exp\circ A=\lim_{N\to\infty}S_N`，`S_N:=\sum_{k=0}^N A^{\circ k}/k!`。
由推论 A.1 每个 `A^{\circ k}` PSD，故有限和 `S_N` 是 PSD 矩阵的非负组合，PSD。
级数按元素绝对收敛（`|A_{ij}|\le\|A\|_2` 给出 `|e^{A_{ij}}|` 有限）。
PSD 集合在逐元素极限下闭：对每个 `u`，`u^*S_Nu\ge0` 且 `u^*S_Nu\to u^*(\exp\circ A)u`
（有限维，逐元素收敛 ⇒ 二次型收敛），故 `u^*(\exp\circ A)u\ge0`。\(\square\)

**注 B.1（与既有命题 4 的关系）**：`proofs/os1_reflection_positivity.md` 命题 4 给出的
另一证明（`B_{ij}=\langle v_i,v_j\rangle` ⇒ `e^{B_{ij}}=\sum_k\langle v_i^{\otimes k},v_j^{\otimes k}\rangle/k!`）
与引理 B 等价：引理 B 走 Hadamard 幂（Schur 路线，论文 B.4(i)），命题 4 走张量幂
（Gram 路线）。两路线在此互为独立复核。

---

## 3. 命题 C（RP_COVARIANCE）与命题 D（RP_QUADRATIC_FORM / RP_GRAM_PSD）

**命题 C（协方差反射正性）**：对任意 `f_1,\dots,f_n\in\mathcal S_+` 与 `c\in\mathbb C^n`，
矩阵
\[
 R_{ij}:=C_m(\theta f_i,f_j)=\langle\theta f_i,f_j\rangle_{\!C}
 \quad\text{满足}\quad
 \sum_{i,j}\overline{c_i}c_jR_{ij}\ge0 ,
\]
即 `R=(R_{ij})` Hermitian PSD。

**证明**：Hermitian 性：
`R_{ji}=\langle\theta f_j,f_i\rangle_C=\overline{\langle f_i,\theta f_j\rangle_C}
=\overline{\langle\theta f_i,f_j\rangle_C}=\overline{R_{ij}}`
（用 `\langle a,b\rangle_C=\overline{\langle b,a\rangle_C}` 与 `\langle\theta a,\theta b\rangle_C=\langle a,b\rangle_C`）。
PSD 性：令 `f=\sum_ic_if_i\in\mathcal S_+`。由 `proofs/os1_reflection_positivity.md`
命题 3（RP-QUAD），
\[
 0\le Q_m(f)=\int_{H_+}\!\!\int_{H_+}\overline{f(x)}C_m(\theta x-y)f(y)\,dx\,dy
 =\sum_{i,j}\overline{c_i}c_j\,R_{ij},
\]
最后一式是双线性展开（`f_i` 实值取复线性延拓）。\(\square\)

**命题 D（RP_QUADRATIC_FORM 与 Gram PSD）**：对 `f=\sum_ic_if_i`（`f_i\in\mathcal S_+`），
\[
 Q_m(f)=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}\frac{|F_f(\mathbf p)|^2}{2\omega_{\mathbf p}}
 =\sum_{i,j}\overline{c_i}c_j\,G_{ij},
 \qquad
 G_{ij}:=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac{\overline{F_{f_i}(\mathbf p)}F_{f_j}(\mathbf p)}{2\omega_{\mathbf p}},
\]
且 `G` **PSD**（`G=R`）。特别地，对任意有限点集/有限测试族，反射 Gram 矩阵 PSD。

**证明**：`Q_m(f)=\int|F_f|^2/(2\omega)\ge0` 即 `proofs/os1_reflection_positivity.md`（7）；
`F_f=\sum_ic_iF_{f_i}` 给出双线性展开；`G` 是加权 `L^2` 内积下的 Gram 矩阵，故 PSD。
`G=R` 由（1）–（7）的双线性形式逐项比对（命题 C 已给出 `R` PSD）。\(\square\)

**注 D.1（RP_GRAM_PSD 升级）**：`verify/osc_os1_probe.py` 的随机点集 Gram PSD 是
**必要条件的数值抽查**（判别力有限、且不构成证明）。命题 D 说明反射 Gram 矩阵的 PSD 是
RP-QUAD 的**推论**，故 `RP_GRAM_PSD` 由 `numeric` 依据升级为 `proof`
（`proofs/rp_chain.md` 命题 D）。数值探针保留为回归检查。

---

## 4. 命题 E（GAUSSIAN_RP_FROM_COVARIANCE，Schur 归约，无条件步骤）

**命题 E**：设 `\mu_m` 为 `\mathcal S'(\mathbb R^4)` 上均值为零、协方差为 `C_m` 的 Gaussian
测度。对实值 `f_i\in\mathcal S_+`、`c_i\in\mathbb C`，令 `W_f=e^{i\phi(f)}`、
`(\Theta W_f)(\phi)=\overline{W_f(\theta\phi)}=e^{-i\phi(\theta f)}`。则
\[
 \sum_{i,j}\overline{c_i}c_j\int(\Theta W_{f_i})W_{f_j}\,d\mu_m\ge0 .
\]

**证明**：Gaussian 特征函数公式给出
\[
 \int(\Theta W_{f_i})W_{f_j}\,d\mu_m
 =e^{-\frac12\langle\theta f_i-f_j,\theta f_i-f_j\rangle_C}
 =e^{-\frac12\langle f_i,f_i\rangle_C}\,e^{-\frac12\langle f_j,f_j\rangle_C}\,
 \underbrace{e^{\langle\theta f_i,f_j\rangle_C}}_{=e^{R_{ij}}},
\]
其中用了 `\langle\theta f_i,\theta f_i\rangle_C=\langle f_i,f_i\rangle_C`、
`\langle f_j,\theta f_i\rangle_C=\overline{R_{ij}}` 与 `\langle\theta f_i,f_j\rangle_C=R_{ij}`。
于是
\[
 \sum_{i,j}\overline{c_i}c_j\int(\Theta W_{f_i})W_{f_j}d\mu_m
 =\sum_{i,j}\overline{d_i}c_i\,\bigl(e^{R_{ij}}\bigr)\,d_jc_j,
 \qquad d_i:=e^{-\frac12\langle f_i,f_i\rangle_C}>0 .
\]
由命题 C，`R` PSD；由引理 B，`\exp\circ R` PSD；由推论 A.2（`D=\operatorname{diag}(d_i)`），
`D(\exp\circ R)D` PSD，故上式 `\ge0`。\(\square\)

**含义**：`GAUSSIAN_RP_FROM_COVARIANCE` 中"条件性柱状指数层"的附注可移除——
该步骤现在是**无条件**的（输入仅：`R` PSD 与 `\exp\circ` 保 PSD）。
残余外部输入只有 `\mu_m` 的存在与其 Gaussian 特征函数公式（= `GFF_MEASURE_EXISTS`，
即 `A_GFF_minlos`，IMPORTED_UPSTREAM）。这与论文 B.4(i) 的归约（B.19）–（B.23）一致。

**注 E.1（与论文 (B.21)–(B.23) 的对应）**：论文把（B.21）写成
`\exp(-\tfrac12\langle f_i-\Theta f_j,K(f_i-\Theta f_j)\rangle)
=e^{-\frac12\langle f_i,Kf_i\rangle}e^{-\frac12\langle f_j,Kf_j\rangle}e^{R_{ij}}`，
（B.22）用协方差反射正性给出 `R_{ij}` PSD，（B.23）用 Schur 定理给出 `\exp(R_{ij})` PSD。
本文件命题 C/E 即（B.22）/（B.23）的 AImath 版本；引理 A 即 Schur 定理。

---

## 5. 状态建议（严格按 STATUS_ONTOLOGY）

| 节点 | 原状态 | 建议 | 依据 |
|---|---|---|---|
| `SCHUR_PRODUCT_PSD` | LITERATURE_SUPPORTED | **PROVED** | 本文引理 A（自证，`proof`） |
| `RP_COVARIANCE` | PROVED_UNDER_ASSUMPTIONS | 维持 PUA | 本文命题 C 重述 + N3 约定核对（`proof`） |
| `RP_QUADRATIC_FORM` | PROVED_UNDER_ASSUMPTIONS | 维持 PUA | 命题 D（`proof`） |
| `RP_GRAM_PSD` | NUMERICAL_EVIDENCE | **PROVED_UNDER_ASSUMPTIONS** | 命题 D：RP-QUAD 推论（`proof`） |
| `GAUSSIAN_RP_FROM_COVARIANCE` | PROVED_UNDER_ASSUMPTIONS | 维持 PUA（去"条件性"附注） | 命题 E（`proof`） |
| `SCHWINGER_PARAMETRIZATION_ABSOLUTE_INTEGRABILITY` | LITERATURE_SUPPORTED | **PROVED_UNDER_ASSUMPTIONS** | `proofs/schwinger_bessel.md`（`proof`） |

**残余假设（诚实声明）**：以上全部步骤无条件，**除**命题 C/E 的 Gaussian 测度层需要
`GFF_MEASURE_EXISTS`（= `A_GFF_minlos`，IMPORTED_UPSTREAM / 文献）。故相关节点维持在
`PROVED_UNDER_ASSUMPTIONS`（显式假设 = `GFF_MEASURE_EXISTS`），不升至 `PROVED`。
`OS1_FREE_SCALAR` 的 `A_OS1_measure` 中"3 个 evidence-bearing axioms"的**数学**部分
（`bessel_k0_integral` / `bessel_k0_integral_complex` / `yukawa_fourier_1d_pos`）
已由 `proofs/schwinger_bessel.md` 纸面闭合；**Lean 侧仍为 AXIOM**，直到换元基础设施
（`integral_comp_mul_deriv_Ioi` 方向问题）在服务器侧解决——该缺口是**基础设施**，非数学。

## 6. 依赖与红线

依赖：`S1_DISTRIBUTION_IDENTIFICATION`（PROVED）、`proofs/os1_reflection_positivity.md`
（命题 1–3，RP-COV/RP-QUAD）、`proofs/schwinger_bessel.md`、经典线性代数
（谱定理、Hadamard 幂）与 `GFF_MEASURE_EXISTS`。
未使用 S3 Green 恒等式；未使用 S6 `green_identity` 反向回灌；数值探针不作证明。
