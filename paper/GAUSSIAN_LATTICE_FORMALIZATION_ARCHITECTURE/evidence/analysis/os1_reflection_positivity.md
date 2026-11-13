# Proof — OS1_FREE_SCALAR：RP-COV 与 RP-QUAD

> 对应节点：`OS1_FREE_SCALAR`。
>
> 本文只证明自由 massive 标量场协方差核的反射正性及其对任意正时间 Schwartz 测试函数的二次型正性。证明不使用 S3 Green 恒等式、OS 重构、谱条件、cluster 性质或散射结论。
>
> **结论范围。** 本文闭合的是连续无限体积自由场的协方差层命题 `RP-COV` 与 `RP-QUAD`。将该命题推广为 Minlos Gaussian 测度上任意正时间柱状函数的 OS 正性，以及随后构造 OS Hilbert 空间，属于独立的 `RP-GAUSS`/`OS-HILBERT` 层，不在本文中偷用。

## 0. 约定

固定质量
\[
 m>0.
\]
欧氏坐标写为
\[
 x=(t,\mathbf x)\in\mathbb R\times\mathbb R^3,
\]
时间反射为
\[
 \theta(t,\mathbf x)=(-t,\mathbf x),
\qquad
 H_+=\{(t,\mathbf x):t>0\}.
\]

自由标量场的协方差为 tempered distribution
\[
 C_m(x-y)=\int_{\mathbb R^4}
 \frac{d p_0\,d^3p}{(2\pi)^4}
 \frac{e^{i p_0(t-s)+i\mathbf p\cdot(\mathbf x-\mathbf y)}}
 {p_0^2+|\mathbf p|^2+m^2}.
\]
在 \(x\ne y\) 时，它由正的径向函数表示为
\[
 C_m(x)=\frac{m}{4\pi^2|x|}K_1(m|x|)
 =\frac1{16\pi^2}\int_0^\infty u^{-2}
 e^{-m^2u-|x|^2/(4u)}\,du.
\]

记
\[
 \mathcal S_+
 =\{f\in\mathcal S(\mathbb R^4):
 \operatorname{supp}f\subset\{t\ge0\}\}.
\]
这是 OS 反射正性中通常使用的正时间 Schwartz 空间；允许支集接触反射超平面 \(t=0\)。对任意 \(\delta>0\)，定义时间平移 \(f_\delta(t,\mathbf x)=f(t-\delta,\mathbf x)\)。则 \(f_\delta\) 的支集距 \(t=0\) 至少为 \(\delta\)，且 \(f_\delta\to f\) 于 Schwartz 拓扑。先对 \(f_\delta\) 证明，再令 \(\delta\downarrow0\)。对空间变量采用 Fourier 约定
\[
 \widehat f(t,\mathbf p)
 =\int_{\mathbb R^3}e^{-i\mathbf p\cdot\mathbf x}
 f(t,\mathbf x)\,d^3x.
\]

---

## 1. RP-COV：反射协方差的正因子分解

### 命题 1（空间 Fourier 表示）

对 \(t,s>0\)，在 \((t,s,\mathbf x-\mathbf y)\) 的意义下，有
\[
 C_m\bigl(\theta(t,\mathbf x)-(s,\mathbf y)\bigr)
 =C_m\bigl((-t-s,\mathbf x-\mathbf y)\bigr)
\]
以及
\[
 C_m\bigl(\theta(t,\mathbf x)-(s,\mathbf y)\bigr)
 =\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 e^{i\mathbf p\cdot(\mathbf x-\mathbf y)}
 \frac{e^{-\omega_{\mathbf p}(t+s)}}{2\omega_{\mathbf p}},
 \tag{1}
\]
其中
\[
 \omega_{\mathbf p}=\sqrt{|\mathbf p|^2+m^2}\ge m>0.
\]

#### 证明

令
\[
 \tau=t+s>0,
 \qquad
 \omega=\omega_{\mathbf p}.
\]
固定 \(\mathbf p\)，考虑一维 Fourier 积分
\[
 I_\omega(\tau)
 =\int_{\mathbb R}\frac{dp_0}{2\pi}
 \frac{e^{-ip_0\tau}}{p_0^2+\omega^2}.
\]
先使用 Schwinger 参数恒等式
\[
 \frac1{p_0^2+\omega^2}
 =\int_0^\infty e^{-u(p_0^2+\omega^2)}\,du.
\]
对 \(\tau>0\)，引入截断 \(u\in[\delta,R]\)、\(p_0\in[-N,N]\)，所有积分均为有限积分，可以直接交换积分次序。令 \(N\to\infty\)，再令 \(\delta\downarrow0\)、\(R\to\infty\)，由高斯 Fourier 积分及其绝对可积的最终表达式得到
\[
\begin{aligned}
 I_\omega(\tau)
 &=\int_0^\infty e^{-u\omega^2}
 \left(\int_{\mathbb R}\frac{dp_0}{2\pi}
 e^{-up_0^2-ip_0\tau}\right)du\\
 &=\int_0^\infty e^{-u\omega^2}
 \frac1{\sqrt{4\pi u}}
 e^{-\tau^2/(4u)}\,du.
\end{aligned}
\]
再对 \(u\) 作代换 \(v=\omega\sqrt u\)，或直接使用标准的一维 Yukawa Fourier 恒等式，得到
\[
 I_\omega(\tau)=\frac{e^{-\omega\tau}}{2\omega}.
 \tag{2}
\]
为说明极限合法性，注意 \(\tau>0\) 固定时，积分表示中的被积函数在 \(u\downarrow0\) 时受 \(e^{-\tau^2/(4u)}\) 超指数压制，在 \(u\to\infty\) 时受 \(e^{-u\omega^2}\) 指数压制；且 \(\omega\ge m>0\)。因此 (2) 对每个 \(\mathbf p\) 有意义。

将 (2) 代入四维 Fourier 表示，并先对正则化的 \(\mathbf p\)-截断积分计算，得到
\[
\begin{aligned}
 C_m((-\tau,\mathbf z))
 &=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 e^{i\mathbf p\cdot\mathbf z}
 \int_{\mathbb R}\frac{dp_0}{2\pi}
 \frac{e^{-ip_0\tau}}{p_0^2+|\mathbf p|^2+m^2}\\
 &=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 e^{i\mathbf p\cdot\mathbf z}
 \frac{e^{-\omega_{\mathbf p}\tau}}
 {2\omega_{\mathbf p}}.
\end{aligned}
\]
由于 \(m>0\)，且 \(e^{-\omega_{\mathbf p}\tau}\) 对大 \(|\mathbf p|\) 提供指数衰减，右端绝对收敛。故可去除 \(\mathbf p\)-截断，并令 \(\tau=t+s\)、\(\mathbf z=\mathbf x-\mathbf y\)，得到 (1)。\(\square\)

### 命题 2（RP-COV 的核分解）

对 \(t,s>0\)，令
\[
 a_{\mathbf p}(t)=e^{-\omega_{\mathbf p}t}.
\]
则反射协方差核具有分解
\[
 C_m\bigl(\theta(t,\mathbf x)-(s,\mathbf y)\bigr)
 =\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac{a_{\mathbf p}(t)\,a_{\mathbf p}(s)}{2\omega_{\mathbf p}}
 e^{i\mathbf p\cdot(\mathbf x-\mathbf y)}.
 \tag{3}
\]
换言之，空间 Fourier 变换后的每个动量模 \(\mathbf p\) 都是一个正系数乘以时间函数
\[
 a_{\mathbf p}(t)a_{\mathbf p}(s)
\]
的 rank-one 正核。

#### 证明

这是命题 1 中
\[
 e^{-\omega_{\mathbf p}(t+s)}
 =e^{-\omega_{\mathbf p}t}e^{-\omega_{\mathbf p}s}
\]
的直接代入。由于
\[
 \frac1{2\omega_{\mathbf p}}>0,
\]
每个 \(\mathbf p\)-模的时间核为正系数乘以 rank-one 核。\(\square\)

---

## 2. RP-QUAD：任意正时间测试函数的二次型正性

### 命题 3（RP-QUAD）

对任意 \(f\in\mathcal S_+\)，定义
\[
 Q_m(f)
 =\int_{H_+}dx\int_{H_+}dy\,
 \overline{f(x)}
 C_m(\theta x-y)f(y).
 \tag{4}
\]
则该积分绝对收敛，并且
\[
 Q_m(f)\ge0.
 \tag{5}
\]
更精确地，令
\[
 F_f(\mathbf p)
 =\int_0^\infty e^{-\omega_{\mathbf p}t}
 \widehat f(t,\mathbf p)\,dt.
 \tag{6}
\]
则
\[
 Q_m(f)
 =\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac{|F_f(\mathbf p)|^2}{2\omega_{\mathbf p}}.
 \tag{7}
\]

#### 证明

### 第一步：正时间 Fourier-Laplace 变换良定义

先取 \(f\in\mathcal S_+\) 且 \(\operatorname{supp}f\subset\{t\ge\varepsilon\}\) 对某个 \(\varepsilon>0\)。对每个 \(t\ge\varepsilon\)，\(\widehat f(t,\mathbf p)\) 关于 \(\mathbf p\) 为 Schwartz 函数；关于 \(t\) 的所有导数也具有 Schwartz 界。特别地，对任意 \(N,M\ge0\)，存在常数 \(A_{N,M}<\infty\)，使
\[
 |\widehat f(t,\mathbf p)|
 \le A_{N,M}(1+t)^{-N}(1+|\mathbf p|)^{-M}.
 \tag{8}
\]
因此 (6) 绝对收敛。事实上，因 \(\omega_{\mathbf p}\ge m\)，
\[
 |F_f(\mathbf p)|
 \le A_{N,M}(1+|\mathbf p|)^{-M}
 \int_\varepsilon^\infty e^{-mt}(1+t)^{-N}dt
 \le B_{N,M}(1+|\mathbf p|)^{-M}.
 \tag{9}
\]
所以 \(F_f\) 是快速衰减的，特别是
\[
 \frac{|F_f(\mathbf p)|^2}{2\omega_{\mathbf p}}
 \in L^1(\mathbb R^3).
 \tag{10}
\]

### 第二步：先对截断测试函数计算

取 \(R>0\)，令
\[
 f_R(t,\mathbf x)=f(t,\mathbf x)\mathbf 1_{|\mathbf x|\le R}.
\]
也可用光滑空间截断代替硬截断；以下计算对光滑截断成立，并由 \(R\to\infty\) 的 Schwartz 收敛给出原命题。再取时间截断 \(T>\varepsilon\)，令
\[
 f_{R,T}(t,\mathbf x)
 =f(t,\mathbf x)\mathbf 1_{\varepsilon\le t\le T}
 \mathbf 1_{|\mathbf x|\le R}.
\]
对固定 \(R,T\)，所有变量都在有界区域内，且反射后的时间差满足
\[
 t+s\ge2\varepsilon>0.
\]
因此 \(C_m(\theta x-y)\) 是该积分区域上的连续有界函数，Fubini 定理适用。

用 (1) 代入 (4)，并暂时保留 \(R,T\) 截断，得到
\[
\begin{aligned}
 Q_m(f_{R,T})
 &=\int_{\varepsilon}^{T}dt\int_{\varepsilon}^{T}ds
 \int_{\mathbb R^3}d^3x\int_{\mathbb R^3}d^3y
 \overline{f_{R,T}(t,\mathbf x)}
 C_m(\theta(t,\mathbf x)-(s,\mathbf y))
 f_{R,T}(s,\mathbf y)\\
 &=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac1{2\omega_{\mathbf p}}
 \left|
 \int_{\varepsilon}^{T}e^{-\omega_{\mathbf p}t}
 \widehat {f_{R,T}}(t,\mathbf p)dt
 \right|^2.
 \tag{11}
\end{aligned}
\]
这里使用了
\[
\int d^3x\,\overline{f(t,\mathbf x)}e^{i\mathbf p\cdot\mathbf x}
 =\overline{\widehat f(t,\mathbf p)},
\]
以及
\[
\int d^3y\,e^{-i\mathbf p\cdot\mathbf y}f(s,\mathbf y)
 =\widehat f(s,\mathbf p).
\]

右端是非负实数，因为 \(2\omega_{\mathbf p}>0\)。这已经证明所有截断测试函数满足
\[
 Q_m(f_{R,T})\ge0.
 \tag{12}
\]

### 第三步：去掉截断

先令 \(T\to\infty\)、空间截断半径 \(R\to\infty\)。为避免硬截断在 Schwartz 拓扑下的无关技术问题，实际取光滑截断函数 \(\chi_R(\mathbf x)\)、\(\eta_T(t)\)，其中 \(\chi_R=1\) 于 \(|\mathbf x|\le R\)、\(\eta_T=1\) 于 \(t\le T\)，并令 \(f_{R,T}=\eta_T\chi_R f\)。则 \(f_{R,T}\to f\) 于 \(\mathcal S(\mathbb R^4)\)。相应的空间 Fourier 变换满足以下极限：
\[
 \widehat {f_{R,T}}(t,\mathbf p)
 \to\widehat f(t,\mathbf p)
\]
并且由 (8) 有统一的可积控制。于是对每个 \(\mathbf p\)，
\[
 \int_\varepsilon^T e^{-\omega_{\mathbf p}t}
 \widehat {f_{R,T}}(t,\mathbf p)dt
 \longrightarrow
 F_f(\mathbf p).
 \tag{13}
\]
同时，(9) 给出统一的 \(\mathbf p\)-衰减界：可取足够大的 \(M\)，使
\[
 \frac1{2\omega_{\mathbf p}}
 \left|
 \int_\varepsilon^T e^{-\omega_{\mathbf p}t}
 \widehat {f_{R,T}}(t,\mathbf p)dt
 \right|^2
 \le C(1+|\mathbf p|)^{-2M-1},
 \tag{14}
\]
右端属于 \(L^1(\mathbb R^3)\)。由支配收敛定理，(11) 的右端收敛到
\[
 \int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac{|F_f(\mathbf p)|^2}{2\omega_{\mathbf p}}.
 \tag{15}
\]
该极限有限且非负。

另一方面，原始位置空间二次型 (4) 也定义良好。因为 \(t+s\ge2\varepsilon\)，反射核远离四维对角线；在该区域上 \(C_m\) 光滑，并且由 Schwinger 表示或 Bessel 渐近可得其随空间差变量指数衰减。结合 \(f\) 的 Schwartz 衰减，位置空间积分绝对收敛。故截断积分的极限正是 (4)。由此得到恒等式 (7)，并推出 (5)。

上面暂时假定支集距 \(t=0\) 有正距离。对一般 \(f\in\mathcal S_+\)，取 \(f_\delta(t,\mathbf x)=f(t-\delta,\mathbf x)\)。每个 \(f_\delta\) 都满足前述假设，故 \(Q_m(f_\delta)\ge0\)。空间 Fourier 表示 (7) 以及 Schwartz 拓扑下的平移连续性给出 \(F_{f_\delta}\to F_f\) 在加权空间
\[
L^2\!\left(\mathbb R^3,\frac{d^3p}{(2\pi)^3 2\omega_{\mathbf p}}\right)
\]
中成立。因此 \(Q_m(f_\delta)\to Q_m(f)\)，从而 \(Q_m(f)\ge0\)。\(\square\) 

---

## 3. 双线性形式与有限线性组合版本

由极化恒等式，定义
\[
 B_m(f,g)
 =\int_{H_+}dx\int_{H_+}dy\,
 \overline{f(x)}C_m(\theta x-y)g(y).
\]
同样的计算给出
\[
 B_m(f,g)
 =\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac{\overline{F_f(\mathbf p)}F_g(\mathbf p)}
 {2\omega_{\mathbf p}}.
 \tag{16}
\]
因此对任意 \(f_1,\dots,f_n\in\mathcal S_+\) 与 \(c_1,\dots,c_n\in\mathbb C\)，有
\[
\begin{aligned}
 \sum_{i,j=1}^n\overline{c_i}
 B_m(f_i,f_j)c_j
 &=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
 \frac1{2\omega_{\mathbf p}}
 \left|\sum_{j=1}^n c_jF_{f_j}(\mathbf p)\right|^2
 \ge0.
\end{aligned}
\tag{17}
\]
所以矩阵
\[
 \bigl(B_m(f_i,f_j)\bigr)_{i,j=1}^n
\]
对任意有限族 \(f_i\subset\mathcal S_+\) 都是 Hermitian 正半定矩阵。这是协方差层的完整反射正性，而非有限点采样条件。

---

## 4. 与现有数值探针的关系

本文的 (7) 是对任意正时间 Schwartz 测试函数的解析恒等式，因此严格强于：

- `verify/osc_os1_probe.py` 中有限随机点集的 Gram PSD 检查；
- 空间平均核
  \[
  K_1(t,s)=\frac{e^{-m(t+s)}}{2m}
  \]
  的秩一数值检查。

空间平均核正是 (3) 在空间动量 \(\mathbf p=0\) 模上的退化投影；它只能看到一个动量模。随机点集探针则只测试有限多个点值。二者都不能替代 (7)。

本文也没有把二次型层结果自动升级为：

\[
 \int \overline{\Theta F}F\,d\mu_m\ge0
\]
对任意正时间场函数 \(F\) 的测度层命题。下面补上 Gaussian 柱状指数函数层的证明；它仍以 Minlos Gaussian 测度存在和其特征函数公式为输入。

---

## 5. RP-GAUSS：从协方差反射正性到 Gaussian 柱状函数

### 命题 4（Gaussian 指数向量的反射正性）

设 \(\mu_m\) 是 \(\mathcal S'(\mathbb R^4)\) 上均值为零、协方差为 \(C_m\) 的 Gaussian 测度。对实值 \(f\in\mathcal S_+\)，定义柱状指数函数
\[
 W_f(\phi)=e^{i\phi(f)}.
\]
定义时间反射作用
\[
 (\Theta W_f)(\phi)=\overline{W_f(\theta\phi)}
 =e^{-i\phi(\theta f)},
\]
其中 \((\theta f)(t,\mathbf x)=f(-t,\mathbf x)\)。则对任意有限族 \(f_1,\ldots,f_n\in\mathcal S_+\) 和系数 \(c_1,\ldots,c_n\in\mathbb C\)，有
\[
 \sum_{i,j}\overline{c_i}c_j
 \int (\Theta W_{f_i})W_{f_j}\,d\mu_m\ge0.
\]
按上述定义，矩阵元为：
\[
\[
 \int (\Theta W_{f_i})(\phi)W_{f_j}(\phi)\,d\mu_m(\phi)
 =d_i d_j\,e^{B_m(f_i,f_j)},
 \tag{18}
\]
其中
\[
 d_i=e^{-\frac12 C_m(f_i,f_i)}>0,
 \qquad
 B_m(f_i,f_j)=C_m(\theta f_i,f_j)
\]
且矩阵 \((e^{B_m(f_i,f_j)})_{ij}\) 正半定。

#### 证明

先说明记号：OS 反射形式是
\[
 (F,G)_{OS}=\int (\Theta F)G\,d\mu_m,
\]
而不是再次对 \(\Theta F\) 取复共轭。于是对指数函数
\[
 (W_f,W_g)_{OS}
 =\mathbb E\left[e^{-i\phi(\theta f)}e^{i\phi(g)}\right].
\]
Gaussian 特征函数公式给出
\[
\begin{aligned}
 (W_f,W_g)_{OS}
 &=\exp\left[-\frac12 C_m(\theta f-g,\theta f-g)\right]\\
 &=\exp\left[-\frac12 C_m(\theta f,\theta f)
 -\frac12 C_m(g,g)+C_m(\theta f,g)\right].
\end{aligned}
\]
协方差的反射不变性给出
\[
 C_m(\theta f,\theta f)=C_m(f,f),
\]
故得到 (18)。该等式先对实值测试函数成立；复测试函数由复线性延拓处理。

现在证明 \(E_{ij}=e^{B_m(f_i,f_j)}\) 正半定。由 RP-QUAD 及极化恒等式，矩阵 \(B=(B_{ij})\) 是 Hermitian 正半定。于是存在（有限维）Gram 向量 \(v_i\) 使
\[
 B_{ij}=\langle v_i,v_j\rangle.
\]
对每个 \(k\ge0\)，矩阵 \((B_{ij}^k)_{ij}\) 是第 \(k\) 次对称张量幂中的 Gram 矩阵：
\[
 B_{ij}^k
 =\langle v_i^{\otimes k},v_j^{\otimes k}\rangle.
\]
因此它正半定。又因为有限维矩阵的指数级数逐项收敛，
\[
 E_{ij}=e^{B_{ij}}
 =\sum_{k=0}^\infty\frac{B_{ij}^k}{k!},
\]
是正半定矩阵的逐项非负线性组合。故对任意 \(c_i\)，
\[
\sum_{i,j}\overline{c_i}c_j E_{ij}\ge0.
\]
乘以正对角矩阵 \(\operatorname{diag}(d_i)\) 的左右两侧仍保持正半定，于是指数柱状函数的 OS 反射形式非负。\(\square\)

### 记号修正

命题 4 中的 OS 形式应统一写成
\[
 \langle F,G\rangle_{OS}
 =\int (\Theta F)G\,d\mu_m,
\]
其中 \(\Theta\) 已包含复共轭。于是没有额外的
\(\overline{\Theta F}\)；若采用通常的 Hilbert 内积记号，则可把 \(\Theta\) 的共轭约定重新吸收到定义中，但全篇必须保持一致。

### 命题 5（柱状多项式层）

令 \(\mathcal A_+^{\exp}\) 为有限线性组合
\[
 F=\sum_{i=1}^n c_iW_{f_i},
 \qquad f_i\in\mathcal S_+\text{ 实值}.
\]
则
\[
 \int (\Theta F)F\,d\mu_m\ge0.
 \tag{19}
\]
此外，正时间柱状多项式可以由这类指数向量在每个固定有限维 Gaussian 子空间的 \(L^2(\mu_m)\) 中逼近。因此 (19) 延拓到所有有限维柱状 \(L^2\) 函数；再由完备性延拓到其 \(L^2\)-闭包。

#### 证明

第一句由命题 4 对有限指数向量族直接得到。对第二句，固定有限族 \(f_1,\ldots,f_r\)，令
\[
 X=(\phi(f_1),\ldots,\phi(f_r)).
\]
其分布是有限维 centered Gaussian。多项式函数属于 \(L^2\)；用 Gaussian 权重下的 Hermite 多项式基，或等价地用 Fourier 变换后的指数函数 \(e^{i\xi\cdot X}\) 的有限线性组合逼近，得到柱状多项式的 \(L^2\) 逼近。反射形式满足 Cauchy–Schwarz 型连续估计
\[
 |(F,G)_{OS}|^2\le (F,F)_{OS}(G,G)_{OS}
\]
先在指数向量稠密子空间上成立，再由半内积的商空间延拓。因此极限保持非负。\(\square\)

---

## 6′. OS-HILBERT：H₁ 半范数商空间与完备化

### 命题 6（H₁ 构造）

令 \(\mathcal D_+\) 为 \(\mathcal S_+\) 的有限复线性组合空间（即 \(\text{span}_{\mathbb C}\{f : f\in\mathcal S_+\}\)，本身仍 \(\subset\mathcal S(\mathbb R^4)\) 且支集包含于 \(\{t\ge0\}\)）。由命题 3 与极化恒等式，
\[
 (f,g)_{1}
 :=\int_{\mathbb R^3}\frac{d^3p}{(2\pi)^3}
   \frac{F_f(\mathbf p)\,\overline{F_g(\mathbf p)}}{2\omega_{\mathbf p}}
\]
是 \(\mathcal D_+\) 上的半内积（hermitian、半正定；线性/共轭线性由 (16) 与 \(F_{cf+g}=cF_f+F_g\) 的线性性给出）。设
\[
 \mathcal N_+=\{f\in\mathcal D_+ : (f,f)_{1}=0\}
 =\{f\in\mathcal D_+ : F_f\equiv0\}.
\]
（第二等号：权重 \((2\pi)^{-3}(2\omega_{\mathbf p})^{-1}>0\) 处处非零，故 \((f,f)_1=0\iff F_f=0\)。）

**H₁ 定义**：\(H_1:=\mathcal D_+/\mathcal N_+\)，赋范
\[
 \|f+\mathcal N_+\|_1^2:=(f,f)_1 .
\]
则 \((H_1,\|\cdot\|_1)\) 是**预 Hilbert 空间**（半内积商 → 内积）。

#### 证明

hermitian 性与非负性即命题 3 / (16) 的内容。商空间上内积良定义：若 \(f-f'\in\mathcal N_+\)、\(g-g'\in\mathcal N_+\)，则 \((f-f',g)=0\)（半内积零元正交性：由 \((a+a',b)^2\le(a+a',a+a')(a',a')\) 在 \((a',a')=0\) 时给出 \((a,a')=0\)，即零半范数元与一切正交），故 \((f,g)_1=(f',g')_1\)。范数公理平凡。Cauchy–Schwarz 在半内积上成立，商后成为内积空间不等式。\(\square\)

### 命题 7（H₁ 的显式等距嵌入与稠密核）

设 \(\mathcal F_+:=\{F_f : f\in\mathcal D_+\}\subset L^2\!\left(\mathbb R^3,\frac{d^3p}{(2\pi)^3 2\omega_{\mathbf p}}\right)\) 为 \(F_f\) 的取值集合。则映射
\[
 J:\mathcal D_+\to L^2\!\left(\mathbb R^3,\frac{d^3p}{(2\pi)^3 2\omega_{\mathbf p}}\right),\qquad J(f)=F_f
\]
是线性、连续、且核恰为 \(\mathcal N_+\) 的算子；它诱导等距嵌入
\[
 \tilde J:H_1\hookrightarrow L^2\!\left(\mathbb R^3,\frac{d^3p}{(2\pi)^3 2\omega_{\mathbf p}}\right),
 \qquad \tilde J(f+\mathcal N_+)=F_f .
\]
\(H_1\) 的**完备化** \(\overline H_1\) 与 \(\overline{\mathcal F_+}\)（\(\mathcal F_+\) 在上述加权 \(L^2\) 中的闭包）等距同构：
\[
 \overline H_1\cong \overline{\{F_f:f\in\mathcal D_+\}^{\,L^2(d^3p/(2\pi)^3\,2\omega_{\mathbf p})}}
 \;\;\text{（等距）}.
\]

#### 证明

\(J\) 等距性：\(\|J(f)\|_{L^2(w)}^2=(f,f)_1=\|f+\mathcal N_+\|_1^2\)，即 (16) 取 \(g=f\)。核：\(\ker J=\{f:F_f\equiv0\}=\mathcal N_+\)（命题 6 已证）。于是 \(J\) 在商上良定义且等距，像为 \(\mathcal F_+\)；商空间的完备化与像的闭包等距（预 Hilbert 空间的 Cauchy 序列在等距像下仍 Cauchy，反之亦然）。\(\square\)

**推论（OS 重构输入）**：\(\overline H_1\) 是 Hilbert 空间；\(J\) 的延拓 \(\overline J:\overline H_1\to\overline{\mathcal F_+}\) 是等距同构；反射算子 \(\Theta\)（\(f\mapsto f\circ\theta\)，\(\theta(t,\mathbf x)=(-t,\mathbf x)\)）在 \(\mathcal D_+\) 上满足 \((\Theta f,g)_{OS}=(\tilde J f,\tilde J g)_{L^2(w)}\cdot(\text{Gaussian 层因子})\)——即协方差层反射形式恰为加权 \(L^2\) 内积（(16)），Gaussian 柱状指数层再由命题 4 的 \(e^{B}\)-PSD 机制叠上。此即 Osterwalder–Schrader 重构所需的正半定反射核。\(\square\)

**备注（\(\mathcal N_+\) 的显式刻画）**：\(F_f\equiv0\) 等价于 \(\widehat f(t,\mathbf p)\) 的 Laplace 变换在 \(\Re z=0\) 上恒为零；由 Laplace 变换唯一性（半空间分布），若 \(f\in\mathcal S_+\) 且 \(F_f\equiv0\)，则 \(f=0\) 于 \(\{t>0\}\)。因此对 \(\mathcal S_+\) 单函数 \(\mathcal N_+=\{0\}\)；\(\mathcal N_+\) 非平凡仅出现在有限线性组合层面（不同 \(f_i\) 的 \(F_{f_i}\) 线性相关时）。该刻画不影响 H₁ 的构造，仅说明半范数在"单函数"层面已是范数。

---

## 6″. RP-EXPLICIT：二点函数显式核验

### 命题 8（二点反射核的显式形式与秩一性）

对 \(t,s>0\)、\(\mathbf x,\mathbf y\in\mathbb R^3\)，
\[
 C_m\bigl(\theta(t,\mathbf x)-(s,\mathbf y)\bigr)
 =\frac{m}{4\pi^2\sqrt{(t+s)^2+|\mathbf x-\mathbf y|^2}}
   K_1\!\left(m\sqrt{(t+s)^2+|\mathbf x-\mathbf y|^2}\right).
\]
空间平均（对 \(\mathbf x-\mathbf y\) 积分后除以体积，即取 \(\mathbf p=0\) 模）给出
\[
 K_1^{\mathrm{avg}}(t,s)
 :=\lim_{\Lambda\to\infty}\frac1{|\Lambda|^3}
   \int_{\Lambda^3}d^3z\;
   C_m\bigl(\theta(t,\mathbf 0)-(s,\mathbf z)\bigr)
 =\frac{e^{-m(t+s)}}{2m}.
\]
该核为**精确秩一**：\(K_1^{\mathrm{avg}}(t,s)=a(t)a(s)\)，\(a(t)=e^{-mt}\)。故任意有限正时间采样 \((t_1,\dots,t_n)\) 的 Gram 矩阵
\[
 \bigl(K_1^{\mathrm{avg}}(t_i,t_j)\bigr)_{i,j}
 =\begin{pmatrix}a(t_1)\\ \vdots\\ a(t_n)\end{pmatrix}
   \begin{pmatrix}a(t_1)&\cdots&a(t_n)\end{pmatrix}
\]
是秩一 PSD 矩阵（min-eig \(=0\)，n>1；n=1 时 \(=(a(t_1))^2>0\)）。

#### 证明

第一式：\(\theta(t,\mathbf x)-(s,\mathbf y)=(-t-s,\mathbf x-\mathbf y)\)，其四维模长为 \(\sqrt{(t+s)^2+|\mathbf x-\mathbf y|^2}\)；代入 \(C_m\) 的 Bessel 闭式（§0）即得。第二式：对 \(\mathbf z\) 的积分即取空间 Fourier 表示 (1) 的 \(\mathbf p=0\) 模（其余模 \(\int e^{i\mathbf p\cdot\mathbf z}d^3z=0\)），得
\[
 \frac1{2\omega_{\mathbf 0}}e^{-\omega_{\mathbf 0}(t+s)}
 =\frac{e^{-m(t+s)}}{2m},
\]
体积因子在平均意义下归一。秩一性：\(e^{-m(t+s)}=e^{-mt}e^{-ms}\)。\(\square\)

**备注（探针判别力）**：此秩一核的 PSD 是**自动**的（秩一非负向量外积恒 PSD），故 `verify/osc_os1_probe.py::check_reflection_positivity_spatial` 对该核的 min-eig 检查判别力为零（仅验证系数符号与数值舍入）；真正的判别力来自**非空间平均**的多点 Gram（随机点集探针），它同时看到多个 \(\mathbf p\) 模的叠加。命题 3 的 (7) 是对**所有**模的逐点 PSD，严格强于二者。

---

## 7. 依赖与状态建议

本证明使用：

1. \(m>0\)；
2. 自由场协方差的 Fourier 表示；
3. 一维 Yukawa Fourier 恒等式
   \[
   \int_{\mathbb R}\frac{dp_0}{2\pi}
   \frac{e^{-ip_0\tau}}{p_0^2+\omega^2}
   =\frac{e^{-\omega|\tau|}}{2\omega};
   \]
4. Schwartz Fourier 变换与 Fubini/支配收敛定理；
5. Minlos Gaussian 测度存在及有限维 Gaussian 特征函数公式；
6. 指数向量在有限维 Gaussian \(L^2\) 中的稠密性；
7. （命题 6/7）半内积商空间的标准 Hilbert 空间构造与等距嵌入定理；
8. （命题 8）\(C_m\) 的 Bessel 闭式 \(mK_1(mr)/(4\pi^2 r)\)（§0）与空间 Fourier 模正交性。

不使用：

- S1/S3 的分布 Green 恒等式；
- OS2、OS3、OS4；
- OS 重构定理；
- 谱条件、真空唯一性或散射理论；
- 有限体积到连续体积极限。

因此，本文新增的 `RP-GAUSS` 与 `OS-HILBERT`（命题 6/7）仍以 `GFF_MEASURE_EXISTS` 和 Gaussian 测度的标准特征函数/稠密性结果为外部输入。它不再把有限点 Gram 数值探针当作证明。OS Hilbert 空间商空间与完备化已由命题 6/7 闭合（等距嵌入加权 \(L^2\)）。

建议状态保持
\[
\texttt{PROVED\_UNDER\_ASSUMPTIONS}
\]
（假设：`A_OS1_measure` = `GFF_MEASURE_EXISTS`，即该 Fourier 协方差是所选 Minlos Gaussian 测度的协方差）。本文 RP-COV/RP-QUAD/RP-GAUSS/OS-HILBERT/RP-EXPLICIT 各层在纸面闭合；Lean 形式化覆盖有限因子核 + 正积分接口 + 分析层引理（`formal/lean/s6/OS1.lean`，target `S6Isserlis.OS1`）。`A_OS1_limit`（有限体积→连续极限）不再是本文路线的假设（连续证明不依赖格点极限）。

有限体积到连续极限不再是本文 RP-COV/RP-QUAD 的必要假设；若另行采用格点路线，应作为独立证明，不得与本文路线混写。

---

## 8. 依赖与状态建议（原 RP-COV/RP-QUAD 记录）

本证明使用：

1. \(m>0\)；
2. 自由场协方差的 Fourier 表示；
3. 一维 Yukawa Fourier 恒等式；
4. Schwartz Fourier 变换与 Fubini/支配收敛定理。

不使用 S1/S3、OS2/OS3/OS4、OS 重构、谱条件、真空唯一性、散射理论或有限体积极限。

本文可作为 `OS1_FREE_SCALAR` 的 `RP-COV`、`RP-QUAD` 与条件性 `RP-GAUSS` 证明工件。若项目状态仍要求区分协方差层和 Gaussian 测度层，保留 `PROVED_UNDER_ASSUMPTIONS`。

有限体积到连续体积极限不再是本文 RP-COV/RP-QUAD 的必要假设；若另行采用格点路线，应作为独立证明，不得与本文路线混写。

---

## 9. 依赖与状态建议（历史记录）

- `A_OS1_measure`：该 Fourier 协方差确实是所选 Minlos Gaussian 测度的协方差，并允许从协方差层进入柱状函数层；
- `A_OS1_Gaussian`：Gaussian 测度的柱状函数反射正性由协方差反射正性推出。 

有限体积到连续极限不再是本文 RP-COV/RP-QUAD 的必要假设；若另行采用格点路线，应作为独立证明，不得与本文路线混写。

---

## 10. 审计备注

项目的自动验证检查全部通过；本文件没有新增可执行验证脚本。数值探针仍只作为必要条件证据，不参与上述解析证明。 

本证明使用：

1. \(m>0\)；
2. 自由场协方差的 Fourier 表示；
3. 一维 Yukawa Fourier 恒等式
   \[
   \int_{\mathbb R}\frac{dp_0}{2\pi}
   \frac{e^{-ip_0\tau}}{p_0^2+\omega^2}
   =\frac{e^{-\omega|\tau|}}{2\omega};
   \]
4. Schwartz Fourier 变换与 Fubini/支配收敛定理。

不使用：

- S1/S3 的分布 Green 恒等式；
- OS2、OS3、OS4；
- OS 重构定理；
- 谱条件、真空唯一性或散射理论；
- 有限体积到连续体积极限。

因此，本文可作为 `OS1_FREE_SCALAR` 的 `RP-COV` 与 `RP-QUAD` 解析证明工件。若项目状态仍要求区分“协方差层”和“Gaussian 测度层”，建议保留
\[
\texttt{PROVED\_UNDER\_ASSUMPTIONS}
\]
并将剩余假设明确写为：

- `A_OS1_measure`：该 Fourier 协方差确实是所选 Minlos Gaussian 测度的协方差，并允许从协方差层进入柱状函数层；
- `A_OS1_Gaussian`：Gaussian 测度的柱状函数反射正性由协方差反射正性推出。

有限体积到连续极限不再是本文 RP-COV/RP-QUAD 的必要假设；若另行采用格点路线，应作为独立证明，不得与本文路线混写。
