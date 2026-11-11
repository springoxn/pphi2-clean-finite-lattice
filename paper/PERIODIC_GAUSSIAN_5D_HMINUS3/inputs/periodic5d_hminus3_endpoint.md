# 五维实际 raw atomic lift 在 H⁻³ 中的弱收敛

> status: ACTIVE · owner: PERIODIC5D_GAUSSIAN_RAW_LIFT_LIMIT · asof: 2026-11-11

本工件的可复现证据为 [完整 pinned Lean 源码与审计包](../deliverables/20261111_periodic5d_hminus3_endpoint.zip)，定理签名和公理审计入口为 [冻结契约](../formal/lean/challenges/PERIODIC5D_GAUSSIAN_RAW_LIFT_LIMIT.check.lean)。以下构建事实以包内审计日志为来源；节点当前状态请查询 `python -m runtime node PERIODIC5D_GAUSSIAN_RAW_LIFT_LIMIT`。

## 数学对象与结论

固定 `L > 0`、`mass > 0`，令 `N = n+1`、`a = L/N`。源测度是五维有限周期格点的 `finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 5 N a mass ha hmass)`。通过物理测试映射 `physicalTestEval 5 N a` 取 Fourier 系数；逐格点振幅是 `a^5 (cos θ + i sin θ)`。因此使用实际物理 raw atomic lift。

频率指标为 `k : Fin 5 → ℤ`。令

\[
 w_s(k)=(1+\|k\|_\infty)^{-2s},\qquad
 \|c\|_{-s}^{2}=\sum_k w_s(k)|c_k|^2.
\]

形式载体 `Periodic5DCompletion` 是复数 `lp(2)`；H⁻³ 系数通过 `c ↦ (sqrt(w_3(k)) c_k)_k` 实现于该完备空间。其 Borel σ 代数是范数拓扑的 Borel σ 代数。这是与通常欧氏频率权重等价的周期 Sobolev 拓扑；当前工程未单独打包与外部分布空间库的同构。

主定理 `periodic5DFixedVolume_weak_tendsto_gaussianTarget` 的冻结类型为：

```lean
∀ (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass),
  Filter.Tendsto
    (periodic5DFixedVolumeProbabilityMeasure L mass hL hmass)
    Filter.atTop
    (nhds (periodic5DGaussianTarget L mass hL hmass))
```

目标概率律由实际源律的弱极限构造。其任意有限实 Fourier 家族（每个分量任意选择 cosine 或 sine、允许重复及线性相关）都等于五维 massive resolvent 的规范中心高斯律，且这些边缘唯一确定目标。构造不要求调用者给出目标测度、紧性或识别接口。

## 显式 H⁻³ 高频尾界

`periodic5DRawAtomicLift_integral_hminusThree_tail_le` 给出，对任意有限频率集 `K`，

\[
 \mathbb E_{\mu_{N,a}}
 \sum_{k\notin K}w_3(k)|c_{N,a}(k)|^2
 \leq 2\,\mathrm{mass}^{-2}L^5
 \sum_{k\notin K}w_3(k),\qquad aN=L.
\]

证明先给出每个实际 Fourier 系数的二阶矩上界 `2 mass^-2 L^5`。对任意非负可和权重，逐项可积性和积分范数的可和性允许应用 `integral_tsum_of_summable_integral_norm`；没有把可能不可积的无穷尾和按零处理。H⁻³ 权重的可和性在五维独立证明。

`periodic5DRawAtomicLift_uniform_hminusThree_tail` 进一步证明：对任意 `ε > 0`，存在同一个有限 `K`，使上述实际尾部期望对所有 `N ≥ 1`、所有满足 `a > 0` 和 `aN=L` 的 `a` 均小于 `ε`。该尾界对 `N` 一致。

## 紧性与整序列识别

权重 `(1+‖k‖∞)^(-11/2)` 也可和，所以相同源二阶矩估计给出 H⁻¹¹⁄⁴ 总能量的一致期望界。权重比为

\[
 \frac{w_3(k)}{w_{11/4}(k)}=(1+\|k\|_\infty)^{-1/2}\longrightarrow0.
\]

`isCompact_closure_periodic5DElevenQuartersBall` 从明确的有限整数频率盒、有限复数坐标投影和统一截断误差，证明 H⁻¹¹⁄⁴ 有界球映入 H⁻³ 后其像的闭包紧。随后对实际源 lift 的强范数平方应用 Markov 不等式，得到 `periodic5DFixedVolumeProbabilityMeasureSet_tight` 和 `periodic5DFixedVolume_prokhorov_subsequence`。

`periodic5DFourierFamilyProjection_finiteSource_map` 精确证明 H⁻³ 源律经过解码坐标 `x_k / sqrt(w_3(k))` 的有限家族投影，等于实际五维物理格点 Fourier 测试家族的律。结合泛维数固定体积协方差收敛，得到 `periodic5DFixedVolume_fourierFamily_marginal_tendsto`。

每个弱收敛子列的有限家族边缘通过连续映射定理识别为相同的五维预解式高斯律。坐标柱集生成 H⁻³ 的 Borel σ 代数，因此 `periodic5D_probabilityMeasure_ext_of_fourierFamily_marginals` 给出概率测度唯一性。对每个子列再次应用 Prokhorov 并识别其极限，即得整序列弱收敛。

`periodic5DGaussianTarget_fourierFamily_hasGaussianLaw`、`periodic5DGaussianTarget_fourierFamily_mean_zero` 和 `periodic5DGaussianTarget_fourierFamily_covariance_quadratic` 明确给出全部有限 Fourier 家族的高斯性、零均值及五维预解式协方差矩阵。没有声称已经单独证明无限维 `IsGaussian` 类谓词。

## 验证与复现

来源命令：服务器隔离工程内 `lake build AImathPPhi2Clean.Periodic5DGaussianMarginals` 及 `lake env lean Audit5D.lean`。均使用项目钉死的 `leanprover/lean4:v4.34.0-rc2`，Lean commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`，Mathlib commit `852d20a84581aeba8527bd01d0be361d8c0e71c0`。最终主定理及契约所列端点的 `#print axioms` 仅含 `propext`、`Classical.choice`、`Quot.sound`。新增五维源码没有 `sorry` 或声明的 `axiom`。

解压审计包，在解压后的项目目录执行：

```sh
lake exe cache get
python REPRODUCE.py
```

包内脚本验证所有打包源码和配置的 SHA256，再构建最终模块并执行冻结类型及公理审计。完整工程源码、依赖锁、typed contract、成功构建日志、公理日志均包含于包内。交付包 SHA256：`3424b3573469c4f894efdfc911922a6348fb9e15f3302de0c56a047a460c06b9`。

## 保留与范围

服务器五维隔离工程中的全部既有 Lean 源码与三维 H⁻³ 基线逐字节比较相同。本机此前三维 companion、合并 H⁻³ PDF 及其源码归档的 SHA256 均与发布记录一致。

本结论不包含相互作用场、无限体积极限、OS 重构，或单独的无限维 `IsGaussian` 谓词定理；它证明实际五维源律在上述 H⁻³ 完备载体中的整序列弱收敛，并以全部有限 Fourier 家族的中心高斯预解式律唯一刻画目标。
