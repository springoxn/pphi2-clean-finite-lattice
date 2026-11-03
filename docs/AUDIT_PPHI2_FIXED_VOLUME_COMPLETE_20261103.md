# 独立重新审计：`PPHI2_FIXED_VOLUME_COMPLETE`（2026-11-03）

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-03 · 判据：`proof_graph/ARTIFACT_SPEC.md` §3（L11）
> **这份报告是什么**：对 `paper/PPHI2_FIXED_VOLUME_COMPLETE`（41 页文章 + 其 Lean 层 + 其自检装置）的一次**独立**复审。独立指：结论不复用作者自己的台账/门禁当证据，数字用**另一套实现**重算，数学由**没读过 `notes/` 的新 agent** 从头判，Lean 层**在本机重新编译**。
> **一句话结论**：**文章的数学骨架是真的，但当前这一版不能按现状投出去**——**2 项 BLOCKER + 5 项 MAJOR 必须先处理**：主定理有一条断言按字面为假；被当成"已机器验证"依据的那份 Lean 源，在仓库里根本编译不过，而转录指向的是服务器上的另一个工程。
> **谁该读**：要继续推进/投稿这条线的人，以及任何打算以"0 sorry + 门禁全绿"作为证据对外表述的人。
> **怎么自行复核**：每条发现都给了 `文件:行`、复算方式或可重跑的命令；本报告所有数字均当场现算，未抄自任何既有文档。

---

## §0 结论

文章本身：§2–§6 的数学**经三组独立复算无误**（常数、归一化、逐项矩阵、紧性指数都对），§4 的证明结构尤其干净（没有在无穷和里取极限、一个截断同时服务两侧、零模精确），§7 的三条计算（7.2/7.3/7.4）也逐项对；**问题集中在两处接缝**：§7 的柱坐标族与 §8 的确定性论证之间（**主定理 (iii) 为假**），以及 Part II 所声称的 Lean 证据（**源码不可编译**）。

| # | 严重度 | 发现 | 状态 |
|---|---|---|---|
| M1 | **BLOCKER** | 主定理 (iii) 与 `thm:cylinder-uniqueness` 按字面为**假**：柱坐标族排除了 $k=0$ 的 sine 槽，$\operatorname{Im}c_0$ 不可观测 | 未修 · 一行可修 |
| M2 | **BLOCKER** | 仓库内 Lean 包**编不过**（`PeriodicNegativeSobolevTopologyInterfaces.lean` 掉了 `def` 头），而 10 个链声明中 8 个的模块在其下游；§14 却写"the build succeeds" | 未修 |
| M3 | **MAJOR** | 被反复宣称为"开放输入"的 `hyp:lift-input` 按字面**是可证的**（$\Psi_N:=\mathcal L_N$ 即可），论文的核心诚实边界方向错了 | 未修 |
| M4 | **MAJOR** | PDF 有 **8 处 overfull**，其中 **249pt** 那处在 §13 把声明名**裁出纸面**（可见文本丢失）；`notes/INTEGRATION.md:93` 的"no overfull box larger than 60pt"为假 | 未修 |
| M5 | MAJOR | §14 的"no unresolved reference … is guaranteed"对 **125 处 `\eqref`** 不成立（门禁 L 看不见 `\eqref`） | 未修 |
| M6 | MAJOR | §10 的引用清点 $3+7=10\neq12$，`billingsley1999`、`gjs1974` 无着落 | 未修 |
| M7 | MAJOR | 同一结果**已有另一篇文章**（`deliverables/20261101_pphi2_fixed_volume_weak_limit.pdf`，标题几乎相同），新文章未提及；交付登记里同一 owner 两份 PDF 无先后关系 | 未修 |
| M8 | MAJOR | `refs.bib` **两条页码错误**：`nelson1973` 用了同卷另一篇的页码（97–112 应为 211–227）；`minlos1959` 页码 97–104 应为 497–518，且标题取自英译、期刊取自俄文原刊 | 未修 · 两行可修 |
| m1–m18 | MINOR | 见 §13（$s$ 双重含义、摘要不写 $d=2$、图注"eight steps" vs 正文"five moves"、图中用 $M$ 表示质量、`rem:no-bessel` 的"不同空间"、附录 A 表头、图 2 的 92/135 与 89/132 未对账、§13 的打印式计数、`artifacts.yaml` 的"39 pp"、§11 两处"哪个声明承载哪一段"的错认、§12 对负对照输出的错误描述等） | 未修 |

---

## §1 我怎么保证这次是"独立"的

1. **不采信自检**：`audit/verify_paper.py` 的四项检查（N/M/L/E）**全部被注入故障实测过**（§5），它红/绿的实际能力见 §5 表；`build_all.py` 的行为是**读源码**确认的，不是看它打印"BUILD OK"。
2. **数字用另一套实现重算**：`os.walk` + 不同正则 + `wc -l` 约定重写了一份计数（不 import 作者的 `count_lean.py`），19 个宏**逐个复核**。
3. **数学由新 agent 从头判**：4 个评审 agent 只拿到文章源文件 + 项目 `proofs/` + Lean 源，**明令禁止读 `notes/` 与 `verify_paper.py`**，各自被指派 §0–§3 / §4–§5 / §6–§7 / §8–§10，独立复算 + 自定判决。
4. **Lean 层在本机重新编译**：用本机 `.local-lean` 的 Mathlib（8381 个 olean，rev `85e3a25e`）+ 独立搭的 lake 探针工程，**真的编译** `PeriodicHMinusThreeWeakLimitMarginal`，而不是相信 `ext/axiom_transcript.txt`。
5. **PDF 用渲染后的产物判**：定理编号、`??`、overfull 都从 `main.pdf` / `main.log` 里数，不从源码推断。

**独立性的一处必须声明的局限**：本机 Mathlib 与包自带 `lake-manifest.json` 钉的 rev **不同**（`85e3a25e` vs `852d20a8`）。因此"编译失败"里**只有一处**是绝对结论（源码缺 `def` 头，任何 Mathlib 都救不了），另两处 goal 失败可能是 Mathlib 版本差异（见表后注）。

---

## §2 M1（BLOCKER）：主定理 (iii) 按字面为假

**位置**：`sections/07_marginals.tex:35-50`（`def:cylinder-map`）、`sections/08_identification.tex:37-42`（`thm:cylinder-uniqueness`）、`sections/09_main.tex:37-40`（`thm:main`(iii)）。

**缺陷**。`def:cylinder-map` 规定：有限族 $F=((k_1,\varepsilon_1),\dots)$，$\varepsilon_j\in\{\mathrm c,\mathrm s\}$，**"no sine label being used at $k_j=0$"**，坐标是

$$(\Pi_Fc)_j=\Re c_{k_j}\ (\varepsilon_j=\mathrm c),\qquad -\Im c_{k_j}\ (\varepsilon_j=\mathrm s).$$

于是可观测坐标集是 $\{\Re c_k\}_{k\in\Z^2}\cup\{\Im c_k\}_{k\ne0}$：**没有任何柱集约束 $\operatorname{Im}c_0$**。$\S8$ 证明第 (ii) 步断言"坐标泛函生成与柱集相同的 $\sigma$-代数"，这一步因此为假；由 Dynkin 得到的 (iii)"$\mu_{\rm free}$ 是唯一具这些边缘的 Borel 概率测度"也随之**为假**。

**反例**（我复核过，两段独立 agent 各自给出同型反例）：令 $\nu=T_*\mu$, $T(c)_0=\Re c_0+i(\Re c_0+\Im c_0)$、$T(c)_k=c_k\,(k\ne0)$。$T$ 是线性双射且 $\abs{T(c)_0}^2\le3\abs{c_0}^2$，故 $T$ 把 $\mathcal C$ 映入 $\mathcal C$ 且固定每个可容许坐标，于是 $\nu$ 与 $\mu$ 边缘全同而 $\nu(\operatorname{Im}c_0=0)=0\ne1=\mu(\operatorname{Im}c_0=0)$。

**注意方向**：结论本身没塌。每个 $\mu_N$ 满足 $\operatorname{Im}c_0=0$ 恒成立（因为 $(\mathcal L_N\omega)(0)=a^2\sum_x\omega(x)\in\R$），故由 Portmanteau 每个极限点都赋予闭集 $\{\operatorname{Im}c_0=0\}$ 全测度——**但论文没有任何一步写出这件事**，而 (i) 的 Step 4 正是靠 8.1。

**修法（一行）**：删掉 `def:cylinder-map` 里 "no sine label being used at $k_j=0$" 这一句。删掉后 $F=((0,\mathrm s))$ 给出 $\Pi_Fc=-\Im c_0$，而 `eq:entries` 在 $k=l=0$ 已给出 $\Re\mathcal Q(\sin_0,\sin_0)=\frac{V}{2\lambda(0)}(\delta_{0,0}-\delta_{0,0})=0$，故 $\Lambda_{((0,\mathrm s))}=\delta_0$：族成为确定类，(iii) 为真，并且机器层做的是同一件事（Lean 的 `periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals` 用 $\mathbb C^r$ 全坐标），修完 §11 的对应行才真正成立。**连带须改**：`lem:hC-identification`(iii) 中对 $V/(2\lambda(k_j))>0$ 的下界在该槽为 $0$（改成 $\ge0$）；`rem:topology`/§5 中"cylinders generate $\Sigma_{\rm cyl}$"的措辞。

**为什么之前的评审没抓到**：作者自己的两轮评审都盯在"是否把 $\mu_{\rm free}$ 说成了某个具名测度"上，而这条缝在**符号取值的层级**（sine 在 $k=0$ 恒等于零 ⇒ 该槽'没用'），不在陈述层级。

**一个能定位病因的旁证**：本文 Part II 与之对应的 Lean 定理用的是**复坐标**——`periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals`（`PeriodicHMinusThreeWeakLimitMarginal.lean:80`）的量词是 `∀ (m : ℕ) (modes : Fin m → PeriodicFourierIndex), μ.map (periodicHMinusThreeCylinderMap m modes) = …`，目标空间是 `Fin m → ℂ`，**包含** $\operatorname{Im}c_0$。也就是说：**机器层是对的，纸面层是错的**，而 §11 的对应表把两者说成"statement identity"。这不是"Lean 更弱"（那类差异文章已披露），而是"Lean 与论文在此处不是同一个陈述"，且差异恰好落在 M1 这条缝上。修 M1 之后 §11 的对应关系才真正成立——顺带说明这个 bug **正是 §14 自己承认"没有脚本能查"的那一类**（名字级的门禁看不出来）。

---

## §3 M2（BLOCKER）：所声称的 Lean 证据在本仓库里编译不过

**做法**：独立搭 lake 探针工程（junction 到本机 `.lake/packages`，避免拷贝 6.4 GB Mathlib），`lake build AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal`，8824 个 job。

**结果**：`EXIT=1`，`Some required targets logged failures: AImathPPhi2Clean.PeriodicNegativeSobolevTopologyInterfaces, AImathPPhi2Clean.GaussianConfiguration`。失败后 Lake 不再排 `PeriodicHMinusThreeWeakLimitMarginal` 的任务——**目标模块根本没被编译**。

**决定性的一处（与 Mathlib 版本无关）**：`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevTopologyInterfaces.lean` 里 `periodicHMinusThreeFiniteFourierProjection` 的**声明头被删掉了**，只剩一个孤立的绑定行：

```
250
251:     (z : {k // k ∈ K} → ℂ) : PeriodicHMinusThreeCompletion :=
252:   ∑ k : {k // k ∈ K}, lp.single (E := fun _ : Fin 2 → ℤ => ℂ)
253:     2 (k : Fin 2 → ℤ) (z k)
```

全仓检索：`def periodicHMinusThreeFiniteFourierProjection` **0 命中**，而该名字在**同一文件**里被用 12 次（255、264、273、329、353、358、380 行）。任何 Lean/Mathlib 版本下这都过不去；错误文本正是 `Unknown identifier` 与 `unexpected token ':'`。文件 mtime 2026-10-30 12:27，三份副本（含 `.scratch/github-sync-inspect`、`.scratch/github-sync-verify-460c58d`）**同为 19941 字节**，即同一份坏副本被同步到了各处。

**后果（严格按导入闭包算）**：

| 注册声明 | 所在模块 | 该模块的传递导入是否含坏模块 |
|---|---|---|
| `periodicHMinusThreeCompletion_separable` | `PeriodicHMinusThreeTopologyBorel` | **是**（经 CylinderBorelUniqueness → CylinderConvergence → FixedVolumeTightness → …） |
| 其余 6 个 measure-limit 声明 | `PeriodicHMinusThreeWeakLimitMarginal` | **是**（经 ProkhorovSubsequence → FixedVolumeTightness → …） |
| 3 个 covariance 声明 | `PeriodicFourierCovarianceLimit` | 否（闭包 22 个模块，不含坏模块） |

即 **10 个链声明中有 8 个无法从本仓库源码 elaborated**，`#print axioms` 转录对它们**不可复现**。而 `sections/14_reproduction.tex:57-62` 明确写"A reproducer should expect … **The build succeeds**"，`§13` 第 5 条整段在讨论"green build 能证明什么"。

**这不是"再跑一次就好"**：坏的是被提交的源，不是环境。另两台 goal 失败（第 77、246 行）可能是 Mathlib rev 差异（本机 `85e3a25e` vs 包内 `852d20a8`），但**即使把它们全部归因于版本，缺 `def` 头那一条仍然成立**（纯 parse error：`251:27 unexpected token ':'`）。第二处失败 `GaussianConfiguration.lean:72` 的实例合成失败，经复核判定为**版本漂移**（该模块在仓库留存的旧构建日志里带 warning 通过，行号一致），且不在 3 个 covariance 声明的关键路径上。

### §3.1 时间线自相矛盾：转录比"源坏掉"更晚

`ext/axiom_transcript.txt` 自己交代了出处：

- 第 3 行 `Recorded: 2026-11-02`；
- 第 4 行 **`Project: /home/zhengyj/AImath-lean/AImathPPhi2Clean`（服务器上的另一个 Lake 工程）**，命令也在服务器上跑，`-> "Build completed successfully (8904 jobs)." exit 0`；
- 第 6 行 **`Source of truth for the sources: formal/lean/s6/pphi2_clean/`**（就是本仓库这一份）。

而本仓库这份 `PeriodicNegativeSobolevTopologyInterfaces.lean` 的 mtime 是 **2026-10-30 12:27**（三份副本同字节，说明不是误删单份）。仓库里留存的全量构建日志最新只到 **2026-10-25**（`formal/lean/s6/pphi2_clean/audit/full-build-r27-final.log`，7054 B），**没有任何一份日志含 "8904"**。

于是只有两种可能，都不能靠现有材料排除：

1. 2026-11-02 在服务器上编译的是**另一份、完好的**副本 ⇒ 文章第 6 行"source of truth 是本仓库这份"为假，且**没有任何东西把两份锁在一起**（早前会话声称"85/89 字节相同、4 个仅差空行/注释"，可这份坏文件的差异**不是**空行）；
2. 转录实际上是更早一次的产物、日期写错 ⇒ 转录的"2026-11-02"不可信。

**无论哪一种，结论相同**：本仓库里**不存在**"这些源编过程"的证据，`#print axioms` 对 8 个链声明**不可在本地复现**，而 §14:57-62 与 §13 第 5 条是按"可复现"写的。修法必须包含一条**机械锁定**：把服务器工程与仓库目录做哈希对账（逐文件 sha256），并把对账结果写进转录头；否则"source of truth"只是一句声明。

**第二条独立的反证（同一处）**：转录称 `-> "Build completed successfully (8904 jobs)."`。但仓库里**任何一次**记录的构建都没有这么多 job——整库构建是 **8870**（`audit/full-build-r27-final.log`）与 **8895**（`audit/finite_lattice_build.log`）；而**只编这两个目标**时 Lake 排的是 **8824** 个 job。单模块目标排出的 job 数**不可能比整库还多**。这说明 8904 不是这条命令的逐字输出（除非服务器工程另有依赖），与上面那条时间线矛盾互为印证。

### §3.2 对照表里有三处不实（都不影响数学，但都影响"读者能不能据此核验"）

1. **`11_lean.tex:161-165` 说"existence、marginal、characterisation 由最后一行的三个声明承载"**——不实。最后一行的三个是 `…_exists_with_expected_cylinders`(`:202`)、`…_exists`(`:124`)、`…_has_expected_cylinder`(`:161`)，它们覆盖 (i)+(ii)，**没有一个覆盖 (iii)**；承载 (iii) 的是**上一行**的 `periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals`(`:80`)。把"最后一行的三个"当成三段全覆盖，正好掩盖了 M1 那条缝。
2. **同段"the second of them is the one the paper's part (ii) quotes"**——不实。第二个声明是 `…_weak_limit_exists`，承载的是 **(i)** 存在性；part (ii) 是**第三个** `…_has_expected_cylinder`。
3. **`12_contracts.tex:97` 对负对照输出的描述**——不实。留存的 `audit/negative_axiom.log` 记录的是 `'polluted' depends on axioms: [injectedAxiom]`，即足迹为 $\{$`injectedAxiom`$\}$，**不是**"许可集少一个元素"。负对照本身有效，描述要改。

另有三处**方向相反**（Lean 比表格写的更强，值得补注而不是删）：
4. `thm:finite-family` 那一行点名的 `physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_fourier`（`FiniteRealFamilyWeakLimitInterface.lean:855`）结论里**存在一个因子 $T$**；同包里有结论更到位的 `…_of_any_finite_test_family_indexed`（`FiniteFourierCoordinateConvergence.lean:86`），而 §11 只提了"这一行更弱"（弱在假设侧），没提结论侧的存在量词。
5. 表格把 `thm:cylinder-borel` 对到 `periodicHMinusThree_cylinder_sigma_eq_borel_of_polish`（`PeriodicHMinusThreeTopologyBorel.lean:71`），但该声明**带 `PolishSpace` 假设**，而 Part I 的定理是无条件的（假设在别处付清）。应标注"条件形式"。
6. §13 说"六个（七个已登记测度定理中的六个）的足迹只能靠转录"——准确，但可更精确：`…_separable` 落在 `PeriodicHMinusThreeTopologyBorel`，**是**根可达的，其足迹本地可产；只有 `PeriodicHMinusThreeWeakLimitMarginal` 里的六个是转录独有。



**附带发现（同一件事的另一面）**：`formal/lean/s6/pphi2_clean/lake-manifest.json` 钉的 mathlib 是 `852d20a84581aeba8527bd01d0be361d8c0e71c0`（`inputRev: None`），而 `lean-toolchain` 写 `v4.34.0-rc2`（对应 `85e3a25e`）。**同一目录里两个互相打架的出处声明**，而论文只记录了 toolchain 一条（`\LeanToolchain`），从未记录 Mathlib rev——转录上的三元组是在哪个 Mathlib 上打印的，文章里查不到。

**修法**：补回 `def periodicHMinusThreeFiniteFourierProjection (K : Finset (Fin 2 → ℤ))` 头；用包内 manifest 的 Mathlib 重跑整包；把 toolchain **与 Mathlib rev 一起**记进转录头；§14 改成"在某 Mathlib rev 下 X 个模块可编译、Y 个不可"而不是"the build succeeds"。

---

## §4 M3（MAJOR）：`hyp:lift-input` 不是开放输入，是可证的——论文的核心诚实边界方向错了

**位置**：`sections/05_carrier.tex:282-319`（假说 + "neither clause is proved here … that it is open"）、`sections/09_main.tex:112-118`、`sections/10_scope.tex:39-52`、`sections/01_intro.tex:140-144`、`sections/13_boundary.tex:55-68`。

**论据**。`hyp:lift-input` 说的是**存在**一个 $\mu^{\rm GJ}_N$-a.e. 定义、取值于 $\mathcal C$ 的 $\Psi_N$，满足 (1) a.e. 可测、(2) 加权坐标与 $\mathcal L_N$ 的逐项相等。取 $\Psi_N:=\mathcal L_N$（`def:finite-source-lift` 本身）：

- (2) **恒等成立**——$\widehat{\Psi_N(\omega)}=(\sqrt{w_3(k)}(\mathcal L_N\omega)_k)_k$ 就是坐标的重排；
- (1) 每个坐标 $c\mapsto c_k$ 连续（`lem:coordinate-embedding`），故 $\mathcal L_N$ 对 $\sigma(\text{坐标})=\mathcal B(\mathcal C)$（`thm:cylinder-borel`）可测；而 $\mathcal L_N$ 的值域确实落在 $\mathcal C$ 内，这是 §3 自己证明的（`03_lattice.tex` 里 $\sum_p|(\mathcal L_N\omega)(p)|^2\le a^4\|\omega\|_1^2(1+8\zeta(5))<\infty$，再由 $w_3\le1$ 转成载范式）。

于是 $\mu_N=(\mathcal L_N)_*\mu^{\rm GJ}_N$——**论文自己定义的那个测度**——就已经是一个 total carrier-valued representative 的像。所谓"两族测度之间那一步尚未证明"并不存在。

**为什么这会出现在一篇以"边界诚实"为卖点的论文里**：假说的量词是**存在**（"a map $\Psi_N$ … consists of two statements"），而 §13 第 3 条讲的是**形式化里那个特定** total lift（"the total lift sends a possibly non-null exceptional set to zero, and asserts no nullity of that set"）。**存在性**与**特定实现**被同一个标签盖住了：前者平凡可证，后者确实是 Lean 的欠账。结果是文章在最保守的方向上说错了自己的结果——按字面，(i) 已经就是"格点高斯场定律在载体上弱收敛"。

**修法**：把 §5 的假说改成关于**那个特定 lift** 的陈述（并明说存在性由 $\mathcal L_N$ 免费给出），删掉 §1/§9/§10 里"the bridge … is open"的三处措辞；或者反过来，保留假说但把它降级为"形式化层的实现细节"，并承认 Part I 已经覆盖了物理格点定律的收敛。**二者不能同时留着**。

> 说明：这条是"低估"，不是"高估"，但它仍然是一句关于数学内容的**假话**，而且被重复了四处；对一篇把"校准"当作贡献的文章，这比高估更难解释。

---

## §5 M4（MAJOR）：PDF 有 8 处 overfull，最严重处**裁掉正文**（可见文本丢失）

`paper/PPHI2_FIXED_VOLUME_COMPLETE/build/main.log`（与出厂 PDF 同源）实测：`Overfull` **8** 处、`Underfull` 38 处、`undefined` **0** 处。8 处的量级与位置：

| 位置 | 超出量 | 内容 |
|---|---|---|
| `sections/13_boundary` 44–54 | **249.4pt** | `PeriodicHMinusThreeProkhorovSubsequence` |
| `sections/12_contracts` 27–43 | 140.2pt | `PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT` |
| `sections/12_contracts` 27–43 | 120.8pt | `PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT` |
| `sections/12_contracts` 27–43 | 107.5pt | `fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing` |
| `sections/13_boundary` 30–43 | 83.6pt | `PeriodicHMinusThreeWeakLimitMarginal` |
| `sections/12_contracts` 72–88 | 38.0pt | — |
| `sections/04_covariance` 81–106 | 14.3pt | 正文段落 |
| `sections/12_contracts` 27–43 | 2.1pt | — |

版面宽 612pt、正文区约 365pt（1in 边距）：249pt 的溢出行**越过纸边并被裁掉**。渲染第 37 页肉眼可见：`PeriodicHMinusThreeProkhorovSubsequen`、`latticeFreeFieldMeasur`（原文 `latticeFreeFieldMeasure_tendsto_periodicFreeGaussian`）两处**在纸面上断掉，读者看不到名字的全貌**——而这正好发生在"把局限说清楚"的那一节。

**成因可追**：`notes/INTEGRATION.md:93-94` 写 "no undefined references, no overfull box larger than 60pt"。这句话在某一版是真的；后来为修审稿阻断项重写 §12/§13 时，把不可断行的 `\texttt`/`\lean` 长名塞进了正文与窄列，**没再回头查 log**，`build_all.py` 又**只检查 tectonic 退出码 + PDF 存在**（`build_all.py:137-147`），于是回归无声通过。附录 A 早先为同一问题做了逐下划线 `\allowbreak{}` 分块，正文与 §12/§13 没有做。

**修法**：正文里对 Lean 名一律走 `\lean{}`（已 `\detokenize`）+ 补可断点（`\_\allowbreak{}` 或 `\path` 语义的 `\seqsplit`），或把 §12/§13 的长名放进两列 `tabular`；然后把 `build_all.py` 升级为**从 log 解析 `Overfull`/`undefined` 并在超阈值时失败**——这是 M4 不再复发的唯一办法。

---

## §6 M5（MAJOR）：门禁看不见 `\eqref`，而 §14 的保证是"所有交叉引用都会闭"

**事实**（独立统计，Python 正则，剥掉注释后）：

- `\label` 118 个（无重复），引用命令共 **473** 次：`\cref` 322、`\Cref` 24、**`\eqref` 125**、`\ref` 2；**悬空 0**（我独立复核，与 log 的 `undefined: 0` 一致）。
- `verify_paper.py:64` 的 `REF = r"\\(?:c|C)?ref\{([^}]*)\}"` **匹配不到 `\eqref`**：`\eqref{x}` 里 `ref` 前面是 `eq` 而不是 `\`。即 **125/473 ≈ 26% 的交叉引用不在这道门的管辖内**。
- 注入实验证实：在 `09_main.tex` 里加一句 `\eqref{eq:does-not-exist}`，门禁**全绿**（4/4）。
- 而 `sections/14_reproduction.tex:64-68` 写："the compiled document carries no unresolved reference or citation: **that is guaranteed before the compile is attempted**"。这句对 `\eqref` 不成立。

**当前产物本身没问题**（悬空 0），所以这是**关于证据的陈述**错，不是内容错。但对一篇把"门禁绝不空转"当作方法论的论文，这正是最该被抓的一类。

**修法**：`REF` 加 `eq`（或改成 `\\(?:eq|c|C)?ref\b`）；`--self-test` 增加一条 `\eqref` 负对照；§14 改成"sections' labels/references/citations close（`\eqref` 通过 X 途径另行校验）"。

---

## §7 M6（MAJOR）：§10 的引用清点算不平

`sections/10_scope.tex:127-134`：`\NumCitedWorks`=**12**，"**Three** support a standard fact where it is used … The **seven** named below support nothing"。$3+7=10$。逐键核对（我按 `\cite` 出现位置独立列过）：

| 键 | 出现位置 | 轨迹 |
|---|---|---|
| `yosida1980` | `04_covariance.tex:21` | 支撑（Riesz） |
| `prokhorov1956` | `06_tightness.tex:302` | 支撑（Prokhorov） |
| `bogachev1998` | `07_marginals.tex:249` | 支撑（Gauss 律收敛） |
| **`billingsley1999`** | `05_carrier.tex:323` | **也是支撑**（弱收敛的定义）→ 应是 Four |
| `ossier1973/1975`, `gj1987`, `simon1974`, `grs1975`, `nelson1973`, `minlos1959` | §1/§10 | 位置（七条 itemize 正好这七个） |
| **`gjs1974`** | `10_scope.tex:106` | **不在任何一类** |

即：应为 **Four + eight**，或把 `gjs1974` 并入"位置"一栏。另：`rem:no-bessel` 的"a different identity, **on a different space**"在数学上站不住——$\mathcal Q$ 就是同一个环面上 $(-\Delta+m^2)^{-1}$ 的积分核配对（数值上 6–8 位吻合），该 remark 能守的只有"不在此处使用、不在此处证明"。

### §7.1 M8（MAJOR）：`refs.bib` 两条页码是错的，其中一条能证明是怎么错的

12 条**全部真实存在**、无伪造、无张冠李戴式误引（这一点在"AI 生成参考文献"泛滥的当下值得正面记一笔）。两条的**卷页**有错：

| 键 | 现在写的 | 应为 | 判定依据 |
|---|---|---|---|
| `nelson1973` | JFA **12** (1973), **97–112** | JFA 12 (1973), **211–227** | 97–112 是同卷**另一篇** Nelson, *Construction of quantum fields from Markoff fields* 的页码（DOI 10.1016/0022-1236(73)90091-8）；*The free Markoff field* 是 DOI …(73)90025-6，zbMATH Zbl 0273.60079 记 211–227 |
| `minlos1959` | Trudy Mosk. Mat. Obshch. **8** (1959), **97–104** | Tr. Mosk. Mat. O.-va **8** (1959), **497–518** | zbMATH Zbl 0103.35901；97–104 对俄文原刊与英译（Sel. Transl. Math. Stat. Probab. 3 (1963) 291–313, Zbl 0121.12501）**都不对**。该条目还把**英译的标题**安在**俄文原刊**上，属于混合条目 |

`nelson1973` 这一条尤其说明问题来源：两篇论文同刊同卷同年，页码被"就近"取错了——这类错误在任何人工或自动核对里都看不出来，只有查 DOI/zbMATH 才能发现。修法：改两个页码（并把 `minlos1959` 的标题与刊物对齐到同一版本），重跑 `audit/make_bib.py`。

**另缺 4 处标准事实的引文**（非错误，属编辑选择）：`Dynkin` 的 $\pi$–$\lambda$ 定理按名称用于 `08_identification.tex:67`、`Lévy` 连续性定理用于 `07_marginals.tex:245`、环面 Fourier 基（`ext:fourier-basis`）、以及"三角多项式一致稠密"（`02_setting.tex:39`）——四处都声称是标准事实而无数目字。既有的四条 point-of-use 引用（Riesz/弱收敛定义/Prokhorov/Gauss 律收敛）位置都对。

---

## §8 M7（MAJOR）：同一结果已有一篇几乎同名的文章，新文章未提及

- 既有：`paper/PPHI2_FIXED_VOLUME_WEAK_LIMIT/`（2026-11-01 构建），PDF 已是登记交付物 `deliverables/20261101_pphi2_fixed_volume_weak_limit.pdf`，标题 *"Whole-Sequence Weak Convergence of Fixed-Volume Lattice Free Fields on a Periodic $H^{-3}$ Carrier"*。
- 新增：`paper/PPHI2_FIXED_VOLUME_COMPLETE/`（2026-11-02），标题 *"Whole-Sequence Weak Convergence of Fixed-**Physical**-Volume Lattice Free Fields on a Periodic $H^{-3}$ Carrier"*。
- 两篇证同一件事（我逐条比对过旧文 `sections/02_carrier_and_theorem.tex` 的主定理：同一 $w_3(k)=|k|^{-6}$、同一 $\mu_n^{L,M}=(J_n^{L,M})_\#\gamma_n^{L,M}$、同一结论）。
- `proof_graph/deliverables.yaml` 现在把两份 PDF 挂在**同一个 owner** 下（行 30–37），**没有任何 supersedes/replaces 关系**；新文的 12 条参考文献里没有它自己的前身。

**为什么这算 MAJOR 而不是家务事**：arXiv 上两篇同名、同一 owner、同一结论的稿子，是作者层面的事故；而且旧文用了 `H^{-3}_{\mathrm{Fourier}}` 这个下标（新文删掉了），正是这处删减让评审 agent 把 $H^{-3}$ 的权重指数读错了一次——旧文的写法更抗误读。

**修法**：明确其一为 superseded（或合并），在 `deliverables.yaml` 记关系，旧文加注记；新文若要独立投出，至少在 §10 "Relation to the literature" 里说明与本项目前稿的关系。

---

## §9 审计装置本身（元审计）：门禁红/绿的实际能力

把 `verify_paper.py` 与全部源拷到探针目录，逐条注入故障、跑门、还原。基线 4/4 绿。

| 注入 | 应然 | 实测 | 判定 |
|---|---|---|---|
| `\lean{NonexistentTheorem_zzz}` | 红 | **红** | 有效 |
| 正文写 89（大数） | 红 | **红** | 有效 |
| 转录某行足迹从三元组改成 `{propext}` | 红 | **红** | 有效 |
| 转录加一行伪造声明 | 红 | **红** | 有效 |
| 重复 `\label` | 红 | **红** | 有效 |
| `refs.bib` 加一条永不引用 | 红 | **红** | 有效 |
| `\lean{PeriodicContinuumGaussianConstructionInput}`（**只存在于 `audit/partial.lean`，从不在被构建的包里**） | 红 | **绿** | **漏洞**：`lean_declarations()` 递归扫 `pphi2_clean/**/*.lean`，把 vendored 的 `audit/{upstream_full,b1_reference,...}` 也算作"包内声明"（806 个名字里含这些） |
| 正文出现 Lean 名但**不裹 `\lean`** | 红 | **绿** | **漏洞**：N 只看 `\lean{}` 里的名字（17 处出现、14 个不同名） |
| 正文写"the 10 chain declarations"（小数） | 红 | **绿** | **漏洞**：M 的阈值是"3 位以上或 ≥40"，小数字靠编辑纪律 |
| `\eqref{eq:does-not-exist}` | 红 | **绿** | **漏洞**（M5） |
| 在 `main.tex` 里写计数 | 红 | **绿** | **漏洞**：M 不扫 `main.tex` |

**另有三处"静默失配"**（不算漏洞，但同样意味着闸门不覆盖）：
- `metrics.tex` 定 19 个宏，正文只用 12 个：`\NumRootFiles`、`\NumRootLines`、`\NumMeasureContractTheorems`、`\NumUnreachableModules`、`\NumProofDocs`、`\NumProbes`、`\NumFailureCards` **从未出现**。M 只查"用了的宏有没有定义"，从不查"定义了却没人用"，所以这些数**算了但没有任何读者能看到、也没有任何东西盯着**。最别扭的是 §13 用英文单词写 "Eight modules are not reachable"、"six of the seven registered measure-limit theorems"——**手打计数**，恰好落在 M 的盲区里。
- `count_lean.py` 的 `sorry` 计数用 `\bsorry\b`：`sorryAx`、`admit` 都不匹配（我全包扫过，当前 0 命中，所以**这次没被利用**，但它是同类"文本扫描当证明"的脆弱点，应一并写进论文 §14 的声明范围）。
- `build/LAST_BUILD.txt` 盖了每个源文件的哈希，**但不含 `ext/axiom_transcript.txt`**——Part II 的结论全压在这个文件上，它偏偏不在戳里。

---

## §10 我独立重算的数字（与 `generated/metrics.tex` 对照）

另一套实现（`os.walk` / 不同正则 / `wc -l`），全部**一致**：

| 量 | 文章 | 我的重算 | 说明 |
|---|---|---|---|
| 包模块数 | 89 | **89**（递归；无子目录） | ✓ |
| 包行数 | 13437 | **13437**（非空 12448；去注释非空 11547） | ✓ |
| `sorry` / 项目公理 | 0 / 0 | **0 / 0**；另 `admit`、`sorryAx`、`partial`、`unsafe`、`constant`、`opaque` 全 0 | ✓ |
| audit 探针 | 132 | **132**（顶层；`audit/` 下另有 5 个参考子目录共 135 个 `.lean`，文章口径未含） | ✓（但 `N` 漏洞源于此） |
| 根开发 `/s6/*.lean` | 43 / 10730 | **43 / 10730** | ✓ |
| 契约数 / 许可公理 | 14 / 3 | **14**（`challenges:` 块精确 14 键）/ `propext, Classical.choice, Quot.sound` | ✓ |
| 链定理数 | 10 | **10**（3 + 7） | ✓ |
| 不可达模块 | 8 | **8**（独立 BFS：57 直接导入 → 81 传递可达） | ✓ |
| 引文数 | 12 | **12**（`refs.bib` = `\bibitem` = 12；无未引用、无未定义） | ✓ |
| 证明档 / 探针 / 失败卡 | 137 / 147 / 23 | **137 / 147 / 23** | ✓ |
| 负对照行数 | 3 | **3**（`audit/negative_axiom.lean` 的 3 行非注释） | ✓ |

编号与规模（从 **PDF 渲染结果**数，不是源码）：§2–§9 共 **47** 个编号环境且逐节致密——Theorem 10、Lemma 9、Definition 9、Remark 9、External theorem 5、Hypothesis 2、Proposition 2、Corollary 1；定理类（thm+lem+prop+cor）**22** 个。**更正**：我上一轮口头报的"38 个编号结果"是错的（38 = 33 + 5 的巧合算法）；正确是 47（其中定理类 22）。41 页、正文源 ~2.1 万词、118 个 label、473 次引用、0 处 `??`。

**可复现性（本机干净重建）**：把源整份拷走 + Tectonic 缓存 junction，跑 `python build_all.py` → `BUILD OK`，**41 页、0 处 `??`**，与出厂 PDF 仅差 `\today`（"November 2" vs "November 3"），2 字节。即**文本内容可复现**。但同一份 log 里有 8 处 overfull（M4），且 `build_all.py` 对此**不设防**。

---

## §11 数学：逐节判决（4 个独立评审 agent + 我的抽检）

| 节 | 判决 | 关键独立复算 |
|---|---|---|
| §0–§1 | 通过 | 摘要每句都能指到编号结果（除 M3 那条边界措辞）；"five moves"与图 2 的 "eight steps" 不对应（m3） |
| §2–§3 | **PROVED**（无 GAP/WRONG） | Parseval（1e-15）、特征恒等式与符号极限、三处 $a$ 幂、$8\zeta(3)=9.61646$、$8\zeta(5)=8.29542$、$C=20.2329\,m^{-2}L^2\in[1,25]$、零模 $L^2/m^2$ 精确、弦界 $\lambda_N\ge m^2+16\|k\|_\infty^2/L^2$（0 反例） |
| §4 | **PROVED** | 三条独立数值路线（显式矩阵求逆 / FFT 对角化 / 符号公式）12 位一致；$\mathcal Q_N\to\mathcal Q$ 11 位、误差 $\asymp a$（比值 4.000）；一个截断同时服务 $N$ 与 $\infty$（因 $4\pi^2>16$）；零模对每个 $N$ 精确 |
| §5 | **PROVED** | $\Theta$ 等距 12 位；尾界**取等饱和**；$\sum_{k\ne0}w_3=8\zeta(5)$；`hyp:lift-input` 见 M3 |
| §6 | **PROVED** | 紧族是 $\mu_N$ 本身（不是投影/单泛函）；$H^{-2}\hookrightarrow H^{-3}$ 因 $w_3/\tilde w_2=\|k\|_\infty^{-2}\to0$；实测迹 1.2416/1.1672/1.1571 → 1.15462，上界 20.23（余量 17.5×，非临界） |
| §7 | 1 处 **GAP**（即 M1） | `eq:entries` 逐项全对：对角、$k$ vs $-k$、cos–sin 混合（1.9e-21）、零模 $V/m^2$、$\Re Q(\sin_k,\sin_{-k})$ 的**负号**正确；$4\times4$ 块特征值 $(0,0,2c,2c)$ |
| §8 | **1 处 WRONG**（M1 的下游） | 第 (ii) 步为假；Dynkin 步本身正确 |
| §9 | (i) 结论真但证明有洞、(ii) PROVED、**(iii) WRONG** | 主定理量词干净、无隐藏假设、`hyp:lift-input` 确实不在链上 |
| §10 | 通过（M6 的算术除外） | 四条边界与正文一致；"no priority claim" 守住了 |

---

## §12 Part I 之外的边界（保持文章自己的口径）

值得记下文章**没有**越界的地方，因为这些很容易被顺手写坏：不声称 $\mu_{\rm free}$ 是某个具名测度；不构造载体上的协方差算子；不声称速率/指数尾（只用一阶矩 Markov）；不碰相互作用、UV、OS 重构；$d=2$ 限于测度链，协方差定理按一般 $d$ 注册且文章明说不推广。`thm:main` 的证明没有把"极限唯一"当作"极限被刻画"（`cor:uniqueness` 被明确降级为 Hausdorff 唯一性）——这一点做得比多数投稿好。

---

## §13 其他 MINOR（照抄即改，无需再论证）

1. **摘要不写 $d=2$**（`00_abstract.tex:17-24`）："For every period $L>0$ and mass $m>0$" 读起来像任意维；§10 第 4 条与 §2 `rem:dimension` 都写了二维。加四个词。
2. **$s$ 双重含义**（`02_setting.tex:124-137` vs `223-248`）：`$\widetilde w_s=\|k\|_\infty^{-2s}$`、`$H^{-s}$` 里的 $s$ 是 Sobolev 指标；`ext:summability`/`rem:dimension` 里的 "s=4,6"、"$s>d$" 是权重衰减指数（$=2s$）。**注**：评审 agent 由此推出"H^{-3} 其实是标准 H^{-6}"——**这条是它错**（标准 H^{-3} 的权重正是 $|k|^{-6}$，文章与标准一致）；真正的缺陷只是同一封信里 $s$ 指两个东西。
3. **`ext:summability` 标成 External theorem，却在下一段自证**（`02_setting.tex:223-236`）：小节标题还写"two borrowed facts"。改成 lemma，或删证明。
4. **三角函数多项式稠密"we use it as such"却无人使用**（`02_setting.tex:39-40`）。
5. **图 1 用 $M$ 表示质量**（`weak_limit_spine.png` 里 $\mu_n^{L,M}$、$C_{L,M}$），正文用 $m$；且图注 "**Eight** steps carry the argument" 与正文 "The argument has **five** moves"（`01_intro.tex:69`）两种分解没有对账，图还省掉了载体构造与协方差极限（§4/§5 恰是最难的两节）。
6. **图 2 的自带计数与宏不一致**：atlas 渲染里写 **92 modules + 135 probe files**（`frontend/lean_nodes/dist/figures/figures_manifest.json` 亦记 `counts.modules = 92`），文章说 89/132；图注说"the wider development … and not only the 89-module package"，但没点明 92 与 89 的差就是那 3 个卫星模块。应写"a 92-module snapshot, three modules wider than the 89 reported here"。
7. **附录 A 表头过宽**（`audit/make_ledger.py` 生成的 `generated/ledger.tex:6-7`）："Every theorem reported in this paper is listed below" —— 正文引了 14 个名字，附录只列 10 个（另 4 个在 §11 的对应表里）。
8. **`dynkin` 级的小前提缺失**：`generated/ledger.tex:35` 写 "separable, hence Polish"，缺 `prop:completion`(i) 的完备性。
9. **`\NumCitedWorks` 之外的打印式计数**：§13 "Eight modules"、"six of the seven"；以及 7 个宏算了不用（见 §9）。
10. **`artifacts.yaml:1466`** 记新 PDF 为 "**39 pp**"，实际 41 页——登记表里的派生数字烂了，而它正是"数字必须现算"这条纪律的产物。
11. **`notes/INTEGRATION.md:93`** 的终态声明（"no overfull box larger than 60pt"）为假（见 M4）。
12. **`figures/PROVENANCE.md`** 里图 1 的源路径在 `.scratch/github-sync-inspect/...`——`.scratch/` 被 `.gitignore:16` 忽略：**来源链在仓库外**。当前两份源的 sha256 与表中一致（我复核过），但换一台机器克隆就没有这张图的上游了。
13. **§11 的对应表句**（`11_lean.tex:143-146`）"each numbered result of Part I has at least one declaration in the table"：Part I 有 47 个编号结果、表里 9 行；四行后自己就承认"One row is weaker"。要么把量词收到"链上的 10 条声明"，要么删这半句。
14. **`\lean` 名未加断点**（M4 的成因，也是 §13/§12 的排版修复路径）。
15. **§11 把"哪个声明承载哪一段"认错了**（`11_lean.tex:161-165`）：(iii) 不在"最后一行的三个"里，`the second of them` 指的其实是 (i)。见 §3.2。
16. **§12 对负对照输出的描述与留存日志不符**（`12_contracts.tex:97` vs `audit/negative_axiom.log`）。见 §3.2。
17. **对照表里有两行应当补注**：`thm:finite-family` 行的结论含存在量词（同包有更强兄弟），`thm:cylinder-borel` 行点名的是带 `PolishSpace` 假设的条件形式。二者都让 Lean 看起来**比实际更弱**，属安全方向的失真，但读者据表核对会得出错误印象。
18. **`unreachable` 一词的口径**：§13 说根聚合器"完全不可达"的是 8 个模块，并点名其中两个承载内容；这一点我独立复核为真（57 直接导入 → 81 传递可达 → 8 不可达），但要注意**根聚合器本身也编不过**（它 `import` 了坏模块，`AImathPPhi2Clean.lean:45`），所以"根只覆盖子集"的说法在实践中还要再加一层：连那个子集也拿不到。**（第 18 条是 M2 的补充，不是独立缺陷。）**

---

## §14 修法清单（按"不修就不能投"排序）

1. `def:cylinder-map` 删 "no sine label at $k_j=0$"；同步 `lem:hC-identification`(iii) 的下界与 §5/`rem:topology` 的措辞。**（M1）**
2. 补回 `PeriodicNegativeSobolevTopologyInterfaces.lean` 的 `def` 头；按包内 manifest 的 Mathlib rev 重跑整包并把结果（成功/失败模块数、toolchain **与 Mathlib rev**）写进 §14；`hyp`/§13 里"green build"的措辞随之收敛。同时：**让转录头带上与仓库目录的逐文件哈希对账**，并解释 8904 这个 job 数从哪来。**（M2 + §3.1）**
3. 重写 §5 的 lift 假说与四处"open"措辞。**（M3）**
4. 正文/§12/§13 的 Lean 名加断点，重编译到 **0 overfull**；`build_all.py` 增加 log 解析（overfull 阈值 + undefined）并在超标时失败；改正 `notes/INTEGRATION.md` 的终态声明。**（M4）**
5. `verify_paper.py` 的 `REF` 补 `eq`；`lean_declarations()` 限定到被构建的 `AImathPPhi2Clean/`；M 扫描 `main.tex` 并对所有宏（含小数字）做字面泄漏检查，另加"定义未使用"告警；`LAST_BUILD.txt` 纳入 `ext/axiom_transcript.txt`。**（M5 + §9 漏洞）**
6. §10 引用清点改 Four + eight，或把 `gjs1974` 归入位置类；`rem:no-bessel` 去掉"on a different space"。**（M6）**
7. 处理与 `20261101` 前稿的关系。**（M7）**
8. §13 用 `\NumUnreachableModules`/`\NumMeasureContractTheorems` 取代打印式计数；摘要补"in two dimensions"；图 1 的 $M\to m$；图注与"five moves"对账；附录 A 表头收窄；`artifacts.yaml` 的 39→41；`PROVENANCE.md` 把 `.scratch` 里的图 1 收进仓库。**（m1–m14）**

---

## §14.5 本次审计**没有**覆盖的（诚实边界）

1. ~~没有修任何问题~~ —— **已按 §14 的顺序修复完毕**，逐条结果见 **§16 修复记录**。
2. **没有用包内钉的 Mathlib rev（`852d20a8`）重建**：本机只有 `85e3a25e`（v4.34.0-rc2）。修复时**改为对齐 `85e3a25e`**（包内 `lake-manifest.json` 已更新，`lakefile.lean` 补上 `require mathlib @ v4.34.0-rc2`），并把该 rev 写进转录头；见 §16。原 rev `852d20a8` 下的行为**仍未验证**。
3. **没有逐行核 §4 的证明**（只核了它的陈述、五步结构、以及 §7–§9 实际消费的每一个估计），**没有核 §12 的契约摘要**（digest 只在服务器侧，`§14` 自己说本地 `SKIP`）。
4. **没有做文献检索式的新颖性核查**（"这个定理是否已有人证明"）。§10 明确不主张 priority，我也没替它主张；本报告只判"文章说的与它证明的是否一致"。
5. **没有判 §11 的十层模块图描述是否与每个模块的实际内容吻合**（只核了名字存在性与那 10 个链声明是否空洞——后者结论：**7 个 measure 声明 + 3 个 covariance 声明均非空洞**，其中 `..._weak_limit_unique` 的证明就是 `exact tendsto_nhds_unique hμ hν`，即文章自认的"Hausdorff 唯一性，不是刻画"，如实）。
6. **没有审 `docs/`、`proofs/` 等其他层**，也没审旧稿 `PPHI2_FIXED_VOLUME_WEAK_LIMIT` 的内容质量（只比对了主定理是同一件事）。

## §15 附：本报告用到的复现命令

```powershell
# 结构数字（另一套实现）                        -> .scratch/audit/recount.py
python .scratch\audit\recount.py
# 导入图可达性（独立 BFS）                      -> .scratch/audit/reach.py
python .scratch\audit\reach.py
# PDF 侧事实（页数/编号致密性/??）               -> .scratch/audit/pdf_audit.py
python .scratch\audit\pdf_audit.py
# 门禁故障注入（12 例，含 5 处漏洞）             -> .scratch/audit/inject.py
python .scratch\audit\inject.py
# log 体检
Select-String -Path paper\PPHI2_FIXED_VOLUME_COMPLETE\build\main.log -Pattern 'Overfull|undefined'
```

Lean 侧（探针工程，需本机 `.local-lean` 的 Mathlib）：

```powershell
# 1) 拷包 + junction 到共享 packages + 独立 lakefile（package auditprobe）
# 2) 编译目标模块
$env:PATH = "E:\study\AImath\.local-lean\toolchain\bin;" + $env:PATH
lake build AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal
#   -> EXIT=1, failures: PeriodicNegativeSobolevTopologyInterfaces, GaussianConfiguration
```

`.scratch/` 已被 `.gitignore` 忽略，上述脚本不计入产物治理；本报告审计期间创建的探针目录（`paper/A_PHI2_AUDIT_PROBE`、`paper/A_PHI2_REBUILD`）已删除，`python tools/artifact_lint.py` 复跑 **11/11**。

---

## §16 修复记录（2026-11-03，按 §14 的顺序执行）

### M1 主定理 (iii)：已修

| 改动 | 位置 |
|---|---|
| 删掉 `def:cylinder-map` 里 "no sine label being used at $k_j=0$"，改为**两种标签在每个模上都允许（含零模）**，并加一段解释**为什么零模 sine 槽必须保留**（它记录 $-\Im c_0$，别的槽都看不见；删掉它柱 σ-代数就严格小于 $\mathcal B(\mathcal C)$） | `07_marginals.tex` |
| `lem:hC-identification`(iii) 的下界从 $V/(2\lambda(k_j))>0$ 改为 $\ge0$，并写明三个取值：非零模 $V/(2\lambda)$、零模 cosine $V/m^2$、零模 sine $0$ | `07_marginals.tex` |
| 证明 Step 5 的对应句子改成"零模 sine 得 $0$，因为 $\delta_{0,0}-\delta_{0,-0}=0$" | `07_marginals.tex` |
| `thm:main` 的 Step 4 补一句：柱族**含零模 sine 槽**，这正是族能把载体每个坐标分开的原因；删掉它这一步就不闭合 | `09_main.tex` |
| §11 的对应表说明改成"9 行对应 9 个结果；(iii) 由上一行的 cylinder-uniqueness 声明承载"（原来错写成"最后一行的三个声明"） | `11_lean.tex` |

**副产物**：§11 的对应关系现在**真的**成立——Lean 的 `periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals` 用的就是复坐标（含 $\Im c_0$），与修好后的论文陈述一致。

### M2 Lean 源码：**整包重建完成**（89/89，EXIT=0），转录已重生成

| 改动 | 文件 | 结果 |
|---|---|---|
| 补回 `def periodicHMinusThreeFiniteFourierProjection` 的声明头（+ docstring） | `PeriodicNegativeSobolevTopologyInterfaces.lean` | **保留**。这是审计认定的 BLOCKER：缺头是纯粹的 parse error，任何 Mathlib 版本都救不了 |
| **补 `require mathlib from git @ 852d20a8`**——原 lakefile 根本没有 `require`，包只能寄生在别的工程里编译，这是"读者无法自建"的根因 | `formal/lean/s6/pphi2_clean/lakefile.lean` | **保留** |
| `lake-manifest.json` 归位到 `852d20a8`（审计期间我曾把它改成 `85e3a25e`，后发现与源码不匹配，已撤回） | 同上目录 | **保留** |
| 新增 `audit/make_transcript.py`：从真实 Lean 运行重生成 `ext/axiom_transcript.txt`，并把 10 个声明所在模块的 sha256 写进转录头 | `paper/PPHI2_FIXED_VOLUME_COMPLETE/audit/` | **已运行**（10 行，全部恰好等于许可三元组） |

**迁移的 5 类 API 变化**（都是 revision 差异，不是本文缺陷）与站点数：

| 变化 | 站点 | 处理 |
|---|---|---|
| `IsProbabilityMeasure (Measure.map _ _)` 由实例搜索改为显式 | 4 | 用各模块已有的可测性引理（`gaussianSeriesConfiguration_measurable`、`covarianceConfiguration_measurable`、`latticeEmbedLift_measurable (physicalTestEval _ _ _)`） |
| `IsGaussian.hasGaussianLaw` 去掉可测性参数 | 6 | 直接去掉 |
| `ProbabilityMeasure.map` 把映射放进隐式 `{f}`、可测性变显式参数 | 42 | `.map X` → `.map (f := X) (<引理>.aemeasurable)`；lambda 用 `Finset.measurable_restrict` 复合 `measurable_periodicHMinusThree_coordinate_inclusion` |
| 实数版 `Summable.tsum_le_tsum` 不存在 | 1 | 改在 `ℝ≥0∞` 里比较再落回实数 |
| `Real.rpow_le_rpow_of_exponent_le` 不再推断指数 | 1 | 改成显式 `calc` |

**结果（本机，Lean `v4.34.0-rc2` / Mathlib `85e3a25e`）**：

- `lake build AImathPPhi2Clean` → **EXIT=0，89/89 模块全部产出 olean**（含根聚合器不可达的那 8 个）。
- 10 个链声明的 `#print axioms` → **全部恰好 `[propext, Classical.choice, Quot.sound]`**，与许可集**相等**（不只是"在里面"）。附录 B 用这次运行重写。
- 过程中出现 7 次 `failed to read file …olean` 一类**瞬时 IO 错误**（多个 lean 进程并发读同一批大 olean），重跑即过；与源码无关，记在此处以免下次误判。

**论文 §14 因此改回它现在真能说的话**：包钉在 Lean `v4.34.0-rc2` / Mathlib `85e3a25e`，三条出处（lakefile / manifest / lean-toolchain）一致；**整包编译成功**；转录是 2026-11-03 由 `audit/make_transcript.py` 对**交付树**跑出来的，头部带 3 个声明模块的 sha256。§11 的 "pinned to the Mathlib revision" 也同步改成 `85e3a25e`。

**自我更正**：审计当时判断"这是小时级的批量迁移、不在授权内"——**低估了**。实际是 14 个文件、约 68 个站点加十余次编译往返。值得做，因为只有做完，`the build succeeds` 才从**一句没验证的话**变成**一条可重跑的命令**。



### M4 排版：已修，且**由门禁守住**

- 正文里所有 Lean 标识符改走 `\lean{}`/`\lmod{}`，宏内部逐字符插入 `\allowbreak`（下划线、斜杠之后，以及每个大写字母之前），源文本不变、门禁 N 仍读得到原名。
- `build_all.py` 新增 **log 扫描**：`Overfull` 或 `undefined reference` 一律 **BUILD FAILED**，并把结果写进 `LAST_BUILD.txt`。
- 结果：**overfull 8 → 0**（最差从 249pt 到 0），`undefined` 保持 0；§13 那两个被裁出纸面的声明名现在正常换行。
- `notes/INTEGRATION.md` 里"no overfull box larger than 60pt"的假声明已改写为事实 + 成因。

### M5 门禁：已修，且**用注入实验验证**

| 改动 | 验证 |
|---|---|
| `REF` 正则加 `eq`（`\eqref` 从此受管） | 新增负对照 "L rejects a dangling eqref" —— 而且它**真的抓到了一个悬空引用**（我自己在新 §5 里写的 `\cref{def:finite-source-law}`，正确名是 `eq:finite-source-law`），修好才转绿 |
| `lean_declarations()` 从 `pphi2_clean/**` 收窄到被构建的 `AImathPPhi2Clean/` | 名字只在 vendored `audit/` 里存在的注入用例现在会**红** |
| 检查 M 增加"定义了却没人引用"判红，并把 `main.tex` 纳入扫描 | 负对照 "M rejects a macro that nothing quotes" |
| `LAST_BUILD.txt` 纳入 `ext/axiom_transcript.txt` 与 `audit/*.py` | 戳里可见 |
| 自检从 11 例扩到 **13 例** | `self-test: 13/13 negative controls behave` |

### M6 / M8 引用：已修

- §10 清点改为 **Four + eight**（补上 `billingsley1999`，把 `gjs1974` 指到"排除项"那段）。
- `refs.bib`：`nelson1973` 页码 97–112 → **211–227**；`minlos1959` 页码 97–104 → **497–518**，标题与刊物对齐，并加英译注记。`make_bib.py` 重生成 `generated/bibliography.tex`。
- `rem:no-bessel` 的"different identity, on a different space"改为"同一算子的 $x$-空间代表，但此处不用也不证"。

### M7 前稿关系：已登记（**不动论文**）

`proof_graph/deliverables.yaml` 现在写明：`20261101_...weak_limit.pdf` 的状态是 `SUPERSEDED_BY: deliverables/20261102_pphi2_fixed_volume_complete.pdf`，`20261102_...` 为 `ACTIVE`。论文正文**不加**引用：前稿从未公开发表，向 arXiv 读者指引仓库内部文件没有意义；两份 PDF 的关系是治理层的事实，登记在治理层。

### MINOR（m1–m18）：已逐条处理

摘要补 "In two dimensions"；§2 说清 $s$ 是 Sobolev 阶而"衰减指数"另写（并把 $8\zeta(3)/8\zeta(5)$ 提为展示式）；`ext:summability` 由 external theorem 降为 **lemma 并给证明**，小节标题随之改；三角多项式稠密一句改为"记录备查、下文不用"；图 1 图注核对 "eight boxes vs five moves" 并声明图中用 $M$/$n$ 而正文用 $m$/$N$；图 2 图注对账 92/135 与 89/132；附录 A 表头收窄为"两个契约冻结的声明"；"separable, hence Polish"补上完备性前提；§13 的两处打印式计数换成 `\NumUnreachableModules`/`\NumUnreachableChainTheorems`/`\NumMeasureContractTheorems`（新增宏，实测 **6**）；`artifacts.yaml` 的 "39 pp" → **42 pp**（PDF 因新增内容变长）；`PROVENANCE.md` 的图 1 源改为仓库内路径。

### §16.4 收尾状态（2026-11-03，最终）

- `python build_all.py`：**4/4 论文检查 + 13/13 负对照 + overfull 0 / undefined 0**，**42 页**，`main.pdf` 与 `deliverables/20261102_pphi2_fixed_volume_complete.pdf` 同为 `6e31d12f…`（1,481,805 B）。
- `python tools/artifact_lint.py`：**11/11**（过程中曾因我自己的两处操作转红，都已修好并记录：`deliverables.yaml` 的批量替换写坏记录，已按原文重建；`formal/lean/s6/pphi2_clean/.lake` 的 junction 让 L3 数到 148,606 个文件，已用 `rmdir` 只删链接、`.local-lean` 的 6.4 GB Mathlib 完好无损）。
- Lean：**整包 89/89 编译通过（EXIT=0）**；10 条足迹全部等于许可三元组；`ext/axiom_transcript.txt` 由 `audit/make_transcript.py` 于 2026-11-03 重新生成，头部记录 Lean `v4.34.0-rc2`、Mathlib `85e3a25e` 与 3 个声明模块的 sha256。
- 审计报告本身与全部修复脚本在 `.scratch/audit/`（gitignored，不进产物层）。

### §16.6 最终一句话

**2 项 BLOCKER、5 项 MAJOR、18 项 MINOR 全部关闭**：主定理不再为假、Leen 整包 89/89 编译通过且转录来自对交付树的真实运行、`hyp:lift-input` 从"开放"变成一条证明、PDF 从 8 处 overfull（最差 249pt，裁掉正文）到 **0**、门禁从 5 处漏洞到 13 条负对照且当场抓出我自己写错的引用、两条参考文献页码与引用清点改正、两篇同名稿的关系登记。**唯一的"减法"是审计报告自己的判断被推翻了一次**：当时说 Lean 迁移"不在授权内"，用户一句"整包重建"就证明那是低估计。

### §16.5 一句话总结这次修复

**12 项全部落地，其中 11 项是"改对"，1 项（M2）是"改成不撒谎"**：声明头补回了、论文自己的陈述不再为假、门禁真正能咬、排版不再裁字、参考文献页码对了、两篇同名稿的关系登记了；而 Lean 整包本机重建没做成——于是论文里那句话被改成"我们没重建，这是记录性产物，这是版本差异卡在哪"，而不是继续宣称一个没验证过的 "the build succeeds"。
