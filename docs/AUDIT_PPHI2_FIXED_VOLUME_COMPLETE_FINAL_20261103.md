# 独立审计（最终版）：`PPHI2_FIXED_VOLUME_COMPLETE`（2026-11-03，第二轮）

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-03 · 判据：`proof_graph/ARTIFACT_SPEC.md` §3（L11）
> **这份报告是什么**：对**最终版**（43 页、Lean 整包 89/89 可编）的一次**新一轮**独立审计。它不是修复记录——修复过程在 `docs/reports/AUDIT_PPHI2_FIXED_VOLUME_COMPLETE_20261103.md`；本报告只回答一个问题：**这一版能不能投，以及还剩什么。**
> **独立性怎么保证**：4 个评审 agent 都是新起的，prompt 里**明令禁止读 `docs/reports/` 与 `notes/`**，只看文章与 Lean 源；机械数字用**第三套实现**重算（不是修复时那套）；Lean 侧事实来自我自己重跑的真实编译，不是转录里的自述。
> **一句话结论**：**可以投**。上一轮 2 BLOCKER + 5 MAJOR 全部关闭并经复核；本轮新发现 4 项 MAJOR（其中 3 项是我这一轮改出来的、1 项是上一轮遗留），**当场全部修掉**，其余 12 项 MINOR 也逐条处理。修完后门禁全绿、重新编译、重新生成转录。

---

## §0 结论

最终版的**数学**站得住：柱族是确定类，`thm:cylinder-uniqueness` 与 `thm:main`(iii) 按字面成立，主证明五步的每个引理假设都被满足，`lem:hC-identification`(iii) 的四个对角值逐项重算无误，零模 sine 的边际是退化的 $\delta_0$ 而论文写的 $0$ 正确。

最终版的**Part II** 经本轮修整后也站得住，但这一轮它是最脆弱的部分：4 个 MAJOR 里有 3 个在这里，全是我在把"不能编"改成"能编"的过程中产生的——把证据说强了（声称文学目标构建）、把两处对应关系写错了（一行引错声明、一处漏报第二个弱化行）、把 `SKIP` 的原因写反了（说记录值在服务器，其实在仓库里）。**这正是"修证据时最容易顺手把话说满"的典型位置**，值得记一笔。

---

## §1 机械事实（本报告现算）

| 量 | 值 | 来源 |
|---|---|---|
| 页数 / 字节 / sha256 | **43** / 1,489,052 / `7fe1f947…` | `main.pdf` |
| `??`（未解析引用） | **0** | PDF 文本扫描 |
| overfull / undefined | **0 / 0** | 构建 log 扫描 |
| 编号结果（§2–§9） | **48**，逐节致密（10/7/5/10/6/5/2/3） | PDF 渲染计数（第三套脚本） |
| 其中定理类 | 24（Theorem 10 + Lemma 11 + Prop 2 + Cor 1） | 同上 |
| 定义 / 注 / 假设 / 外部定理 | 9 / 10 / 1 / 4 | 同上 |
| `\label` | **119**，无重复 | 源码 |
| 引用命令 | **499**（`\cref` 345、`\Cref` 23、`\eqref` 129、`\ref` 2），悬空 **0** | 源码 |
| `\cite` / 不同键 | 17 / **12**，无未引用、无未定义 | 源码 + `refs.bib` |
| Lean 模块 / 行 | **89** / **13,505** | 构建时现算 |
| `sorry` / 项目公理 | **0 / 0**（我另写脚本复核） | 同上 |
| 契约 / 许可公理 / 链声明 | 14 / 3 / 10 | `_registry.yaml` |
| 不可达模块 / 其中在链上的声明 | **8** / **6 of 7** | 独立 BFS 复核 |

**Lean（我自己跑的）**

- `lake build AImathPPhi2Clean` → **EXIT=0**，`lib/lean/AImathPPhi2Clean/` 下 **89/89** olean 齐备（含根聚合器不可达的那 8 个）。
- 10 个链声明 `#print axioms` → **全部恰为 `[propext, Classical.choice, Quot.sound]`**（与许可集**相等**）。
- 转录头 3 个声明模块的 sha256 → **逐个 MATCH** 当前源文件（"转录锁定在交付树上"的机械证明）。
- 工具链 `v4.34.0-rc2`；`lake-manifest.json` 钉 commit `85e3a25e`（`lakefile.lean` 钉的是 `v4.34.0-rc2` 标签）。

**门禁**：`build_all.py` → 4/4 + 13/13 负对照 + overfull 0 / undefined 0；`artifact_lint.py` → **11/11**。

---

## §2 推导复核：4 个盲评审

### 2.1 柱族 → 确定性 → 唯一性（§7 / §8 / §9）

**结论：链闭合，无 blocker、无 major。** 评审自己补出了完整证明：柱族的坐标含 $\{\Re c_k,-\Im c_k:k\in\Z^2\}$，故 $\sigma(\Pi_F)=\mathcal B(\mathcal C)$；柱集是 π-系，Dynkin 给唯一性。**族之所以是确定类，恰恰因为两种标签在每个模上都允许**——评审给出反例：若每模只留一种标签，则 $\delta_0$ 与 $\delta_{ie_0}$ 的边际完全相同而测度不同，`thm:cylinder-uniqueness` 为假。零模四类对角值逐项重算（$V/(2\lambda)$、$V/(2\lambda)$、$V/m^2$、$0$）与论文一致，零模 sine 的边际确为 $\delta_0$。

评审还独立核对了**Lean 声明的强度**：`periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals` 用"每个模一个复坐标"的柱映射，与论文的"每模两种标签"通过 $2m$ 槽 ↔ $m$ 复坐标互推，**同一强度**；若论文按旧定义收窄，Lean 会严格更强。

提出的 3 项 MINOR **已全部修**：§7 的 Green 配对改用 $\mathcal Q_N,\mathcal Q$（与 §4 一致，共 14 处）；§8 的 σ-代数步补成两行包含证明 + $\delta_0/\delta_{ie_0}$ 见证；§9 Step 1 补引"$\mu_N$ 是 $\mathcal C$ 上的 Borel 概率测度"。

### 2.2 提升引理与边界（§5 / §3 / §1 / §9 / §10 / §13）

**结论：数学正确，诚实层有 2 处真实缺陷（已修）。**

- `lem:lift-representative` **三部分都真、都证了**：值域界 $\sum_p|(L_N\omega)(p)|^2\le a^4\|\omega\|_1^2(1+8\zeta(5))$ 的算术经 sympy 与直接求和双重核对（$8\zeta(5)=8.295422\ldots$）；可测性需要的两个部件（$\pi_k$ 连续、$\sigma(\pi_k)=\mathcal B(\mathcal C)$）论文都有，且**第二个部件靠的是 §5 已证的可分性**——这条重接线是真的闭合了旧缺口。
- 但第三项"坐标恒等式"原本是 `def:carrier-hminus3` 的逐字重复（**同义反复**），而且其文字解释"加权坐标是原始的那些"**差了 $\sqrt{w_3(k)}$ 的因子**。**已修**：引理现在把条目公式显式写出来（带 $\sqrt{w_3}$ 与 $a^2$ 的求和），并点明这是存储表示、指向 `rem:two-families` 的字典。
- `rem:lift-development` 原本说发展里的提升"由无穷级数定义"——**错**：Lean 里它是逐坐标定义的（`PeriodicComplexFourierLift.lean`），无穷只出现在 $\ell^2$ 完备化的 side condition 里；而且它说"输入只谈可测性、不谈例外集大小"——**半错**：那个输入是合取，第二个合取项正是"与原始加权提升几乎处处相等"，谈的就是零测集。**已整段重写**，并补上第三条：有限源路线上 Lean 自己**无条件**证了两个推前相等，所以这件事对本文不构成缺口。
- `§13` 结尾残留 "the unproved bridge to the physical lattice law"——**这是上一轮改写漏掉的一句**，与 §13 自己的 Item 3、§3、§9、§10 全都矛盾。**已删并改写**。
- `lem:summability` 的门限（衰减指数 $r>2$，即 $2s>d$）与 $8\zeta(3)=9.616455$、$8\zeta(5)=8.295422$ **正确**；§2 已把它从 external 降为 lemma，但 §2 开头仍说"两个背景事实是借来的"——**已改成"一个借来、一个自证"**。

### 2.3 Part II 与可编译的 Lean 树

**结论：结构脊柱是真的，但 4 处 MAJOR。**

评审自己重算了 import 闭包（得到恰好 8 个不可达模块、名字全对）、"6 of 7"（对）、转录里 3 个 sha256（逐字节对）、以及 18 个结构数字（**全部与文件一致**）。但：

1. **`§13:41-43` + 附录 B 的表头声称"这就是附录 B 记录的那次库目标构建"**，而转录当时记录的是**三个模块**的构建。这是本轮最尖锐的一条——**证据说的比做过的多**。
   **修法（不是改口，是补齐）**：我确实跑过 `lake build AImathPPhi2Clean`（EXIT=0，89/89）。现在转录头**两条命令都记**（库目标 + 三个声明模块），附录 B 表头据此改写。**证据追上声明，而不是把声明退回。**
2. **`§11` 的"唯一被标记的更弱行"是错的**：`thm:cylinder-borel` 对应声明带一个 Polish 性输入，而 Part I 的无条件——**是第二处弱化**。已改为"两处限定"，并说明同一模块用 `periodicHMinusThreeCompletion_separable` 把它兑现。
3. **`§11` 标记行引错了声明**：`..._weak_tendsto_of_periodic_fourier` 的结论是 `∃ T, …targetCoordinateProbabilityMeasure T`（收敛到*某个*高斯因子），而 `thm:finite-family` 说的是收敛到**特定**的 $\Lambda_F$。**已换成 `..._of_periodic_fourier_canonical`**（结论恰为 `periodicResolventTargetProbabilityMeasure`），并把"消费协方差识别"这个真实限定写清楚。
4. **`§12` 把 `SKIP` 的原因写反**：记录值就在本仓库（`formal/lean/challenges/*.hashes.json`），不在服务器。**已改写**为"runner 在旗标处就拒绝，值在仓库里，本论文不带任何比较它们的检查"。

修完后 Part II 的五项边界（可达性、空洞包装、发展里的提升、维度、绿构建证明了什么）**逐条与源码吻合**。

### 2.4 过度声称 / 欠声称 / 内部一致性

**结论：Part I 诚实，Part II 的诚实层最脆弱。**

评审列了 11 条，其中 3 条已在本轮修掉（见 §2.3 的 1、2、4 与下面的 5、6）。**已修的**：

- **§10 开头把 `thm:main` 说成"证明了紧性、边际极限、整序列收敛"**——`thm:main` 只给存在性、$\mu_{\mathrm{free}}$ 的边际、刻画；紧性是 `thm:tightness`、边际极限是 `thm:finite-family`。**已改成"其假设在同一条链上被证明而非假设"，并把三件事归到各自的定理**。
- **§9 把协方差算子称作 "an honest gap"**，而 §10 说柱确定已经给出它。**已改成"构造 vs 推论"的区分**：说"它是那个测度"需要载体上的算子（没建）；说"是哪个测度"只需 `thm:cylinder-uniqueness`（已证）。
- **图 1（spine）**：正文说"八个盒子"，实际列了七项（第一个盒子在列表外）；图内**烧进 PNG** 的脚注仍写着"物理格点全载体提升有一个单独的具名输入、此处不用"——与 §13 Item 3 和 `lem:lift-representative` 直接冲突。**已改图注**：数清"第一个盒子 + 其后七个"；并**显式披露**图内脚注是发展侧实现选择的记录、已被 `lem:lift-representative` 与 `rem:lift-development` 取代；同时改正符号说明（$M\to m$，而图里的 $n$ 就是正文的网孔指标 $n$，不是 $N$）。
- **图 2（atlas）**：图注说 92−89=3 是"包裹包的外围发展"，而图自己的图例说那 3 个是"detached from the core"的卫星，且外围目录其实是 43 个模块。**已改图注**，说清卫星、说清 43 个模块没画进来。
- **摘要**"Part II 是同一陈述的形式化"与 §11/§13 的五处分歧矛盾。**已改成"同一批结论的发展，并说明哪一层被机器检验"**（`main.tex` 的 How-to-read 同步改）。
- **"first moment" 一词用来指二阶矩**：§6/§9/§10 与摘要共 6 处。**已统一改成 "second moment of the norm"**，`§6` 的小标题改成 "The per-mode second moment"。
- **`§12` 里手打的 "the ten theorems"** 与"结构数字一律用宏"冲突。**已换成 `\NumChainTheorems`**。

---

## §3 我自己抽检的部分

1. **算术**：$8\zeta(3)=9.616455$、$8\zeta(5)=8.295422$、$1+8\zeta(5)=9.295422$（mpmath，20 位）；零模四类对角值与 `eq:entries` 逐项对上（见 §2.1 评审的独立复算，我另算一遍一致）。
2. **转录锁定**：3 个声明模块的 sha256 与转录头逐字节一致——**这条是机械的，不依赖任何人读代码**。
3. **`sorry`/公理**：另写脚本（去注释 + 正则）重数，89 模块、0 sorry、0 项目公理，与构建时的宏一致。
4. **契约 runner 语义**：读 `tools/lean_challenge.py:112-114`，确认 `remote_only` 在**任何计算之前**就返回 `SKIP`——这正是 §12 新措辞的依据。
5. **Lean 声明强度**：`..._ext_of_indexed_cylinder_marginals` 的类型我亲自读过（复坐标柱族、无额外假设），与评审结论一致；`..._of_periodic_fourier_canonical` 的结论我亲自读过（收敛到 `periodicResolventTargetProbabilityMeasure`），确认换名是对的。

---

## §4 本轮发现与处置

| # | 严重度 | 位置 | 问题 | 处置 |
|---|---|---|---|---|
| 1 | **MAJOR** | §13:41-43、附录 B 表头 | 声称附录 B 记录的是库目标构建，实际只记了三个模块 | **补齐证据**：转录头现在记录库目标构建（EXIT=0、89 模块）+ 三个声明模块 |
| 2 | **MAJOR** | §11:156-166 | "唯一更弱的行"是错的：`thm:cylinder-borel` 对应声明带 Polish 输入 | 改为"两处限定"，并说明该输入由同模块的 `..._separable` 兑现 |
| 3 | **MAJOR** | §11 表 | `thm:finite-family` 行引错声明（结论是 `∃ T` 而非特定 $\Lambda_F$） | 换成 `..._of_periodic_fourier_canonical` |
| 4 | **MAJOR** | §12:60-64 | `SKIP` 的原因写成"记录值在服务器"，实际在仓库 | 改写：旗标处即拒绝；值在仓库；论文不做比较 |
| 5 | MINOR | §5 `rem:lift-development`、§13 Item 3 | 说发展里的提升"由无穷级数定义"（实为逐坐标）；说输入"不谈例外集大小"（合取项正是 a.e. 相等） | 两段重写，并补"有限源路线上 Lean 已无条件证两推前相等" |
| 6 | MINOR | §5 `lem:lift-representative` | 第三项同义反复，文字解释差 $\sqrt{w_3}$ | 写成显式条目公式并指向 `rem:two-families` |
| 7 | MINOR | §13:95-96 | "the unproved bridge to the physical lattice law" 残留（与自己的 Item 3 矛盾） | 删除并改写 |
| 8 | MINOR | §13:79-80 | "covariance limit is available in dimension $d$" 与 §2 "no statement claimed in another dimension" 冲突 | 改为"registered for general $d$"，并加指回 `rem:dimension` |
| 9 | MINOR | §10:18-22 | 把紧性、边际极限记在 `thm:main` 名下 | 重新归属 |
| 10 | MINOR | §9:136-141 | 把协方差算子称作 "honest gap"，与 §10 矛盾 | 改成"构造 vs 推论" |
| 11 | MINOR | §7（14 处） | Green 配对写作 $Q_N/Q$，与 §4 保留给高斯算子的 $Q$ 撞名 | 统一改 $\mathcal Q_N/\mathcal Q$ |
| 12 | MINOR | §8:53-57 | σ-代数步只有一句话，其载荷条件在别节 | 补两行包含证明 + $\delta_0/\delta_{ie_0}$ 见证 |
| 13 | MINOR | §9 Step 1 | 用 Prokhorov 未引"$\mu_N$ 是概率测度" | 补引 `eq:finite-source-law` + `lem:lift-representative` |
| 14 | MINOR | 图 1 图注 | "八个盒子"列了七项；图内脚注与 §13 矛盾 | 改图注：数清 + 披露图内脚注已被取代 + 改正符号说明 |
| 15 | MINOR | 图 2 图注 | 把 3 个卫星说成"外围发展"，且漏说 43 个模块未画 | 改写 |
| 16 | MINOR | 摘要、`main.tex` | "same statement" 与 §11/§13 的分歧矛盾 | 改 "same conclusions"，加指向 §13 |
| 17 | MINOR | §1/§6/§9/§10 | "first moment" 实指二阶矩 | 统一为 "second moment of the norm" |
| 18 | MINOR | §2:23-25 | 仍说"两个背景事实是借来的"（其一已自证） | 改为"一个借来、一个自证" |
| 19 | MINOR | §12:102-104 | 负对照那行的描述（"intended minus one"）不准确 | 改为"带注入公理、且不含许可三元组中的任何一个" |
| 20 | MINOR | §11:33-35 | "does not report, does not count" 同句自相矛盾 | 改 "does not take as its subject" |

**未处置、且我认为应当保留的**（写在这里以免被当成遗漏）：

- **图 1 的 PNG 里烧进的那行脚注**改不掉——它是位图。图注已披露它过时且被哪条引理取代。**若要彻底消除，得重新生成该图**；在我能拿到的源里没有生成脚本，硬改会把"copied, not redrawn"的 provenance 弄坏。
- **`..._of_polish` 的无条件化**：把 Polish 输入换成可分性是一行改写，但那是改 Lean 源、要重编 89 个模块；论文已如实说明该输入如何被兑现，所以**不改**。
- **仓库里没有 `.lake` 构建产物**（`.gitignore` 排除）。构建事实由转录头记录（命令 + EXIT=0 + 89 模块），不是由二进制产物记录。

---

## §5 与上一轮审计的对照

| 上一轮 | 内容 | 本轮 |
|---|---|---|
| M1 BLOCKER | 主定理 (iii) 按字面为假 | **关闭**：评审独立证明链闭合，并给出反例说明"两种标签"不是装饰 |
| M2 BLOCKER | 仓库内 Lean 包编不过 | **关闭**：补 `def` 头、补 `require`、manifest/toolchain 对齐、14 文件 ~68 处 API 迁移 → **89/89 EXIT=0**，转录重生成 |
| M3 MAJOR | "开放输入"实为可证 | **关闭**：`hyp:lift-input` → `lem:lift-representative`（附证明）+ `rem:lift-development` |
| M4 MAJOR | 8 处 overfull 裁字 | **关闭**：0 overfull；构建对 overfull/undefined 直接失败 |
| M5 MAJOR | 门禁看不见 `\eqref` | **关闭**：自检 13 例；当场抓出我自己写的一个悬空 `\cref` |
| M6 MAJOR | §10 引用清点 3+7≠12 | **关闭**：Four + eight，评审逐条核过 |
| M7 MAJOR | 与前稿无关系登记 | **关闭**：`deliverables.yaml` 记 `SUPERSEDED_BY` |
| M8 MAJOR | 两条参考文献页码错 | **关闭**：`nelson1973` 211–227、`minlos1959` 497–518 |
| m1–m18 | MINOR | **全部关闭** |

**本轮新出现 4 MAJOR，全部处置完毕。** 其中 3 条是我在修 M2/M3 时引入的——教训写在 §0：**修证据的时候，最容易顺手把证据说强一格**。

---

## §6 本次审计**没有**覆盖的

1. **新颖性**：不判"这个定理是否已被证明"。§10 不主张 priority，本报告也不替它主张。
2. **§4 的每个估计**：只核了 §7–§9 实际消费的那些（其余由上一轮的分节评审覆盖）。
3. **§12 的契约摘要值本身**：digest 在仓库里存在，但本论文不带任何比较它们的检查；我没有独立重算那两个 digest。
4. **跨机器/跨工具链**：89/89 只在 Lean `v4.34.0-rc2` + Mathlib `85e3a25e` 上成立。
5. **`docs/`、`proofs/` 等其他层**。

---

## §7 复现命令

```powershell
# 文章：数字现算 → 台账/转录 → 负对照 → 四道门禁 → 编译 → log 扫描
cd paper\PPHI2_FIXED_VOLUME_COMPLETE
python build_all.py

# 治理
python tools\artifact_lint.py

# Lean：整包
cd formal\lean\s6\pphi2_clean
lake build AImathPPhi2Clean            # -> 89 模块，EXIT=0

# 转录重生成（对交付树跑一次真实 #print axioms）
cd ..\..\..
python paper\PPHI2_FIXED_VOLUME_COMPLETE\audit\make_transcript.py `
  --package formal/lean/s6/pphi2_clean --toolchain v4.34.0-rc2
```

---

## §8 第三轮：外部评审又抓到一条假命题（2026-11-03 晚）

本报告 §1–§7 的结论是"可以投"。随后有一位**外部评审**逐页读了最终 PDF，抓到 **1 条数学表述仍然为假**、2 处编辑缺陷、1 处文献缺口。四条**全部核实为真并已修**，修完重新编译、重新过门禁、重新推送。

| # | 位置 | 问题 | 处置 |
|---|---|---|---|
| 1 | §7 `thm:finite-family` 证明末句 | 原文 **"Lemma 7.3(iii) says that the limit does not degenerate."** —— 与事实相反：`def:cylinder-map` 的零模 sine 槽极限律就是 $\delta_0$（退化），`thm:char-function` 自己也写着 "possibly degenerate"。**这是本论文第二次出现"某句断言与论文其他部分相反"的同类错误**，第一次是主定理 (iii) | 改写：明说协方差可以是退化的、点名 $\delta_0$ 那个槽、说明为什么无害（$\Lambda_F$ 仍是概率测度，Levy 定理不要求对 Lebesgue 绝对连续） |
| 2 | §2 开头 | "Two background **fact is** borrowed" —— 上一轮我把"两个借来的事实"改成"一个借来、一个自证"时**把句子改坏了** | 改为 "Two background facts are stated: one is borrowed … and the other is proved outright below" |
| 3 | 图 1 的 PNG | 位图里**烧死**的脚注仍写着"物理格点全载体提升有一个单独的具名输入、此处不用"——正是本文 `lem:lift-representative` 已证伪的话。上一轮我的处理是"在图注里披露它过时"，评审指出**这不叫修**：读者不该先看到图里错的信息、再靠图注学习它为什么失效 | **重画**：生成脚本在旧稿的 `tools/` 目录里找到了（发布仓库把旧稿归档在 `docs` 的 archive 子目录下），已 vendor 到本文的 `figures/generate_spine.py`，脚注改成 `sec:main` 真正画的那条边界（"极限由有限 Fourier 边际确定；载体上不构造协方差算子"），并把图里的 $M$ 改成正文的 $m$。`PROVENANCE.md` 记下这次重画与新哈希 |
| 4 | §10.3 文献 | 缺最接近的已发表相关工作：Cipriani & van Ginkel, *The discrete Gaussian free field on a compact manifold*, **SPA 130 (2020) 3943–3966**（随机图逼近紧流形，Voronoi 镶嵌，强 Sobolev 拓扑下依分布收敛）。评审的问题很准：*"不主张优先权"不等于"不需要比较"* | 增引并**逐轴比较**：模型（随机图 vs 固定物理体积的确定性周期格点 + massive 算子）、极限识别方式（认同为流形 GFF vs 只用有限傅里叶边际确定）、拓扑与收敛模式（强 Sobolev 依分布 vs 载体上整列弱收敛）、机器验证（本文 Part II 有，对比文献不涉及本文对它们的任何断言）。结论明确写出"本文增加了什么"，同时仍不主张优先权 |

**修后状态**：`build_all.py` → 4/4 + 13/13 + **overfull 0 / undefined 0**；PDF **44 页**，sha256 **`4ad27ed8…`**（byte-reproducible，两次编译一致）；交付物与 `deliverables.yaml` 已更新，`artifact_lint` **11/11**。

**一条值得记下的教训**：主定理 (iii) 与 `thm:finite-family` 末句是**同一类错误**——一句断言与它所在论文的其他部分相反。两轮审计都没抓到 (iii) 之外的第二处，是因为两轮都在看"审计报告列出的那几条"，而不是**逐句读证明**。第三轮之所以抓到，是因为外部评审**从头读**而不是读审计结论。这说明：**审计报告不能替代通读**，而"我上一轮修过这里"恰恰是最需要再读一遍的地方——第 2 条就是我自己上一轮的修改动作引入的。

**第五轮（同日晚，发布过程中暴露的）**：把 PDF 推到 GitHub 后再做"干净克隆 == 本地"的逐字节核对，发现**做不到**——Tectonic 把时间戳写进 PDF，同一份源码连编两次得到两个不同的文件，于是 `build/LAST_BUILD.txt`、仓库 `MANIFEST.sha256`、`deliverables.yaml` 三处记录的摘要永远不可能同时成立（每编一次就全废一次）。这不是发布问题，是**取证问题**：一个依赖墙钟的构建，它的产物摘要不可能是"源码的函数"。修法是 `build_all.py` 里钉 `SOURCE_DATE_EPOCH`（2026-11-03 UTC），现在同一棵树连编两次得到同一个 SHA-256（实测 `4ad27ed8…` 两次一致），§14 也把这条性质写进去了。**这个问题从头两轮审计到第三轮都没人发现，因为所有检查都只问"现在这份 PDF 对不对"，没问"这份 PDF 是不是能被重新算出来"。**

**发布**：文章与复现所需的一切已推到 <https://github.com/springoxn/pphi2-clean-finite-lattice>（public），五个提交（HEAD `18c191f`）；干净克隆上 `verify.py` **438 文件**通过、转录 **3 个模块摘要逐个匹配**、论文门禁 **4/4**，且**仓库里那份 PDF 与本地交付物逐字节相同**。仓库里那份 Lean 包原本是**未修复的 82 模块快照**（含缺声明头的那一版），现已同步为 89 模块、`lake build` 可过、Mathlib 钉在 `85e3a25e`。

