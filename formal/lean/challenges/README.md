# 陈述-挑战协议（statement-challenge）

> **移植来源**：OpenAI `openai/math` 的 `lean/ComparatorChallenges/` —— 每个结果一对文件：
> `<Name>.lean`（冻结陈述，证明体是 `by sorry`）+ `<Name>.json`（解模块、定理名、公理白名单），
> 由 `comparator` 校验「陈述相等 + 公理 ⊆ 白名单」。
>
> **本项目的适配**：本机**没有** `comparator` / `nanoda`，也不引入。改用两条本机可跑的等价机制
> （见下 §2），并诚实标出弱化之处。

## 1. 文件

| 文件 | 作用 |
|---|---|
| `_registry.yaml` | **机器可读的『节点 → Lean 模块/定理』注册表**。这是本项目原本缺的那一环：`theory_graph.yaml` 的 `evidence[].ref` 是自由文本，从散文推不出全限定名 |
| `<NODE>.check.lean` | **生成物**（勿手改）：`import` 解模块 + 每个定理一条 `#check @…` 和一条 `#print axioms …` |
| `<NODE>.hashes.json` | **陈述冻结**：每个定理的 `#check` 精化签名哈希 |

生成物由 `--init` 重写；注册表由人维护。

## 2. 两条机制（各自的牙齿）

1. **公理足迹**（与 Comparator 同义）：`#print axioms <thm>` 的结果必须 ⊆
   `[propext, Classical.choice, Quot.sound]`。`sorryAx` 与任何额外公理都会被抓到。
2. **陈述冻结**：`#check @<thm>` 打印的是 Lean **精化后**的完整类型（含全部 typeclass binder），
   取其规范化文本的 sha256。陈述被加强/削弱/换参数 ⇒ 哈希变 ⇒ **持续红**，直到有人显式
   `--update-hashes --why "<理由>"` 接受它。

**诚实边界（不夸大）**：机制 2 冻结的是**签名**，**不是**与一份独立转写的挑战陈述的
「定义相等」检验。真正的 Comparator 做的是后者。要补上这一点需要引入 `comparator`
（或手写第二份陈述 + 粘连 `example`），本项目暂时不做，理由是本机无可用的该二进制。

## 3. 命令

```powershell
python tools/lean_challenge.py --init            # 由注册表生成/更新 *.check.lean
python tools/lean_challenge.py --run             # 跑 Lean：核公理足迹 + 陈述冻结（需本机 Lean 或服务器）
python tools/lean_challenge.py --run --node S3_GREEN_DISTRIBUTION
python tools/lean_challenge.py --update-hashes --why "……"   # 显式接受陈述变更
python tools/lean_challenge.py --self-test       # 负对照：证明检查器不是空转
python verify/lean_challenge_probe.py            # 结构自洽（不跑 Lean，已并入 run_checks）
```

`--run` 用**本机** Lean：`.local-lean/toolchain/bin/lake.exe` + 工程
`.local-lean/S6Isserlis`（toolchain `v4.34.0-rc2`）。找不到时报告 `SKIP`，
**不静默通过**（对照本项目的「基础设施失败 ≠ 数学前沿」纪律）。

## 4. 与其它层的关系

- **状态仍只在** `proof_graph/theory_graph.yaml`。本协议**不写状态**，只提供「某节点确实
  形式化到了它声称的那条陈述、且没有偷用公理」的**判据**。
- 注册表只登记 `lean_provenance: self` 的条目；`imported:` 的上游形式化另记 `imported_nodes`，
  不参与本地检查（上游的陈述由上游负责）。
- 已知的机器收益：`OS1.lean` 里有 3 条 `axiom` 声明，历来靠人工断言「是死声明、未被任何定理使用」。
  公理足迹检查把这句话变成**可复算**的 —— 见 `OS1_FREE_SCALAR` 的注册条目。
