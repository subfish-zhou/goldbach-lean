# 九节点直接加权路线：结构评估

本记录为只读探索；未修改项目源码，未引入新的 Lean 声明。命令：

```sh
python3 /tmp/wu-structural/weighted_check.py
```

输出保存在 `/tmp/wu-structural/weighted-check.json`。脚本从当前 `WR2XiRationalCandidate.lean` 读取矩阵，用 `fractions.Fraction` 检查，并从当前源文件 import 图重算假设依赖变化，不对源码做任何编辑。

## 数学结论

现有有理矩阵 M 的全部 81 项严格正。九个行和分别为：

369/1000, 363/1000, 179/500, 89/250, 361/1000, 359/1000, 363/1000, 93/250, 199/500。

故最大行和为 199/500 < 1，谱半径小于 1。对任何非零向量 ℓ ≥ 0，规范对偶

w = (I − Mᵀ)⁻¹ ℓ = Σ(n ≥ 0) (Mᵀ)ⁿ ℓ

存在且全部九个分量严格正（第一阶项 Mᵀℓ 已全部严格正）。若 H ≥ 0 且 (I − M)H ≥ B，则

ℓᵀH = wᵀ(I − M)H ≥ wᵀB。

更一般的足够条件为 w ≥ 0、(I − Mᵀ)w ≤ ℓ。

此处正性及行和由有理脚本检查；Neumann 级数及对偶推导是数学论证，未声称已有新的 Lean 形式化。严格正性意味着：沿现有逐项矩阵界组合的路线，规范对偶仍用到每一行和每一列。它不自动消除任何解析矩阵项证书。这并不证明所有可能的稀疏、不等式对偶都不可能，而是排除“直接套标准对偶即可删除现有节点界”的假设。

## 实际消费者

- `WR2XiRationalCandidate.actual_lower_of_entry_bounds` 消费 81 个 entry bounds，给出全部九个实际节点下界。
- `WR2XiCandidateCertificate.candidate_actual_lower` 通过共同 sigma 界无条件兑现上述接口。
- `WR2XiCandidateGrid.actual_tables` 经 `WSrcGridTables.full_tables_lower` 生成 `extendedNode`、`originalTransfer` 整张逐点表。
- `WR2XiSourceNodeCertificate` 及各 SourceNode 数值模块逐点认证扩展 profile。
- `WR2XiSourceSingleRational` 用这些表加权求和。
- `WR2XiSixthRationalH`、`WR2XiSixthContinuousPanel` 对连续第六增益做逐点下界及积分。

因此仅加一个对偶定理不能替换当前消费者；需要重写后续连续积分、有限求和与实际计数之间的接口。更有结构意义的候选是直接对完整阶梯 profile 证明九个加权行界，替代逐基向量的 81 个界；但仍需要真正的新积分证明，不能简单把现有 81 个证书相加再声称删除了其依赖。

当前主比较的文件规模：`WR2XiNineCorrected` 64 物理行，`WR2XiRationalCandidate` 56 行，通用 `FiniteComparison` 约 90 行。不是项目的主要代码大头。

## 排除删除 max 支路

`WR2XiCandidateCount.nodes` 定义为逐点 `max W17Accepted.enhanced lowerH`。当前第六增益数值证书经 `candidate_gain_le_amount` 实际只消费 lowerH 的下界，旧增强支路不参与这一具体数值下界。

然而 `WR2XiSourceSixth.amount` 当前公开定义为 `continuousGain CandidateCount.nodes + HighConsumer.highGain`。直接换成 lowerH 会降低/改变一个公开数学中间量；即使最终 1.8938 及现有 0.0566 下界不受影响，也不能称作保持中间精度的等价压缩。

此外，假设只切断 SourceSixth 到 CandidateCount 的 import，主闭包仅少以下三个模块、125 物理行：

- WR2XiCandidateBaseCount
- WR2XiCandidateCount
- WR2XiContinuousMonotone

W17 旧链仍经 WE10FourBudget 等共享依赖进入主闭包。脚本输出中的 remaining_W17_importers 给出实际剩余导入者。故不采用此修改。

## 结论

本轮保留现有九节点和公开 amount 定义，不新增未使用对偶抽象。未运行新的 Lean 构建，因为未改变源代码。后续只有获得直接加权积分替代证明后，才值得重新评估该路线。
