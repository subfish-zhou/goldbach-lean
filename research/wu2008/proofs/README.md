# 原论文证明稿与研究检查点

本目录保存自然语言数学源稿（Markdown/LaTeX公式），不是完整证明已验收或Lean全链完成的声明。

当前沿Li–Liu对1.894的备注及其Wu引用补全证明。1.8938是后期研究目标，不是已经证明的结论。

## 当前阅读顺序

1. [有限母式的明示补正](M1/PAPER-FINITE-FINAL.md)：已做数学核对，保留原最终第六项系数支持；不声称原full-Upsilon6字面引理已证。
2. [原数值方法与输入](M3/PAPER-NUMERICS.md)、[原有号数值账补全](ORIGINAL-NUMERIC-COMPLETION.md)：依赖明确列出的文献数值和已有同对象证书。
3. [第六项解析候选](M3/PAPER-SIXTH-NUMERIC-TARGET.md)须与[数学补充](SIXTH-ANALYTIC-SUPPLEMENT.md)共同使用；原较强数值端点未获确认，改用[固定表向量严格证书](TABLE-GAIN-CERTIFICATE.md)并明确支付差额。
4. [到1.894的后半桥](M3/PROOF.md)：在准确引用的Wu计数定理及经典输入下已核对。
5. [第九项上筛引用补正](NINTH-SIEVE-CORRECTION.md)。
6. [自然语言总装稿](PAPER-ROUTE-ASSEMBLY.md)：沿原方法、明确列出经典及数值引用；总装终审中，不是Lean全链完成。

证书脚本与固定输入见 `certificates/`，只使用Python标准库，生成与证书校验均已实跑。

其余稿件保留其历史阶段，特别是LOW-REGION-CANDIDATE.md已撤下主攻。正文里的阶段性结论以各文件顶部状态及manifest.json为准。旧书目信息的后续更正见PAPER-NUMERICS.md。

源码位于../src/，其中Wu18938Campaign/M3/Confirmed/接入已确认部分。成功局部回执只证明对应源码完成过该项检查；不等于论文主结论或完整依赖锥验收。标准Lean逻辑公理与定理类型中的数学前提分别判断。

## 来源与保存边界

- Li–Liu，Theorem (1+1.9) on the Goldbach Conjecture，https://arxiv.org/html/2606.05224v1 ，Theorem1.1后有1.894备注。
- Wu，Chen's double sieve, Goldbach's conjecture and the twin prime problem；以及同题续篇（2008，Acta Arithmetica 131.4，367–387）。具体公式位置和原件哈希保留在各稿。
- 文中的sources/Wu04.tex、sources/Wu08.tex与期刊提取文本是原文核对标签；第三方原文不随此次检查点重新分发。src/引用相对于research/wu2008。
- 不发布凭据、会话日志、私有审读记录或调度文件。公开正文经过非数学路径/工具标签清理；原稿哈希另列，数学原式不改。

本项目按实质进展逐次提交检查点，不等待全量构建。每个提交都是可回取的历史版本，并非自动提升证明等级。
