> **Checkpoint status:** parent mathematical correction to sieve-parameter application.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# 第九项引用的局部补正

M1/PAPER-COMPLETION.md(P29)–(P31)的移动/固定筛门差估计可保留：对差集的每个实际标签(a,b,m)，p=N−abm唯一，整数放大给2N^(5/6+sigma/2)，且(1−3sigma)/6=473/15924>0。

但(P32a)不能直接把z_sieve=N^(1/2)代入Wu04 Lemma2.2，其陈述要求z<=sqrt(Q)。修正只需原上筛的单调性，不改变计数或积分：令Q=N^(1/2)/(log N)^B，z=sqrt(Q)。任何原输出素数p>sqrt(N)仍通过z筛；原先已付的小输出界不变。若中间写过S(B,sqrt(N))，则S(B,sqrt(N))<=S(B,z)。
在z=sqrt(Q)上合法应用Lemma2.2，s=log Q/log z=2、F(2)=e^gamma；Mertens局部产品给V_N(z)<=(2e^(-gamma)+o(1))*C_N/log z，且log z/log N趋于1/4。因此主项仍为(8+o(1))*C_N X/log N。
非互素标签的R4继续按同一原计数另付，不能直接采用所有m与筛模数互素的简化式。来源Wu04(10.8)的求和在标签最小素因子N^beta下给O(N^(1−beta)log²N)；Pan–Ding的其余余项用原有界权引用。此补正只处理上筛范围，不声称未证母式或第六项下筛已完成。
