> **Checkpoint status:** historical partial source completion; superseded.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# 沿原文补全：Wu08 的有限母式与第六项调用

**当前结果：补全了原 (2.3)–(2.6) 的逐项展开、已选标签的筛记号解释，
以及原第九项接 Wu04 §10 的一个上幂次误差桥；尚未接通原 (2.6) 后的
最后缩域和原 §5 第六项调用的全部范围。** 本文不改变作者参数、正第六项、
负四重域或数值预算，不消费已撤下的低域剪收益候选。

这是沿 Wu08 及其 Wu04 引用补全正文，不是另找一条证明，也不要求重新证明
所有经典前置。原文明确给出的数值方向保留文献引用等级；数字、函数和积分
来源由 M3 负责。本文不把“本轮没有重算”列为数学缺陷，也不把待解释的出处
推成作者定理错误。旧 `PROOF.md` 保留不改，其中固定第九门／移动第六项的
组合并未被改名后当作原 (2.2)。

## 1. 固定原对象和原编号

令 \(N\geq4\) 为偶数，原素数指标始终记为 \(p\)，补数记为 \(n=N-p>0\)。
\[
 D_{1,2}(N)=\#\{p\leq N:p\text{ 素},\ \Omega(N-p)\leq2\},
 \qquad \Omega(1)=0,\qquad \Theta(N)=C_NN/\log^2N.
\]
这里
\[
 C_N=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
          \prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2},
\]
乘积中的 \(\ell\) 均为素数。
单位补数和素补数都属于该计数。这里不把实际素数指示函数替换成整数计数。
最终主线目标是 Li–Liu 的 1.894 备注；Wu08 的普通计数输入是其证明所用的
0.899，不称为“Wu08 的 1.8938”。

使用 Wu08 (5.1) 的参数：
\[
 \alpha=\kappa_1=\frac{100}{1327},\quad
 \beta=\kappa_2=\frac{25}{206},\quad
 \sigma=\frac12-3\alpha=\frac{727}{2654},\quad
 \lambda=\frac12-2\alpha=\frac{927}{2654},
\]
\[
 z=N^\alpha,\quad w=N^\beta,\quad u=N^\sigma,\quad
 v=N^{1/3},\quad V=N^\lambda,\quad B(a)=\sqrt{N/a}.
 \tag{P1}
\]
所需条件确实成立：
\[
 \beta<\sigma<1/3,\qquad 3\alpha+\beta<1/2,\qquad
 3\alpha-\beta<1/6,\qquad \alpha>1/18.
 \tag{P2}
\]
除 §6 的实际固定参数误差外，下文的有限展开使用的正是 Lemma 2.2 条件。

本文的原编号以作者 TeX 为准。Wu08 期刊版把 §3 的两个交叉不等式分列为
(3.8)、(3.9)，故后续 §3 编号比 TeX 后移；(2.1)–(2.6)、Propositions
4.1–4.4、(5.1)–(5.6) 一致。来源为：

* `sources/Wu08.tex`，§2 全段、§3 定义 (3.1)–(3.7)、§4、§5 第三及第四小节；
* `sources/Wu04.tex`，§2 的 \({\cal A}_d\) 定义、§9 Lemmas 9.1/9.2
  完整证明、§10 (10.6)–(10.12)；
* `sources/wu08-journal.txt`，pp. 370–374、378–382，核对上述实际记号和范围。

路径相对于 `research/wu2008/`。引用这些正文结果不以其最终结论
遮住正在展开的内部步骤。

## 2. \({\cal A}_d\)、已选标签和筛门：先把原文的意思写成无歧义对象

### 2.1 两种表示不能逐字混同

Wu04 §2 明确写
\({\cal A}_d=\{n\in{\cal A}:d\mid n\}\)，即**未缩放**整除子列。
对任何模数 \(M\)，它的字面筛计数是
\[
 S^{\rm un}_M(d;t)=
 \#\{p\leq N:p\text{ 素},\ d\mid N-p,\
             \ell\mid N-p,\ \ell\nmid M\Longrightarrow\ell\geq t\}.
 \tag{P3}
\]
相应商筛写为
\[
 Q_M(d;t)=
 \#\{p\leq N:p\text{ 素},\ d\mid N-p,\
       \ell\mid (N-p)/d,\ \ell\nmid M\Longrightarrow\ell\geq t\}.
 \tag{P4}
\]
在两式中，素数变量 \(\ell\) 才是筛掉的素因子；\(p\) 仍是原输出指标。

这不是从旧 Lean 中选择定义。决定 lower weight 实际含义的原始依据是
**Wu04 (9.2) 下方对 \(s_2(n),s_3(n),s_4(n)\) 的明确定义**：
它们逐字要求
\[
 \ell\mid n/(p_1p_2)\Longrightarrow\ell\geq p_2,\qquad
 \ell\mid n/(p_1p_2p_3)\Longrightarrow\ell\geq p_2.
 \tag{P5}
\]
因此已选标签与剩余商必须分开。本文把后续 Buchstab 展开读成 (P5) 所确定的
计数，并明确注明何时能够用未缩放记号表示。

先限于
\[
        (n,N)=1,\qquad n\text{ 平方自由},\qquad P^-(n)\geq z.
 \tag{P6}
\]
约定 \(P^-(1)=+\infty\)。下文所有自由标签 \(a,b,c,d,q\) 均为与 \(N\)
互素的素数；只有 (P31) 的计数放大明确改为整数标签。
令 \(d\) 是若干已选标签的乘积。在 (P6) 上，\((n/d,d)=1\)，所以
\[
 Q_N(d;t)=Q_{Nd}(d;t)=S^{\rm un}_{Nd}(d;t).
 \tag{P7}
\]
更一般地，只须在未缩放的模数中排除那些**小于筛门的已选标签**。
例如 \(a<b<c\)：
\[
\begin{aligned}
 Q_N(ab;b)&=S^{\rm un}_{Na}(ab;b),\\
 Q_N(abc;b)&=S^{\rm un}_{Na}(abc;b),\\
 Q_N(abc;a)&=S^{\rm un}_{N}(abc;a),\\
 Q_N(abcd;b)&=S^{\rm un}_{Na}(abcd;b)\quad(a<b<c<d).
\end{aligned} \tag{P8}
\]
这些是对好补数的等式，不是全体补数上“模数没有影响”的断言。

### 2.2 哪些印出的简写须按 (P5) 展开

原 Lemma 2.1 的 \(S_2,S_3,S_4\) 写成
\({\cal P}(Np_1)\)，正好符合 (P8)。但是 (2.6) 的正三重项改写成
\({\cal P}(N)\)，原两个负四重项也写成
\(S({\cal A}_{abcd};{\cal P}(N),b)\)。
若同时坚持“未缩放”和“并不排除 \(a\)”这两个字面条件，因
\(a<b,\ a\mid n,\ (a,N)=1\)，后一计数恒为零。它就不能等于原证明实际展开的
四因子计数。

这里能够补出的解释是：**该处继续采用 (P5) 的剩余商条件**；
若用未缩放子列表示，须补写 \({\cal P}(Na)\)，或者统一用
\({\cal P}(Nabcd)\)。同样，第三个负三重项在门 \(c>b\) 时，若采用未缩放子列，
须排除 \(a,b\)，不能只排除 \(a\)。
原第九项也有同一问题：当 \(b<\sqrt{N/(ab)}\) 时，若使用未缩放子列，
只写 \({\cal P}(Na)\) 仍会被已选标签 \(b\) 筛掉；表达剩余商的条件须写
\({\cal P}(Nab)\)。Wu04 固定第九门在 \(b<N^{\sigma_1}\) 时亦然。
这把作者前面明确给出的逐补数权同后面的 Buchstab 项接到同一对象上。
它不是声称印出的两种字面记号原本相等；也不能利用字面四重项为零来“证明”
母式或套用其后非零的四重积分。

以下在 (P6) 上简记 \(Q(d;t)=Q_N(d;t)\)。从这里开始每一次有号展开都只用
这个已由 (P5) 固定的对象。特别地，§6 所谓“原第九项”是按此逐补数含义
规范化的移动门计数，不是声称其字面未缩放、未排除全部小标签的式子与商筛
相等；后一种确定性的筛除不能塞进平方异常费用。

### 2.3 被排除的补数确实只贡献允许的费用

若 \((N-p,N)>1\)，则 \(p\mid N\)，只有 \(O(\log N)\) 个素数指标。
若某个有贡献的粗补数不平方自由，则有 \(\ell\geq z\) 满足
\(\ell^2\mid n\)，其指标数至多
\[
                    N\sum_{m\geq z}m^{-2}=O(N/z).
 \tag{P9}
\]
每个补数的已选标签均至少 \(z\)，标签数（按重数）不超过
\(\lfloor1/\alpha\rfloor\)。固定阶的标签多重性有仅依赖 \(\alpha\) 的上界，
所以 (P9) 支付的是**加权的所有相关项**，而不只无标签指标数。
模数从 \(N\) 改为包含已选标签的乘积时，额外商因子恰是已选标签的重复，
也包含在这个费用中。原三重正量、prime remainder 和各次下界的非负 slack
没有被改成零；它们只在原文已经取下界的地方被舍弃。

第九项在本参数下的商门也大于 \(z\)：由 \(a<u,\ b<B(a)\)，
\[
 ab<N^{(1+\sigma)/2},\qquad
 \sqrt{N/(ab)}>N^{(1-\sigma)/4}>N^\alpha.
 \tag{P10}
\]
故它不会引入本估计未涵盖的小素因子重复族。
单位补数满足 (P6)，始终保留。

### 2.4 端点不是可任意互换的约定

Wu04 用筛乘积 \(\ell<t\)，Wu08 §2 的定义写 \(\ell\leq t\)。
本文沿 Wu04 的严格门展开，并逐项说明端点：

* 当筛门为已选标签 \(a,b,c\) 时，好补数的商不再含该标签，
  故商筛的严格／闭门相同；其余差异在重复费用 (P9) 中。
* 对固定的正有理幂 \(t=N^{r/s}\)，如果某素数 \(\ell=t\)，
  则 \(\ell^s=N^r\)，从而 \(\ell\mid N\)，该素数本来就不属于
  \({\cal P}(N)\)。因此本参数所有固定幂次门没有这一端点损失。
* 原第九门不能等于任何整数 \(q\)：否则
  \(N=abq^2\)，与素数 \(a\) 满足 \((a,N)=1\) 矛盾。
  这也正是已存 `WR2MotherNinthEndpoint.lean` 中
  `WuPaper.R2Mother.no_natural_sqrt_endpoint` 及
  `WuPaper.R2Mother.ninth_strict_eq_closed` 的实际理由。
* 移动乘积边界 \(cd=N^\lambda\) 在本有理 \(\lambda\) 下同样不可能：
  取整次幂得到 \(c\mid N\)。这不允许删除开域 \(cd>N^\lambda\)。

因此下面的问题不来自遗漏一个端点，也不是用相同名称隐藏严格／闭域差异。

## 3. 原 Lemma 2.1 如何输入 (2.3) 和 (2.5)

沿 Wu04 Lemma 9.1 的逐补数证明，令 \(r\) 为小于上筛门 \(t\) 的素因子数，
\(k=\Omega(n)\)。它使用
\[
 W(z_0,t)=2Q(1;z_0)-S_1(z_0,t)-2S_2(z_0,t)-S_3(z_0,t)+S_4(z_0,t).
 \tag{P11}
\]
若 \(k\leq2\)，正三重项为零，其权不超过 2。
若 \(k\geq3\)，最小两个因子 \(q_1<q_2\) 满足 \(q_1q_2^2<n<N\)；
商筛条件使负两标签权只能选这一对。
当 \(r=0\) 时 \(S_2=1\)，当 \(r=1\) 时 \(S_3=1\)；
当 \(r\geq2\) 时两者均为零，且 \(S_4=r-2\)。
于是三种情形的权分别为 \(2-2\)、\(2-1-1\)、\(2-r+(r-2)\)，均为零。
这也补上 Wu04 逐案文字没有单列的 \(k\geq4,r=0\) 情形。
单位和素补数不被负项错误剔除。

所以原 (2.1) 对两组参数成立。原正文实际选的是
\[
                   (\beta,\sigma),\qquad(\alpha,1/3).            \tag{P12}
\]
以 (2.3) 和 (2.5) 的明确代入为准；原 Remark 1 把两组上门的配对写反，
不能据那句概述改变已经展开的权。
第一组丢掉非负 \(S_4(\beta,\sigma)\)，就是 (2.3)；
第二组有 \(S_2(\alpha,1/3)=0\)，因为 \(a\geq v,b>a\) 与
\(b<\sqrt{N/a}\) 不相容，得到 (2.5)。

这些引用和简单分类足以继续原证明，不需要重新研究一般 Chen 定理。

## 4. 不换第九筛门，逐项导出原 (2.4)–(2.6)

为使组合自足，先列清原 Lemma 2.2 的全部槽。依 §2 的记号解释，在好补数上为
\[
\begin{aligned}
 \Upsilon_1&=Q(1;z),&
 \Upsilon_2&=Q(1;w),\\
 \Upsilon_3&=\sum_{z\leq a<v}Q(a;z),&
 \Upsilon_4&=\sum_{z\leq a<u}Q(a;z),\\
 \Upsilon_5&=\sum_{z\leq a<b<w}Q(ab;z),&
 \Upsilon_6&=\sum_{z\leq a<w\leq b<u}Q(ab;z),\\
 \Upsilon_7&=\sum_{u\leq a<b<B(a)}Q(ab;b),&
 \Upsilon_8&=\sum_{z\leq a<v\leq b<B(a)}Q(ab;b),\\
 \Upsilon_9&=\sum_{w\leq a<u\leq b<B(a)}Q(ab;\sqrt{N/(ab)}),\\
 \Upsilon_{10}&=\sum_{z\leq a<b<c<d<w}Q(abcd;b),\\
 \Upsilon_{11}&=\sum_{z\leq a<b<c<w\leq d<V/c}Q(abcd;b).
\end{aligned}
\]
后三项的商允许为 1。返回全部补数的记号运输使用 (P9)，而不是删除这些单位商。

### 4.1 作者两次／三次 Buchstab 的承重算式

对好补数，在同一个素数指标上，商的最小素因子分拆给出
\[
              Q(d;r)=Q(d;t)+\sum_{r\leq q<t}Q(dq;q)
                         \quad(r\leq t),                       \tag{P13}
\]
其中已选标签不能再作新因子；重复项已经由 (P9) 处理。
对原文当前使用的两个窗口，(P13) 依次给出
\[
\begin{aligned}
 Q(1;w)
  &=Q(1;z)-\sum_{z\leq a<w}Q(a;a),\\
 \sum_{z\leq a<w}Q(a;z)
  &=\sum_{z\leq a<w}Q(a;a)+
      \sum_{z\leq b<a<w}Q(ab;b),\\
 \sum_{z\leq a<b<w}Q(ab;z)
  &=\sum_{z\leq a<b<w}Q(ab;a)+
      \sum_{z\leq c<a<b<w}Q(abc;c).
\end{aligned} \tag{P14}
\]
第二式中的有序对换名后接第三式，因而
\[
 \Upsilon_2=\Upsilon_1-\sum_{z\leq a<w}Q(a;z)
                              +\Upsilon_5-T_0,
 \qquad T_0=\sum_{z\leq a<b<c<w}Q(abc;a).                         \tag{P15}
\]
这正是 (2.3) 后的第一条 Buchstab 展开。

同理，保持正二重项的**全矩形**，
\[
\begin{aligned}
 S_1(\beta,\sigma)
 &=\sum_{w\leq d<u}Q(d;z)-\sum_{z\leq c<w\leq d<u}Q(cd;c)\\
 &=\sum_{w\leq d<u}Q(d;z)-\Upsilon_6+T_1,\\
 T_1&=\sum_{z\leq a<b<w\leq c<u}Q(abc;a).
\end{aligned} \tag{P16}
\]
这里没有提前加 \(bc<V\)，也没有缩小原 \(\Upsilon_6\)。
每次换名是一一对应，既不产生也不丢掉阶乘系数。

### 4.2 原移动平方根门的 Buchstab 不等式

对 \(w\leq a<u\leq b<B(a)\)，令
\[
                         Y(a,b)=\sqrt{N/(ab)}.
\]
原第九项保持为
\[
             \Upsilon_9=\sum_{w\leq a<u\leq b<B(a)}Q(ab;Y(a,b)).
 \tag{P17}
\]
如果 \(b<Y(a,b)\)，(P13) 给出
\[
 Q(ab;b)=Q(ab;Y(a,b))+
                           \sum_{b<c<Y(a,b)}Q(abc;c).            \tag{P18}
\]
如果 \(b\geq Y(a,b)\)，单调性给出 \(Q(ab;b)\leq Q(ab;Y(a,b))\)。
于是恰有原文需要的
\[
 S_3(\beta,\sigma)\leq\Upsilon_9+T_2,\qquad
 T_2=\sum_{w\leq a<u\leq b<c<\sqrt{N/(ab)}}Q(abc;c).
 \tag{P19}
\]
在 \(T_2\) 中 \(b<c<\sqrt{N/(ab)}\) 已蕴含 \(ab^3<N\)，
故原先的 \(b<B(a)\) 自动成立，省写它是合法的。
被舍弃的是 \(b\geq Y(a,b)\) 上的非负筛门差；没有改变单位商条件。

将 (P15)、(P16)、(P19) 代入 (2.3)，且
\[
 \sum_{z\leq a<w}Q(a;z)+\sum_{w\leq a<u}Q(a;z)=\Upsilon_4,
\]
得到原 (2.4)，其中
\(\Delta_1=T_0+T_1+T_2\)。加上原 (2.5)，就得到原 (2.6)：
\[
\begin{aligned}
 4D_{1,2}(N)\geq{}&
 3\Upsilon_1+\Upsilon_2-\Upsilon_3-\Upsilon_4+\Upsilon_5+\Upsilon_6
 -2\Upsilon_7-\Upsilon_8-\Upsilon_9+\Delta_2
 -O_\alpha(N^{1-\alpha}),\\
 \Delta_2={}&\sum_{z\leq a<b<c<v}Q(abc;b)-T_0-T_1-T_2 .
\end{aligned} \tag{P20}
\]
这段证明与原步骤对应，不消费旧稿的替代母式。

## 5. 原 (2.6) 后的范围归并：已接通部分与最早尚未接通处

前三个负三重域互不相交。前两个域包含在 \(z\leq a<b<c<v\) 中，因为
\(w<u<v\)。第三个域也包含在内：
\[
 c<\sqrt{N/(ab)}
   \leq N^{(1-\beta-\sigma)/2}
   =N^{(1/2+3\alpha-\beta)/2}<N^{1/3}.
 \tag{P21}
\]
这补全原文紧接 (2.6) 的第三域算式；条件
\(3\alpha-\beta<1/6\) 的用途正是这里，不是用来截掉第二个域。

在这三个互不相交域上减去相应正三重项，第一域出现
\[
 \sum_{z\leq a<b<c<w}\{Q(abc;a)-Q(abc;b)\}.
 \tag{P22}
\]
按 (P13) 插入新最小剩余因子 \(a<q<b\)，把 \((a,q,b,c)\) 依次换名为
\((a,b,c,d)\)，(P22) 正好等于原 \(\Upsilon_{10}\)。
第三域出现 \(Q(abc;b)-Q(abc;c)\geq0\)，方向也正确。

第二域同一操作实际给出
\[
 \sum_{z\leq a<b<w\leq c<u}\{Q(abc;a)-Q(abc;b)\}
      =\sum_{z\leq a<b<c<w\leq d<u}Q(abcd;b).                    \tag{P23}
\]
其中插入及换名仍为 \((a,q,b,c)\mapsto(a,b,c,d)\)。
右端最后两标签的范围是原来的矩形，不自动带 \(cd<V\)。

原文接下来显示的第二个负三重和却改为
\[
        z\leq a<b<w\leq c<V/b.                                 \tag{P24}
\]
因为 \(b\geq z\) 且 \(V=zu\)，有 \(V/b\leq u\)，故 (P24) 是 (P23) 左侧的
**子域**。被积筛门差非负；在负号之后缩域，会提高右端。仅凭三个域包含于
正三重域，还不能推出这个提高后的不等式。

为准确陈述原文这一行还需什么，而不是新增一个要求单项足够小的接口，
令 \({\cal R}_0(N)\) 为正三重域扣除上述三个域后的计数和，令
\[
 {\cal R}_3(N)=
 \sum_{w\leq a<u\leq b<c<\sqrt{N/(ab)}}\{Q(abc;b)-Q(abc;c)\}\geq0.
 \tag{P25}
\]
那么只用上述已展开的恒等式，在好补数上有
\[
\begin{aligned}
 \Delta_2+\Upsilon_{10}+\Upsilon_{11}
   ={\cal R}_0(N)+{\cal R}_3(N)
    -\sum_{\substack{z\leq a<b<c<w\leq d<u\\cd\geq V}}Q(abcd;b).
\end{aligned} \tag{P26}
\]
这是原始三重换名的核算，不是新的付款定理；与已存
`WR2MotherDelta2.lean` 中 `WuPaper.R2Mother.paper_delta2_moving_exact` 的符号相符。
回到全部补数只增加 (P9) 的费用。

**沿原印出推导的最早未接通箭头**，是由现有输入推出
\[
               \Delta_2(N)\geq-\Upsilon_{10}(N)-\Upsilon_{11}(N)
                                    -O_\alpha(N^{1-\alpha}).    \tag{M}
\]
其现有输入是 (P20)–(P26)、原参数条件和非负性，不是任何数值表。
本文没有证明 (M)。这不表示必须单独把 (P26) 最后一项估成
\(O(N^{1-\alpha})\)；原先在 (2.3)、(P19) 和 lower weight 中舍弃的正量，
若有作者方法支持的联合比较，也可以用于直接证明最终 (2.2)。
目前没有给出这种比较，不能用“全正量必能支付”代替证明。

### 与 Wu04 Lemma 9.2 的确切对应，而非借名换路线

Wu04 (9.6) 后的那一步的确出现同一移动门 \(V/b\)。在那里作者先有一个
**正**二重和
\[
 \sum_{z\leq c<w\leq d<N^\rho}Q(cd;c),
\]
利用 \(3\alpha+\rho\geq1/2\) 得 \(V/c\leq N^\rho\)，先把它减小为
\(\sum_{cd<V}Q(cd;c)\)，再作 Buchstab，于是同时产生
\[
 \sum_{cd<V}Q(cd;z)
  -\sum_{z\leq a<b<w\leq c<V/b}Q(abc;a).
 \tag{P27}
\]
所以在 Wu04 的步骤中，移动正二重项与移动负三重项成对出现，方向完全有根据。
这解释了旧稿移动第六项的原文来源。
但 Wu08 (P16) 已经保留全矩形 \(\Upsilon_6\)，不能只把 (P27) 中的移动负域
拿来，而把原成对缩小的正项免费恢复成全域。
本文不把 (P27) 当作原 (2.2) 的证明，也不继续消费旧低域剪收益候选。

## 6. 补上原第九项到 Wu04 (10.11) 的实际计数桥

这一节不换原母式中的 (P17)。它只解释 Wu08 §5 第四小节“这些项就是
Wu04 相应项”在第九项上所需的渐近运输。

Wu04 (9.4) 的 \(\Upsilon_{10}\) 使用固定门 \(N^{\sigma_1}\)，而 Wu08 的
\(\Upsilon_9\) 用 \(\sqrt{N/(ab)}\)。为对照原 §5 所引
Wu04 (10.11)，记同标签的固定门计数
\[
 J_9=\sum_{w\leq a<u\leq b<B(a)}Q(ab;v).
 \tag{P28}
\]
以下证明，不假定它与 \(\Upsilon_9\) 逐项相等：
\[
       \Upsilon_9=J_9+O_\alpha\!\left(N^{1-\eta_9}\right),
       \qquad \eta_9=\frac{1-3\sigma}{6}
                       =\frac{473}{15924}>0.                   \tag{P29}
\]

在好补数上，\(ab\geq N^{\beta+\sigma}\)，且
\[
      \beta+\sigma-\frac13=\frac{25403}{410043}>0,
\]
故 \(Y(a,b)<v\)，给出 \(J_9\leq\Upsilon_9\)。
一个由 (P17) 计到的非单位商 \(m=n/(ab)\) 必为素数：若 \(\Omega(m)\geq2\)，
其每个素因子至少 \(Y(a,b)\)，从而
\[
                         m\geq Y(a,b)^2=N/(ab)>n/(ab),
 \tag{P30}
\]
矛盾。模数排除已选首标签的重复异常由 (P9) 支付。这一素商判断也已有同对象
`NinthSwitchingCofactor.lean` 中
`Wu2008DoubleSieve.ninth_cofactor_one_or_prime`，并非另设商为素数的假设。

因此 \(\Upsilon_9-J_9\) 只可能有商为素数 \(m<v\) 的指标。
**单位商在两项都被计入，差中恰好抵消。** 放大这个小商差集而不放大整个
第九负项，保留标签的数量上界为
\[
\begin{aligned}
 0\leq\Upsilon_9-J_9
 &\leq \sum_{1\leq a<u}\sum_{1\leq b<\sqrt{N/a}}
                                  \sum_{1\leq m<v}1\\
 &\leq v\sqrt N\sum_{1\leq a<u}a^{-1/2}
 \leq 2v\sqrt{Nu}
 =2N^{5/6+\sigma/2}=2N^{1-\eta_9}.
\end{aligned} \tag{P31}
\]
每个 \((a,b,m)\) 最多给出一个 \(p=N-abm\)，所以该放大计数正确处理了多重性；
不需要假定所有这些 \(p\) 都是素数，也没有把整个母式的素数指示函数丢掉。
加回 (P9) 的费用仍为 (P29)，因为 \(0<\eta_9<\alpha\)。

Wu04 §10 对固定门计数使用
\(2\sigma_1+\sigma_2+\kappa_2>1\) 排除复合商。
取本处 \(\sigma_1=1/3,\sigma_2=\sigma,\kappa_2=\beta\) 时该条件成立。
虽然 Wu04 §9 的母式参数写 \(\sigma_1<1/3\)，这里引用的是其 §10 对该计数的
switching 估计，不是在边界上直接引用整条 Lemma 9.2。估计所需的不等式仍有
严格余量：
\[
 2/3+\sigma+\beta>1,\qquad
 N^{1/3}<\sqrt{N/a}\quad(a<u,\ \sigma<1/3),\qquad
 ab<N^{(1+\sigma)/2}<N^{2/3}.
 \tag{P32}
\]
固定门只使商必须是素数或 1；上筛时还可放宽其素数下门。具体把 Wu04 的“similarly”代入如下。令
\[
 {\cal M}=\{ab:w\leq a<u\leq b<B(a),\ (ab,N)=1\},\quad
 X=\sum_{m\in{\cal M}}\operatorname{li}(N/m).
\]
由于两个窗口分离，每个 \(m\) 的标签分解唯一，故权 \(f=1_{\cal M}\) 满足
\(|f|\leq1\)。商为 1 的那部分 \(J_9\) 至多
\(2\sqrt{Nu}=o(\Theta)\)，先明确支付；它在 (P31) 的差中抵消不等于在
\(J_9\) 自身不存在。
其余项的商是素数。放宽其下门，令 \({\cal B}\) 为按 \((m,r)\) 计重的
\(N-mr>0\)，其中 \(m\in{\cal M}\)、\(r\leq N/m\) 为素数。
原输出素数 \(p\leq\sqrt N\) 至多贡献 \(O_\beta(\sqrt N)\) 个带标签项：
每个 \(N-p\) 中至少 \(N^\beta\) 的因子按重数有常数上界。
其余输出素数必被 \({\cal B}\) 的 \(N^{1/2}\) 上筛计入。

引用 Wu04 Lemma 2.3 第一条（Pan–Ding），其真实量词是：对任意有界权
\(f\)、固定 \(\theta\in(0,1]\) 及每个 \(A>0\)，存在 \(B=B(A)>0\)，
相应模数平均误差为 \(O(N/\log^A N)\)。此处取
\(\theta=1/6\)、\(x=y=N\)、权 \(1_{\cal M}\)、既定剩余类 \(N\bmod q\)
且 \((q,N)=1\)。它的权支撑上门是 \(N^{1-\theta}=N^{5/6}\)，
而本处 \(m<N^{(1+\sigma)/2}<N^{2/3}\) 有严格余量。因此原 (10.7) 的
\(R_3\ll N/\log^3N\) 可直接消费。对原 (10.8) 的非互素余项，只把其
最小因子下门 \(N^{\sigma_1}\) 换成本处的 \(N^\beta\)：
\[
            R_4\ll N^{1-\beta}\log^2N=o(\Theta).
\]
这沿用同一求和证明，因为 \(m=ab\) 的所有因子均至少 \(N^\beta\)，
并未误用 \(N^{1/3}\) 作为已选标签下门。
Wu04 Lemma 2.2 的经典上筛，取原 (10.6) 的
\(Q=N^{1/2}/\log^B N\)、\(z_{\rm sieve}=N^{1/2}\)，于是给出
\[
            J_9\leq (8+O(\varepsilon))C_N X/\log N+o(\Theta).
 \tag{P32a}
\]
这已保留实际输出和标签多重性；没有改变分布定理或重证它。
素数分部求和给出
\[
 X\leq(1+o(1))\,\frac{N}{\log N}
       \int_\beta^\sigma\int_\sigma^{(1-x)/2}
                      \frac{dy\,dx}{xy(1-x-y)}.                 \tag{P32b}
\]
其中可先放宽标签的 \((ab,N)=1\) 以取得上界。
原双重积分内层为
\[
 \int_{\sigma}^{(1-x)/2}\frac{dy}{y(1-x-y)}
     =\frac1{1-x}\log\frac{1-x-\sigma}{\sigma};
\]
令上筛中的固定 \(\varepsilon\downarrow0\)，该引用给出
\[
 J_9\leq(C_9+o(1))\Theta(N),\qquad
 C_9=8\int_\beta^\sigma
 \frac{\log((1+6\alpha-2x)/(1-6\alpha))}{x(1-x)}\,dx.             \tag{P33}
\]
由 (P29) 及 \(C_N\gg1\)，其误差除以 \(\Theta\) 趋于零，于是**原移动门**
\(\Upsilon_9\) 得到同一个 (P33) 上界。
这补的是 Wu08 (5.6) 的引用运输，不是用固定第九门代替原 (2.2)；
也不把指数较弱的 (P29) 冒充 Lemma 2.2 所写的 \(O(N^{1-\alpha})\)。

## 7. Proposition 4.3 的真实输入与 §5 调用

### 7.1 原命题为何有三个条件

Wu08 Proposition 4.3 的条件是
\[
\begin{gathered}
 0<\phi_1<\phi_2\leq\phi_3<\phi_4<1/4,\qquad
 2\phi_2+\phi_4<1/2,\qquad \phi_2+\phi_4+\kappa\leq1/2.
 \tag{P34}
\end{gathered}
\]
其第二重求和印成再次约束 \(p_1\)；由被积对象 \(p_1p_2\) 和两段窗口可确定
它约束的是 \(p_2\)，并非第三个自由标签。

下面补充原文“In a similar fashion”的两标签衔接，不增加命题条件。
把两个素数窗口分成 §3 规定的短区间，分别有上端 \(X,Y\)，\(X\leq Y\)，
令权为
\[
                   \eta=\pi_{[Y/\Delta,Y)}*\pi_{[X/\Delta,X)}.
 \tag{P35}
\]
两窗口不交，唯一分解中的较大标签来自第一因子，故对 \(d=ab\) 的卷积重数
是 1，而不是 2。这也与已存
`WR2SixthCountWindows.lean` 中 `separated_coefficient_one` 的对象一致。
按原 (3.1) 取 \(V_1=Y,V_2=X\)，实际要求
\[
                   Y^2\leq Q,\qquad YX^2\leq Q,\qquad
                   Q=N^{1/2-\delta}.                            \tag{P36}
\]
因此 (P34) 中前两条上界分别支付 (P36) 的两条，而非同一个条件的两种写法。
第三条保证 \(\log(Q/(XY))/(\kappa\log N)\) 的筛参数至少为 1；
在等号边界先取严格内区再通过积分极限即可。

设
\[
 s_{X,Y}=\frac{\log(Q/(XY))}{\kappa\log N}.
\]
对该箱中的 \(a,b\)，\((Q/(ab))^{1/s_{X,Y}}\geq N^\kappa\)，所以
\[
 \sum_{a,b}Q(ab;N^\kappa)
 \geq \Phi(N,\eta,s_{X,Y})
 \geq\{a(s_{X,Y})+h_{k,N_0}(s_{X,Y})\}\Theta(N,\eta).             \tag{P37}
\]
第一步是下筛方向，不需要把可变筛门差假定为零。
第二步正是原 (3.7)，只能在 (P36) 满足时使用。再用
\[
 C_{abN}/\varphi(ab)=C_N/((a-2)(b-2)),
\]
素数分部求和和原文的极限约定，得到其双标签主核
\[
 4\iint\frac{a((1/2-x-y)/\kappa)+h((1/2-x-y)/\kappa)}
                   {xy(1/2-x-y)}\,dx\,dy.
 \tag{P38}
\]
令 \(s=(1/2-x-y)/\kappa\)，绝对 Jacobian 为 \(\kappa\)，(P38) 成为
\[
 8\int_{\phi_1}^{\phi_2}\int_{(1/2-\phi_4-x)/\kappa}^{(1/2-\phi_3-x)/\kappa}
       \frac{a(s)+h(s)}{xs(1-2x-2\kappa s)}\,ds\,dx,             \tag{P39}
\]
正是 Proposition 4.3 的核与方向。这里 \(H,h\) 使用作者的极限记号；
在固定正 \(\delta\) 上先用 (P37)，不自行假定 \(\delta=0\) 存在一个实际筛类。
数字及极限函数来源由 M3 接续，本文没有改变这些对象。

### 7.2 原三分区的条件代入

令 \(L=1/2-2\beta\)。原 §5 第三小节把 \(\Upsilon_6\) 分为
\[
\begin{array}{c|cc}
 &x=\log a/\log N&y=\log b/\log N\\ \hline
 {\cal A}&[\alpha,\beta)&[\beta,L)\\
 {\cal B}&[\alpha,3\alpha/2)&[L,\sigma)\\
 {\cal C}&[3\alpha/2,\beta)&[L,\sigma)
\end{array} \tag{P40}
\]
并说前两块用 Proposition 4.3，最后一块用经典线性筛。
原前两块对应的参数是
\[
 (\phi_1,\phi_2,\phi_3,\phi_4,\kappa)
  =(\alpha,\beta,\beta,L,\alpha),\quad
    (\alpha,3\alpha/2,L,\sigma,\alpha).
\]
其中
\[
\begin{array}{c|cc}
 &2\phi_2+\phi_4&\phi_2+\phi_4+\kappa\\ \hline
 {\cal A}&1/2&1/2+\alpha-\beta<1/2\\
 {\cal B}&1/2&1/2-\alpha/2<1/2
\end{array} \tag{P41}
\]
第一个等号可以处理：把相应上门向内移 \(\varepsilon\)，在固定内区应用定理，
最后 \(\varepsilon\downarrow0\)。丢掉的只是边界条带；主核在本固定域上可积。
因此不应把这一等号单独报成不可解的障碍。

但是另一条条件仍需解释：
\[
                L-\frac14=\frac3{412}>0,\qquad
                \sigma-\frac14=\frac{127}{5308}>0.              \tag{P42}
\]
所以 (P36) 的 \(Y^2\leq Q\) 不由 (P41) 支付。
期刊原文同样有 \(\phi_4<1/4\)，§5 同样采用 (P40)。
紧接 Proposition 4.3 的原文还明确说明，大于 \(N^{1/4}\) 的单标签和
不能直接用该完整双筛，因为 (3.1) 的第一条件；随后 Proposition 4.4
给的是单标签的简化**上筛**，不能直接换成 (P37) 的两标签下筛。

这不是说高区没有分布定理。标准 BV 及既有
`Wu08G6HighActual.lean` 中 `unrestricted_AP_and_theta` 可供应实际余项控制；
它没有结论 \(a+h\)。已读同对象的
`WSrcSixthGainQualification` 也只给出 (P42) 与既有筛类的范围，
不是更强下筛的生产者。
把两标签交换顺序不会解决它：原 (3.1) 要求按大小排序，
且最大标签的平方仍须不超过 \(Q\)。

### 7.3 不把“必须恢复全函数”加到作者真正用的结论上

作者 (5.5) 写 \(\Upsilon_6\geq(F_6+o(1))\Theta\)，其后最终求值却只使用
\(s\geq2\) 的部分。按其原积分，设
\[
 {\cal R}=\{(x,y):\alpha\leq x\leq\beta,\ \beta\leq y,\
                                          x+y\leq\lambda\}.
 \tag{P43}
\]
这里 \(y\leq\lambda-\alpha=\sigma\) 自动成立。经典函数在 \(s\leq2\) 为零，
故原矩形的经典第六项 \(C_6\) 恰等于在 \({\cal R}\) 上的积分。
作者最后的阶梯收益是
\[
                  G_{6,\mathrm{step}}=8\sum_{i=1}^{21}g_6^i h(s_i),
                  \qquad s_i=2+i/10,                           \tag{P44}
\]
其中第 15 格跨原对数核分界
\((1/2-2\beta)/\alpha=70331/20600\)，第 21 格截于
\((1/2-\alpha-\beta)/\alpha=41453/10300\)。
保留作者原取值与方向，不另选低域剖面、不扣高域收益。

于是继续原数值论证所需的可以只是
\[
 \forall\varepsilon>0\ \exists N_0\ \forall N\geq N_0\ (N\text{ 偶})
 \quad
 \Upsilon_6(N)\geq
                 (C_6+G_{6,\mathrm{step}}-\varepsilon)\Theta(N).
 \tag{S}
\]
这比要求两个原矩形上处处具有完整最优 \(h\) 改善弱。本文**不把更强的高区
全函数命题列为额外必经接口**。但 (S) 也还没有从 (P34)–(P42) 推出：
原阶梯的前四格有一部分位于
\[
 \alpha<x<1/4-2\alpha,\qquad 1/4<y<\lambda-x,\qquad
                   2<s(x,y)<927/400,
 \tag{P45}
\]
不是零测边界。作者最终积分并未自动排除这些点。
原最后只用较弱积分这一事实减少了所需结论，却不自动完成 (S)。

因此原第六项需要的是一条能支持原 (S) 的计数推导，或对原 §5 调用的另外
正确解释。本文尚未找到所读原文及现有同对象定理中能够直接提供它的结果。
这句话不排除原作者方法还有可展开的平均／重组论证，也不把当前未接通称为
作者定理错误；这里只准确划清已用定理的真实条件。

## 8. 本轮补全结果与仍未接通处

本轮沿原步骤已经实际补出的数学连接是：

1. 用 Wu04 (9.2) 的显式商条件解释已选标签，给出 (P7)–(P10) 的未缩放
   表示、重复费用及端点关系，不再把冻结定义当作原文规格；
2. 保留原全 \(\Upsilon_6\) 和移动平方根第九门，逐次导出 (P15)–(P20)，
   接通原 (2.3)–(2.6)，说明三个域的包含关系和每次换名；
3. 以 (P29)–(P33) 接通原第九计数至 Wu04 (10.11) 的上界引用，
   明确只在解析估计层运输，不替换原有限母式；
4. 展开 Proposition 4.3 的短箱卷积、标签重数、筛门方向和 Jacobian，
   并处理 §5 两个平方前缀条件中的可解等号边界。

沿原证明顺序，最早仍未接通的是 **(M)**，即 (2.6) 后第二个负三重域的
缩小如何由现有原量推出；精确现有等式是 (P26)，而 Wu04 的来源步骤是
成对出现的 (P27)。其后仍有 **(S)**，即原第六项真正用于最终求值的下界：
现成 Proposition 4.3 的一个条件超出其所供范围，尚无补充推导。

这两处没有用 0.899 本身作黑箱，也没有用新的数值预算掩盖。经典分布、筛法、
Wu04 专门估计按真实对象和条件引用即可，不另设“全部祖先重证”门槛。
数字／函数／积分身份交给 M3，本文不另算、不替其下结论。
`math_complete=false`，`global_complete=false`；不宣称原单条母式、
0.899 或 1.894 全链已经证明。
