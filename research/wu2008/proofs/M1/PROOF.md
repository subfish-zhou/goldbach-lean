> **Checkpoint status:** historical reconstruction draft; superseded.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# Wu 的普通 Chen 计数输入 0.899：数学重建

**结论状态：尚未证明 0.899。** 本文不以该结论为引用。已经独立展开一个沿 Wu04 Lemma 9.1/9.2 的有效有限组合：使用移动正二重项和固定第九筛门，而不要求先证明旧 full-U6 接口。它与作者最后实际使用的第六项积分支持相容。其后第一个尚不能由已核适用定理推出的解析命题，是 §6 的高素数区双筛下界；此外，最后的有向数值输入尚未齐备。

本文的“推导”指下文给出论证；“引用”指明确使用所列文献结果，不表示本阶段独立重证；“打印数”不是已认证数值。本文没有进行 Lean、Lake、gate、构建、内核检查或新的数值求积、扫描、优化。

## 1. 目标、对象与来源

以 Wu08 §1 的定义为准：
\[
 D_{1,2}(N)=\#\{p\leq N:p\text{ 为素数},\ \Omega(N-p)\leq2\},
 \qquad \Omega(1)=0,
\]
\[
 C_N=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
       \prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2},
 \qquad \Theta(N)=C_N\,\frac N{\log^2N}.
\]
要证明的量词是：存在 \(N_0\)，对每个偶数 \(N\geq N_0\)，
\[
                         D_{1,2}(N)\geq0.899\Theta(N).                 \tag{T}
\]
素数变量 \(p\) 与补数 \(N-p\) 一一对应；这不是去掉素数指示函数的整数计数，也不要求补数恰有两个素因子。归一化不是 \(2C_NN/\log^2N\)。

目标定位：Li–Liu 正文 Theorem 1.1 是 \(1+1.9\)，备注是 \(1+1.894\)；1.8938 是本项目后期未验证的加强，不是 Wu08 原定理。本文只负责 (T)，不证明 M3 负责的后半桥。

主要来源均为本地原文：

| 简称 | 来源及本文实际使用位置 |
|---|---|
| Wu08 | `sources/Wu08.tex`：§1 计数与定理；§2 Lemma 2.1/2.2；§3 双筛类及 \(H,h\)；§4 Propositions 4.1–4.4；§5 全部积分与打印数 |
| Wu04 | `sources/Wu04.tex`：§2 筛法、Pan–Ding 与 Fouvry 输入；§3–§7 双筛及反馈；§9 Lemma 9.1/9.2；§10 尤其 (10.10)–(10.12) 的实际 switching 估计 |
| 期刊核对 | `sources/wu08-journal.txt`，尤其 pp. 378–383：Propositions 4.2/4.3、§5 第六项分区；它没有消除 §6 所述适用条件问题 |
| Fouvry | `sources/fouvry-1987-original.txt`，Corollary 2(i) 及其系数和 Siegel–Walfisz 假设 |
| Li–Liu | `parent-fixes/liliu-source-target/arxiv-2606.05224v1-mathtext.txt`，开头的 Theorem 1.1、备注及 Wu 引用 |

以上路径均相对于 `research/wu2008/`。下文引述公式编号比 TeX 行号更稳定。

固定作者参数，始终不作优化：
\[
 \alpha=\frac{100}{1327},\qquad \beta=\frac{25}{206},\qquad
 \sigma=\frac12-3\alpha=\frac{727}{2654},\qquad
 \lambda=\frac12-2\alpha=\frac{927}{2654}.
\]
记
\[
 z=N^\alpha,\quad w=N^\beta,\quad u=N^\sigma,\quad
 v=N^{1/3},\quad V=N^\lambda,\quad B(a)=\sqrt{N/a}.
\]
直接有理数运算给出
\[
 0<\alpha<\beta<\tfrac16<\tfrac14<\sigma<\tfrac13,\quad
 3\alpha+\beta<\tfrac12,\quad 3\alpha-\beta<\tfrac16,
\]
\[
 2\beta<\lambda,\quad \beta<2\alpha,\quad
 \frac23+\sigma+\beta-1=\frac{25403}{410043}>0.             \tag{1.1}
\]
最后一个严格不等式将保证固定第九筛门的商为素数或 1。

## 2. 无歧义的商筛，以及可以支付的例外

**定义。** 对素数标签的乘积 \(d\)，令
\[
 Q(d;t)=\#\{p\leq N:p\text{ 素},\ d\mid n=N-p,\ 
              \ell\mid n/d,\ \ell\nmid N\Rightarrow \ell\geq t\}.
                                                               \tag{2.1}
\]
标签都与 \(N\) 互素；空商 \(n/d=1\) 被计入。筛乘积使用严格门 \(\ell<t\)。
本节先在
\[
              (n,N)=1,\quad P^-(n)\geq z,\quad n\text{ 平方自由}   \tag{2.2}
\]
上作恒等式；\(n=1\) 按惯例满足粗性和平方自由性。

**记号辨析。** Wu04 §2 的字面 \({\cal A}_d\) 是整除子列，Wu08 又把筛乘积端点写成 \(\ell\leq z\)。不能据此把所有
\(S({\cal A}_d;{\cal P}(M),t)\) 无条件认作 (2.1)：若一个已选标签小于 \(t\) 而不整除 \(M\)，未缩放子列会被它筛掉，商子列则不会。
本文的有限组合完全按 (2.1) 重新证明，不以这种含混替换为证明步骤。
用于双筛的 \({\cal P}(dN)\) 排除了全部已选标签，故在 (2.2) 上商筛与该实际双筛序列确实相同。负项则在 §8 明确写成素数输出的乘积计数，不凭同名 \(S\) 认定来源身份。

**推导：例外费用。**

若 \((N-p,N)>1\)，则 \(p\mid N\)，只有 \(O(\log N)\) 个指标。
若一个有贡献的补数不满足平方自由性，则除上述指标外，必有某个
\(\ell\geq z\) 满足 \(\ell^2\mid n\)，因而指标总数至多
\[
 \sum_{m\geq z}\frac{N}{m^2}=O(N/z).
                                                               \tag{2.3}
\]
所有选中标签至少为 \(z\)，每个 \(n<N\) 的此类素因子数按重数至多
\(\lfloor1/\alpha\rfloor\)。本文固定阶的标签权重因此有只依赖 \(\alpha\) 的常数上界。(2.3) 可以支付全部重复标签，而不是每项分别损失一个未控重数。
不粗的补数不进入以下商筛项，除非已经落在 \((n,N)>1\) 的例外内。

固定幂次筛门的严格/闭端点若恰为素数，只需计入该素数整除补数的指标，费用 \(O(N/z)\)。本文移动乘积门从定义起始终取 \(cd<V\)，没有将它与 \(cd\leq V\) 偷换。解析积分的边界是零测集，其极限处理在 §4 说明。

所以从 (2.2) 返回全部实际指标的总费用为 \(O_\alpha(N^{1-\alpha})\)。
由于 \(C_N\) 有正的绝对下界，该费用为 \(o(\Theta(N))\)。

## 3. 承重有限组合：固定第九筛门的 Wu04 路线

本节是**同结论组合替代的有限部分**，不是 Wu08 字面 Lemma 2.2 的补全。
它改用 Wu04 的固定第九筛门，并保留作者移动正二重项；计数对象、最终参数、归一化与负四重域不变。

### 3.1 两倍 lower weight 的逐补数证明

对 \(z_0\leq t\leq N^{1/3}\)，定义
\[
\begin{aligned}
 L(z_0,t)&=\sum_{z_0\leq a<t}Q(a;z_0),\\
 A(z_0,t)&=\sum_{t\leq a<b<B(a)}Q(ab;b),\\
 B(z_0,t)&=\sum_{z_0\leq a<t\leq b<B(a)}Q(ab;b),\\
 C(z_0,t)&=\sum_{z_0\leq a<b<c<t}Q(abc;b).
\end{aligned}
\]
所有字母标签均为素数。令
\[
 W(z_0,t)=2Q(1;z_0)-L(z_0,t)-2A(z_0,t)-B(z_0,t)+C(z_0,t).
                                                               \tag{3.1}
\]
这是 Wu04 Lemma 9.1、Wu08 Lemma 2.1 的 lower-weight 结构。

在一个平方自由、\(z_0\)-粗补数 \(n\) 上，令 \(r\) 为小于 \(t\) 的素因子数，\(k=\Omega(n)\)。
若 \(k\geq3\)，写最小两个因子为 \(q_1<q_2\)，则
\(q_1q_2^2<n<N\)。商筛条件使两标签惩罚只能选这两个最小因子。

* \(r=0\)：\(A\) 恰计一次，权为 \(2-2=0\)。这也包括 \(k\geq4\)，不只三因子。
* \(r=1\)：\(L=1\)，\(B\) 恰计一次，权为 \(2-1-1=0\)。
* \(r\geq2\)：两标签惩罚均为零；\(C\) 的前两个标签必须是
  \(q_1,q_2\)，第三标签可选其余 \(r-2\) 个小因子，故权为 \(2-r+(r-2)=0\)。

若 \(k\leq2\)，\(C=0\)，其余扣项非负，权至多 2。
特别地，单位补数的权为 2；素补数并未被删除。
这就逐指标证明
\[
                    W(z_0,t)\leq2D_{1,2}(N)+O(N^{1-\alpha}).       \tag{3.2}
\]

### 3.2 十一槽实际计数

以下是本组合的槽，而非无说明重命名的旧接口：
\[
\begin{aligned}
 U_1&=Q(1;z),& U_2&=Q(1;w),\\
 U_3&=\sum_{z\leq a<v}Q(a;z),&
 U_4&=\sum_{z\leq a<u}Q(a;z),\\
 U_5&=\sum_{z\leq a<b<w}Q(ab;z),&
 K_6&=\sum_{\substack{z\leq c<w\leq d<u\\cd<V}}Q(cd;z),\\
 U_7&=\sum_{u\leq a<b<B(a)}Q(ab;b),&
 U_8&=\sum_{z\leq a<v\leq b<B(a)}Q(ab;b),\\
 J_9&=\sum_{w\leq a<u\leq b<B(a)}Q(ab;v),\\
 Q_{10}&=\sum_{z\leq a<b<c<d<w}Q(abcd;b),\\
 Q_{11}&=\sum_{\substack{z\leq a<b<c<w\leq d\\cd<V}}Q(abcd;b).
\end{aligned}                                                     \tag{3.3}
\]
在 \(Q_{11}\) 中 \(d<V/c\leq V/z=u\)，故不需要另一个 \(d<u\) 截断。
\(J_9\) 的门是 \(v=N^{1/3}\)，**不是**
\(\sqrt{N/(ab)}\)。我们不声称两者逐项相等。

将证明
\[
\boxed{\quad
4D_{1,2}(N)\ \geq\
3U_1+U_2-U_3-U_4+U_5+K_6
 -2U_7-U_8-J_9-Q_{10}-Q_{11}
 -O(N^{1-\alpha}).\quad}                                         \tag{3.4}
\]

### 3.3 正二重项先分区，不向回加未付尾部

在好补数上，反复按商的最小素因子使用 Buchstab 恒等式，得到
\[
 2Q(1;w)=Q(1;z)+Q(1;w)
          -\sum_{z\leq a<w}Q(a;z)+U_5-T_0,
\]
\[
 T_0=\sum_{z\leq a<b<c<w}Q(abc;a).                                \tag{3.5}
\]
另外
\[
 -L(w,u)=-\sum_{w\leq d<u}Q(d;z)
            +\sum_{z\leq c<w\leq d<u}Q(cd;c).
                                                               \tag{3.6}
\]
后一正和的每一项非负，故可以**先**只保留 \(cd<V\)。在所保留域再次展开：
\[
 \sum_{\substack{z\leq c<w\leq d<u\\cd<V}}Q(cd;c)=K_6-T_m,\qquad
 T_m=\sum_{\substack{z\leq a<b<w\leq c<u\\bc<V}}Q(abc;a).
                                                               \tag{3.7}
\]
这是合法的下界方向，不是从“某个负尾部不超过正尾部”倒推出尾部可免费加回。
所有被保留的商仍可为 1 或任意较大的粗数。

### 3.4 第九项：固定门的精确有号展开

把 \(B(w,u)\) 中 \(b<v\) 和 \(b\geq v\) 分开，在同一个门 \(v\) 作 Buchstab：
\[
 B(w,u)=J_9+T_h-T_{\geq v},
\]
\[
 T_h=\sum_{w\leq a<u\leq b<c<v}Q(abc;c),\qquad
 T_{\geq v}=\sum_{w\leq a<u,\ v\leq b<c<B(a)}Q(abc;b)\geq0.
                                                               \tag{3.8}
\]
第一域原来的 \(b<B(a)\) 自动满足，因为 \(a<u<v\) 且
\(av^2<N\)。第二域由原先 \(v\leq c<b<B(a)\) 交换后两个标签得到；
没有改换实际素数 \(p\)，也没有消除其指示函数。
重复标签在 (2.3) 中支付。

### 3.5 三重项抵消及负四重域的产生

\(C(z,v)\) 包含以下三个互不相交的标签子域：
\[
 z\leq a<b<c<w;\qquad
 z\leq a<b<w\leq c<u,\ bc<V;\qquad
 w\leq a<u\leq b<c<v.
                                                               \tag{3.9}
\]
在第一域，\(Q(abc;a)-Q(abc;b)\) 按最小新素因子展开，恰得到
\(Q_{10}\) 的有序四标签；在第二域，同一展开恰得到
\(Q_{11}\)：新标签插入前两个标签之间，原最后两标签的条件
\(bc<V\) 正好成为四标签的 \(cd<V\)。没有遗漏排列系数。
在第三域，\(Q(abc;b)\geq Q(abc;c)\)，足以支付 \(T_h\)。
所以
\[
                  C(z,v)-T_0-T_m-T_h\geq-Q_{10}-Q_{11}.           \tag{3.10}
\]
未用的 \(C(z,v)\) 子域、第三域筛门差、\(C(w,u)\) 和
\(T_{\geq v}\) 都是非负量；可保留，但证明 (3.4) 不需其主项。

最后 \(A(z,v)=0\)，因为 \(a\geq v,\ b>a\) 会给出 \(ab^2>N\)。
把 (3.5)–(3.10) 代入 \(W(z,v)+W(w,u)\)，再用 (3.2)，就得到 (3.4)。
这完成了本节有限组合的证明，不以任何剩余总量付款命题为假设。

## 4. 从实际筛序列到归一化积分

### 4.1 引用的分布与线性筛

对偶数 \(N\) 的序列 \(\{N-p:p\leq N\}\)，模 \(d\) 的主项是
\(\operatorname{li}(N)/\varphi(d)\)，在 \((d,N)=1\) 上成立。
使用 Bombieri–Vinogradov 的加权标准推论：每个固定 \(A,K>0\) 有 \(B\)，
对 \(D\leq N^{1/2}/(\log N)^B\)，相应 AP 误差的
\(\mu^2(d)\tau_K(d)\)-加权绝对和为 \(O_{A,K}(N/\log^A N)\)。
这是 Wu04 §2 的实际输入，不是逐模数误差界。

固定 \(\delta>0\)，先取 \(Q=N^{1/2-\delta}\)，而非直接把筛层级设为
\(N^{1/2}\)。标准一维线性筛的函数满足
\[
 A(s)=\frac{sF(s)}{2e^\gamma},\qquad a(s)=\frac{sf(s)}{2e^\gamma},
\]
\[
 A(s)=1\ (0<s\leq3),\quad a(s)=0\ (0<s\leq2),\quad
 a(s)=\log(s-1)\ (2<s\leq4),
\]
\[
                  A'(s)=\frac{a(s-1)}{s-1},\qquad
                  a'(s)=\frac{A(s-1)}{s-1}
                                                               \tag{4.1}
\]
在各自后续区间给出延迟递推。
对固定素数标签乘积 \(d\)，筛商的层级是 \(Q/d\)。

双筛引用 Wu04 §3 定义、Propositions 1–4 及 Wu08 §3：
\[
\begin{aligned}
 \Phi(N,\eta,s)&=\sum_d\eta(d)
 S({\cal A}_d;{\cal P}(dN),(Q/d)^{1/s}),\\
 {\cal T}(N,\eta)&=
 4\operatorname{li}(N)\sum_d
       \frac{\eta(d)C_{dN}}{\varphi(d)\log(Q/d)}.
\end{aligned}                                                     \tag{4.2}
\]
这里 \(\eta\) 属于原文的短素数区间卷积类 \({\cal U}_k(N)\)，不是任意非负权：
若区间上端按 \(V_1\geq\cdots\geq V_i\) 排列，必须有
\[
 V_1\cdots V_{j-1}V_j^2\leq Q\quad(1\leq j\leq i),\qquad
 V_i\geq W_k,
                                                               \tag{4.3}
\]
并使用原文的短区间比例和 \(i\leq k\) 条件。
具体量词是先固定误差容许量及严格的指数内区，再选择 \(k\)、足够小的
\(\delta>0\) 和足够大的 \(N_0\)；对所有偶数 \(N\geq N_0\) 及该类权统一有
\[
 \Phi\leq(A(s)-H(s)+\varepsilon){\cal T},\qquad
 \Phi\geq(a(s)+h(s)-\varepsilon){\cal T}.                          \tag{4.4}
\]
严谨地说，先用 \(H_{k,N_0},h_{k,N_0}\)，再按原定义取极限获得 (4.4) 的
\(\varepsilon\) 版本。不能因最终记号 \(H,h\) 而略去类条件。

有限个严格内区短箱可统一取阈值；随后让箱宽、被删边界条带和
\(\delta\) 趋于零。本文积分域离 \(x=0,y=0,\frac12-x-y=0\) 均有正距离，
核有界，边界条带积分趋零。这个过程只能跨零测边界，不能跨 §6 的开楔形域。

### 4.2 系数与 Jacobian 的推导

对平方自由、与 \(N\) 互素的标签 \(d\)，有精确恒等式
\[
 \frac{C_{dN}}{\varphi(d)}=\frac{C_N}{\prod_{\ell\mid d}(\ell-2)}.
                                                               \tag{4.5}
\]
利用素数定理和分部求和，(4.2) 因而产生如下两种核：
\[
 4\int\frac{A((1/2-x)/\alpha)-H((1/2-x)/\alpha)}
                {x(1/2-x)}\,dx
 =8\int\frac{A(s)-H(s)}{s(1-2\alpha s)}\,ds,
                                                               \tag{4.6}
\]
\[
 4\iint\frac{a((1/2-x-y)/\alpha)+h((1/2-x-y)/\alpha)}
                {xy(1/2-x-y)}\,dx\,dy
 =8\int dx\int\frac{a(s)+h(s)}{xs(1-2x-2\alpha s)}\,ds.
                                                               \tag{4.7}
\]
所以双标签核确实含 \(s^{-1}\)。Wu08 Proposition 4.2 打印的积分少一个
\(u\)，而 §5 的 \(F_5,G_5\) 有它；本文使用由 (4.2)、变量代换直接决定的
(4.7)，不默默照搬那个缺因子的式子。

## 5. 前五项与实际第六项的系数

将经典部分记为 \(C_i\)，另将增益记为 \(G_i\)，避免与原文已经吸收增益的
\(F_i\) 混淆。令 \(s(x,y)=(1/2-x-y)/\alpha\)，则
\[
\begin{aligned}
 C_1&=8a(1/(2\alpha)),&C_2&=8a(1/(2\beta)),&
 G_2&=8h(1/(2\beta)),\\
 C_3&=8\int_{1/(6\alpha)}^{1/(2\alpha)-1}
                  \frac{A(s)}{s(1-2\alpha s)}\,ds,\\
 C_4&=8\int_3^{1/(2\alpha)-1}\frac{A(s)}{s(1-2\alpha s)}\,ds,\\
 C_5&=4\int_\alpha^\beta\int_x^\beta
                  \frac{a(s(x,y))}{xy(1/2-x-y)}\,dy\,dx,\\
 G_5&=4\int_\alpha^\beta\int_x^\beta
                  \frac{h(s(x,y))}{xy(1/2-x-y)}\,dy\,dx.
\end{aligned}                                                     \tag{5.1}
\]
丢弃 \(8h(1/(2\alpha))\geq0\)，而不把它当作未知补款。
Wu08 TeX 中 \(G_2\) 的一行混入了 \(a\) 和未绑定的 \(i\)；期刊 §5(5.2) 的
\(G_i=8h(1/(2\kappa_i))\) 以及 (4.2) 都确定上述含义。

引用 Wu08 Propositions 4.1、4.2，并使用 §4 已核的核，可得
\[
 U_1\geq(C_1-o(1))\Theta,\quad
 U_2\geq(C_2+G_2-o(1))\Theta,\quad
 U_5\geq(C_5+G_5-o(1))\Theta.                                    \tag{5.2}
\]
适用检查：第五项有 \(\beta<1/6\)、
\(\alpha+2\beta<1/2\)，全部两标签属于 (4.3)。

对第三、四项，只有 \(x<1/4\) 部分直接使用完整 \(H\)。
定义
\[
 G_4=8\int_{1/(4\alpha)}^{1/(2\alpha)-1}
                \frac{H(s)}{s(1-2\alpha s)}\,ds,\qquad
 G_3=G_4+8\int_{1/(6\alpha)}^{2.9}
                \frac{\psi(s)}{s(1-2\alpha s)}\,ds,              \tag{5.3}
\]
其中 \(\psi\) 是下列固定阶梯函数：
\[
\begin{array}{c|ccccccc}
s\text{ 区间}&[1327/600,2.3]&[2.3,2.4]&[2.4,2.5]&[2.5,2.6]&[2.6,2.7]&[2.7,2.8]&[2.8,2.9]\\ \hline
\psi(s)&\Psi_2(2.3)&\Psi_2(2.4)&\Psi_2(2.5)&\Psi_1(2.6)&\Psi_1(2.7)&\Psi_1(2.8)&\Psi_1(2.9)
\end{array}
\]
这里每个 \(\Psi\) 使用 §7 指定的全部辅助参数。
Wu08 Proposition 4.4 是针对大于 \(N^{1/4}\) 的**单素数**卷积权的简化双筛上界；
其条件 \(1/4\leq1/2-s\alpha<\phi\) 在这些区间成立。
不是将它当成任意双标签下筛。
剩下的单标签区间只使用经典上筛，由此
\[
                   U_3\leq(C_3-G_3+o(1))\Theta,\qquad
                   U_4\leq(C_4-G_4+o(1))\Theta.                  \tag{5.4}
\]
此处引用的承重结果是 Proposition 4.4 的计数上界，不是 (T)。
其证明里负系数的 \(\Omega_2\) 必须用下界；Wu04 的对应 (5.2) 给的是
\(\geq\)，不能把 Wu08 那一处印成同向上界的符号拿来相减。

令
\[
 {\cal R}=\{(x,y):\alpha\leq x\leq\beta,\ \beta\leq y\leq\sigma,\
                                      x+y\leq\lambda\},
\]
\[
 C_6=4\iint_{\cal R}\frac{a(s(x,y))}{xy(1/2-x-y)}\,dx\,dy,\qquad
 \widehat G_6=4\iint_{\cal R}\frac{h(s(x,y))}{xy(1/2-x-y)}\,dx\,dy.
                                                               \tag{5.5}
\]
**推导：经典第六项无需 full U6。**
在原矩形但不在 \({\cal R}\) 内，\(s(x,y)<2\)，因而 \(a(s)=0\)。
所以 (5.5) 的 \(C_6\) 与作者原矩形的经典 \(C_6\) **完全相同**。
对 \({\cal R}\) 先用 \(x+y<1/2-\delta-2\alpha\) 的线性下筛，再作 §4 的极限，
就得到无额外双筛假设的
\[
                            K_6\geq(C_6-o(1))\Theta.             \tag{5.6}
\]
这一步不使用 \(H,h\) 或某个未付总量。

## 6. 作者最终 \(G_6\) 的真实支持，以及首个未证解析箭头

### 6.1 最后数值公式确实只用移动域

令 \(L=1/2-2\beta\)。Wu08 §5 最初定义的 \(G_6\) 使用两块：
\[
 [\alpha,\beta]\times[\beta,L],\qquad
 [\alpha,3\alpha/2]\times[L,\sigma].
                                                               \tag{6.1}
\]
它随后用于打印下界的积分从 \(s=2\) 开始。
在 \({\cal R}\) 内若 \(y>L\)，
\[
 x\leq\lambda-y<\lambda-L=2\beta-2\alpha<3\alpha/2.
                                                               \tag{6.2}
\]
故 \({\cal R}\) 包含在 (6.1) 中；反之 (6.1) 与 \(s\geq2\) 的交正是
\({\cal R}\)。因此作者最后使用的第六项收益支持是 (5.5)，而不是必须保留的
\(s<2\) 尾部。

为独立核对积分，把 \(S=1/2-\alpha s\)，
\[
 r_0=(1/2-2\beta)/\alpha,\qquad r_1=(1/2-\alpha-\beta)/\alpha.
\]
当 \(s\geq2\)，固定 \(x+y=S\) 的截面为
\(\alpha\leq x\leq\min(\beta,S-\beta)\)：下门
\(S-\sigma=\alpha(3-s)\leq\alpha\)。积分
\(\int dx/[x(S-x)]=S^{-1}\log(x/(S-x))\) 给出
\[
\begin{aligned}
 \widehat G_6={}&
 8\int_2^{r_0}\frac{h(s)}{s(1-2\alpha s)}
          \log\frac{\beta(S-\alpha)}{\alpha(S-\beta)}\,ds\\
 &+8\int_{r_0}^{r_1}\frac{h(s)}{s(1-2\alpha s)}
          \log\frac{(S-\alpha)(S-\beta)}{\alpha\beta}\,ds .
\end{aligned}                                                     \tag{6.3}
\]
这逐项解释了原文最后 \(g_6^i\) 的两个对数核和分割点；没有新的求积。
把 \(h\) 换成 \(a\) 也给出 \(C_6\) 的同一截面公式。
所以 (3.4) 在有限组合层面可以承载作者最后实际使用的经典项及这份收益，
无需先补旧 full-U6 母式。

### 6.2 不能由 Proposition 4.3 推出的部分

**仍未证明**
\[
             K_6\geq(C_6+\widehat G_6-o(1))\Theta.                \tag{A6}
\]
Wu08 Proposition 4.3 的完整条件是
\[
 0<\phi_1<\phi_2\leq\phi_3<\phi_4<1/4,\quad
 2\phi_2+\phi_4<1/2,\quad \phi_2+\phi_4+\alpha\leq1/2.
                                                               \tag{6.4}
\]
原 §5(a) 的上门 \(L>1/4\)，§5(b) 的上门 \(\sigma>1/4\)；
作者写的“前两块由 Proposition 4.3”并非已经检查过 (6.4) 的应用。
这是 TeX 与期刊都有的适用性问题，不是旧 Lean 对象强加的条件。

在 \({\cal R}\cap\{y<1/4\}\) 内，其他条件没有问题：
\[
 2x+y\leq\beta+\lambda<1/2,\qquad x+y+\alpha\leq1/2-\alpha.
\]
短箱分割、(4.4) 和极限给出该低区完整的 \(a+h\) 下界。
但剩余是正面积的开楔形，不是端点：
\[
 {\cal R}_{\rm hi}
 =\left\{(x,y):\alpha<x<\frac{527}{5308},\
                              \frac14<y<\lambda-x\right\}.       \tag{6.5}
\]
这里 \(2<s(x,y)<927/400\)。精确需要的实际计数是
\[
 K_{\rm hi}=
 \sum_{\substack{N^\alpha<c<N^{527/5308}\\
                  N^{1/4}<d<N^\lambda/c}}
                                  Q(cd;N^\alpha).
                                                               \tag{6.6}
\]
它的两个标签均为素数、与 \(N\) 互素，商仍允许为 1 或任何粗数。
所缺命题的量词为：对每个 \(\varepsilon>0\)，存在 \(N_0(\varepsilon)\)，
对所有偶数 \(N\geq N_0\)，
\[
 K_{\rm hi}\geq
 \left\{4\iint_{{\cal R}_{\rm hi}}
       \frac{a(s(x,y))+h(s(x,y))}{xy(1/2-x-y)}\,dx\,dy
                  -\varepsilon\right\}\Theta(N).                \tag{A6-hi}
\]
标准 BV 加线性筛给出其中的 \(a\)，不产生额外 \(h\)。
完整双筛的卷积类在这里违反第一条 \(V_1^2\leq Q\)，因为最大标签
\(d>N^{1/4}\)。Proposition 4.4 则是单标签上界，不是 (A6-hi)。
把标签顺序倒置也无用，(4.3) 要按大小重排。

Wu04 的移动正二重母式解决的是有限组合，而不自动扩大该双筛权类。
目前已读来源中没有核到能直接供给 (A6-hi) 的定理，也没有在本文推导出
足量的跨指标替代收益。因此这就是**本条已修复有限组合路线的首个未证解析箭头**。
它是原文 §5 简写应用需要补充论证之处，不是一个原定理反例。

## 7. \(H,h,\Psi\) 的强度从哪里来

### 7.1 功能不等式与表格的逻辑地位

引用 Wu04 Propositions 1、2：
\[
 H,h\geq0,\quad H\text{ 在 }[1,10]\text{ 非增},\quad
 h\text{ 在 }[2,10]\text{ 非增},
\]
\[
 h(s)\geq h(s')+\int_{s-1}^{s'-1}\frac{H(t)}t\,dt
                      \quad(2\leq s\leq s'\leq10).               \tag{7.1}
\]
初始 \(H(2.2),\ldots,H(3.0)\) 来自 Wu04 §7 的九维正核反馈：
\[
                         {\bf H}\geq {\bf B}+{\bf A}{\bf H}.     \tag{7.2}
\]
前四行使用 Proposition 4 的 \(\Xi_2\)，后五行使用 Proposition 3 的
\(\Xi_1\)；列区间依次为
\([1,2.2],[2.2,2.3],\ldots,[2.9,3]\)，
\[
 A_{ij}=\int_{\text{第 }j\text{ 格}}\Xi_{\nu(i)}(t,s_i)\,dt,
 \quad B_i=\Psi_{\nu(i)}(s_i).
                                                               \tag{7.3}
\]
这里引用的是这些明确功能不等式，不是最终 0.899。
若要把一个小数向量认作严格下界，需要核实正核、带方向的
\({\bf A},{\bf B}\) 界，并用有限正迭代或有证明的逆矩阵正性完成 (7.2) 的消费。
原文 Maple 输出不能自行替代这个步骤；本阶段没有重新求解矩阵。

Wu04 初始打印下界为
\[
 (.0223939,.0217196,.0202876,.0181433,.0158644,
  .0129923,.0100686,.0078162,.0072943).
                                                               \tag{7.4}
\]
Wu08 用 Wu04 Lemma 6.1 将其扩展到 \(H(3.1),\ldots,H(4.9)\)。
其核可明确写为
\[
 \Sigma(a,b,c)=\int_a^b\frac{\log(c/(t-1))}{t}\,dt,\qquad
 \Sigma_0(t)=\frac{\Sigma(3,t+2,t+1)}{1-\Sigma(3,5,4)},
\]
\[
 H(s')\geq\int_1^3 H(t)\left\{
 \frac{\Sigma_0(t)}t\log\frac4{s'-1}
 +\frac{{\bf1}_{[s'-2,3]}(t)}t\log\frac{t+1}{s'-1}
                                      \right\}\,dt
                       \quad(3\leq s'\leq5).                   \tag{7.5}
\]
再由 (7.1)、\(h(6)\geq0\)，得
\(h(s)\geq\int_{s-1}^{5}H(t)\,dt/t\)（这里使用的 \(s\leq6\)）。
用非增 \(H\) 的右端阶梯下界，丢掉尚无表值的正尾段，才产生 Wu08 的
\(h\) 表和各 \(G_i\) 的下界。

例如 \(1/(2\beta)=4.12<4.2\)，所以正确的方向是
\[
           G_2\geq8\left(h(4.2)+\int_{3.12}^{3.2}H(t)\frac{dt}t\right).
                                                               \tag{7.6}
\]
原 §5 把积分上下限印反；本文的正方向由 (7.1) 推出。我们没有据此声称
原打印数 .005283 已重新认证。

### 7.2 实际采用的 \(\Psi\) 参数

\(\Psi_1,\Psi_2\) 是 Wu04 Lemmas 5.1、5.2 的积分功能，不是可任填的数。
固定参数如下；最后一列仍仅为作者打印值：

| \(s\) | \(s'\) | \(k_1\) | \(k_2\) | \(k_3\) | 功能及打印值 |
|---|---|---|---|---|---|
| 2.2 | 4.54 | 3.53 | 2.90 | 2.44 | \(\Psi_2\)：.015826357 |
| 2.3 | 4.50 | 3.54 | 2.88 | 2.43 | \(\Psi_2\)：.015247971 |
| 2.4 | 4.46 | 3.57 | 2.87 | 2.40 | \(\Psi_2\)：.013898757 |
| 2.5 | 4.12 | 3.56 | 2.91 | 2.50 | \(\Psi_2\)：.011776059 |
| 2.6 | 3.58 | — | — | — | \(\Psi_1\)：.009405211 |
| 2.7 | 3.47 | — | — | — | \(\Psi_1\)：.006558950 |
| 2.8 | 3.34 | — | — | — | \(\Psi_1\)：.003536751 |
| 2.9 | 3.19 | — | — | — | \(\Psi_1\)：.001056651 |

前四行的有理参数满足
\[
 5\geq s'\geq3\geq s\geq2,\quad s'-s'/s\geq2,\quad
 s\leq k_3<k_2<k_1\leq s'.
\]
Wu04 Proposition 4 额外使用的九个 \(\alpha_j\in[1,3]\) 及
\(\alpha_1<\alpha_4,\alpha_5<\alpha_8\) 也由这些固定有理数直接核算满足。
这里的 \(k_i\) 与本文 \(\alpha,\beta\) 无关。

为固定数值对象，记 \(J(b)=\int_2^{b-1}\log(t-1)\,dt/t\)。则
\[
 \Psi_1=-J(s')+\frac12\int_{1-1/s}^{1-1/s'}
               \frac{\log(s't-1)}{t(1-t)}\,dt-I_1,
\]
\[
 I_1=\sup_{\phi\geq2}
 \int_{1/s'\leq t\leq u\leq v\leq1/s}
     \frac{\omega((\phi-t-u-v)/u)}{tu^2v}\,dt\,du\,dv.
                                                               \tag{7.7}
\]
\(\Psi_2\) 的完整负包是
\[
\begin{aligned}
 \Psi_2={}&-\tfrac25J(s')-\tfrac25J(k_1)-\tfrac15J(k_2)
 +\tfrac15\int_{1-1/s}^{1-1/s'}\frac{\log(s't-1)}{t(1-t)}\,dt\\
 &+\tfrac15\int_{1-1/k_3}^{1-1/k_1}
             \frac{\log(k_1t-1)}{t(1-t)}\,dt
 -\tfrac25\sum_{i=9}^{21}I_{2,i}.
\end{aligned}                                                     \tag{7.8}
\]
所有十三项均取各自积分对 \(\phi\geq2\) 的上确界，不能先固定一个 \(\phi\)
或只保其中几项。其域完整固定如下：

| \(i\) | \({\cal D}_{2,i}\) |
|---|---|
| 9 | \(1/k_1\leq t\leq u\leq v\leq1/k_3\) |
| 10 | \(1/k_1\leq t\leq u\leq1/k_2\leq v\leq1/s\) |
| 11 | \(1/k_1\leq t\leq1/k_2\leq u\leq v\leq1/k_3\) |
| 12 | \(1/s'\leq t\leq u\leq1/k_1,\ 1/k_3\leq v\leq1/s\) |
| 13 | \(1/s'\leq t\leq1/k_1\leq u\leq1/k_2\leq v\leq1/s\) |
| 14 | \(1/s'\leq t\leq1/k_1,\ 1/k_2\leq u\leq v\leq1/s\) |
| 15 | \(1/k_1\leq t\leq1/k_2\leq u\leq1/k_3\leq v\leq1/s\) |
| 16 | \(1/k_2\leq t\leq u\leq v\leq w\leq1/k_3\) |
| 17 | \(1/k_2\leq t\leq u\leq v\leq1/k_3\leq w\leq1/s\) |
| 18 | \(1/k_2\leq t\leq u\leq1/k_3\leq v\leq w\leq1/s\) |
| 19 | \(1/k_1\leq t\leq1/k_2,\ 1/k_3\leq u\leq v\leq w\leq1/s\) |
| 20 | \(1/k_2\leq t\leq1/k_3\leq u\leq v\leq w\leq x\leq1/s\) |
| 21 | \(1/k_3\leq t\leq u\leq v\leq w\leq x\leq y\leq1/s\) |

对 9–15，核为 \(\omega((\phi-t-u-v)/u)/(tu^2v)\)；
对 16–19 为 \(\omega((\phi-t-u-v-w)/v)/(tuv^2w)\)；
20 为 \(\omega((\phi-t-u-v-w-x)/w)/(tuvw^2x)\)；
21 为 \(\omega((\phi-t-u-v-w-x-y)/x)/(tuvw x^2y)\)。
变量仅在本表内使用。

标准 Buchstab 函数由 \(\omega(t)=1/t\)（\(1\leq t\leq2\)）及
\((t\omega(t))'=\omega(t-1)\) 决定。若某个 \(\Psi_2\) 积分的参数落在
\(t<1\)，非单位粗数密度应取零，单位商须另行处理，不能任用一个程序对负参数的延拓。
本文没有认证这些上确界或其单位商处理与现有全部数值证书的一致性。
因此 (7.4) 及上述 \(\Psi\) 打印值仍列为待有向认证的输入，而非已付数值。

## 8. 负项解析估计：对象、原引用与系数

### 8.1 三个负两标签项为什么是 switching 对象

在 (2.2) 上：

* \(U_7\)：若 \(n/(ab)\) 非素且非 1，其粗性至少给出
  \(n\geq ab^3\geq u^4>N\)，矛盾。
* \(U_8\)：同理 \(n\geq ab^3\geq zv^3>N\)，矛盾。
* \(J_9\)：其商 \(v\)-粗，若有至少两个因子，则
  \(n\geq abv^2\geq wuv^2>N\)，由 (1.1) 矛盾。

所以每个商均为素数或 1。单位商不能直接删去，但在这些标签域
\(ab<N^{2/3}\)，每个补数只有有界标签重数，单位商费用
\(O(N^{2/3})=o(\Theta)\)。于是每个负项都有实际三素数乘积
\(n=abr\)、输出素数 \(p=N-abr\) 的 switching 上界。
特别是 \(J_9\) 可以在上界中放宽 \(r\geq v\)，但不能在有限母式中据此改变筛门。

这里使用 Wu04 §10 的 Pan–Ding switching 估计（基础结果为其 Lemma 2.3）：
固定 \(\eta>0,A>0\)，存在 \(B\)，对有界长系数、长变量
\(m\leq X^{1-\eta}\)，在 \(q\leq X^{1/2}/\log^B X\) 上，
\(mr\equiv a\pmod q\) 的素数变量误差有加权平均 \(O(X/\log^A X)\)，
均匀于互素剩余类及文献规定的截断端点。
本处 \(m=ab\leq N^{2/3}\)，固定标签重数可先除以常数，
例如取 \(\eta=1/6\) 有严格余量。截断 \(b<B(a)\)、商的下门及 \(abr<N\)
必须保留在该端点版本或短箱分割中。
这就是 Wu04 (10.10)、(10.11) 用到的实际计数，而不是对未指明的粗数总量应用 BV。

把输出素数用一维上筛控制，半层级给出归一化因子 8。
令 \(x=\log a/\log N,\ y=\log b/\log N\)。素数商的连续主质量的内积分是
\[
 \int_l^{(1-x)/2}\frac{dy}{y(1-x-y)}
       =\frac1{1-x}\log\frac{1-x-l}{l}.                           \tag{8.1}
\]
这保留 \(a,b\) 的原有顺序和重数；不额外除以 \(2!\)。

### 8.2 Fouvry 的增强层级及不能省略的引用范围

对 \(a\leq N^{1/10}\) 的第八项及两个四重项，作者用 Fouvry 而不只半层级。
原 Corollary 2(i) 的对象是短区间双线性序列：
\(\alpha_m\) 支持于 \([M,2M]\)、\(\beta_n\) 支持于 \([Y,2Y]\)，
二者为固定阶数的 divisor-bounded 系数，\(\beta\) 满足文中的
Siegel–Walfisz 条件。令 \(X=4MY\)、
\(\nu=\log Y/\log X\in[\varepsilon,1/10]\)；
对任意固定 \(A,\varepsilon>0\)，well-factorable、order 1、层级
\[
                       X^{(5-5\nu)/9-\varepsilon}               \tag{8.2}
\]
的权给出 \(O(X/\log^A X)\) 的平均误差，原陈述还要求 \(1\leq|a|\leq X\)。
Wu04 TeX 的 `5(1-\nu)9` 应由原文确认为除以 9，不是乘以 9。

在作者的计数应用，短变量是首标签素数，长变量为其余标签及粗商的乘积；
短系数的 Siegel–Walfisz 来自素数定理的该版本，长系数为固定阶
\(\tau_K\) 控制。Rosser 上筛权具有所需 well-factorability。
因此局部主质量的层级指数是
\(\theta(x)=5(1-x)/9\)，相应权
\[
 b(x)=
 \begin{cases}
 36/[5(1-x)],&x\leq1/10,\\
 8,&x\geq1/10.
 \end{cases}                                                     \tag{8.3}
\]
这是 \(4/\theta(x)\)，不是另造的预算。

**引用边界。** 在下述全范围上界中，本文引用的是 Wu04 §10
(10.12) 已组织好的实际 switching 估计，而不是声称仅写出 Corollary 2(i)
就完成了所有局部假设。尤其在小乘积短箱上，偏移是 \(a=N\)，不自动满足
\(|a|\leq4MY\)；还须有原应用所需的全范围/短箱运输。
本文没有将这个运输独立补证，也没有重复 M6 的专门分析任务。
若不接受这条专门计数估计作为文献引用，而要求仅由原 Fouvry 陈述现场推出，
这里还存在这个明确的技术证明义务。它不被标成已经独立推导通过。

### 8.3 三个明确积分

由 (8.1)，对 \(U_7\) 取 \(l=x\)、再令 \(t=1/x-1\)；
对 \(U_8\) 取 \(l=1/3\)；
对 \(J_9\) 取 \(l=\sigma\)，得到
\[
\begin{aligned}
 C_7&=8\int_2^{1/\sigma-1}\frac{\log(t-1)}t\,dt,\\
 C_8&=\frac{36}{5}\int_\alpha^{1/10}
              \frac{\log(2-3t)}{t(1-t)^2}\,dt
       +8\int_{1/10}^{1/3}\frac{\log(2-3t)}{t(1-t)}\,dt,\\
 C_9&=8\int_\beta^\sigma
       \frac{\log((1+6\alpha-2t)/(1-6\alpha))}{t(1-t)}\,dt.
\end{aligned}                                                     \tag{8.4}
\]
故以所述文献 switching 上界为引用，量词为每个固定
\(\varepsilon>0\)、全部充分大偶数 \(N\)，有
\[
 U_7\leq(C_7+\varepsilon)\Theta,\quad
 U_8\leq(C_8+\varepsilon)\Theta,\quad
 J_9\leq(C_9+\varepsilon)\Theta.                                 \tag{8.5}
\]
这说明固定第九门不需要换一个数值积分：原 \(C_9\) 正是
\(\int_\beta^\sigma b(t)\log((1-t-\sigma)/\sigma)/(t(1-t))\,dt\)
在半层级 \(b=8\) 的式子。没有把移动门计数同固定门计数声称相等。

### 8.4 四重项的完整非单位粗商

对 \(Q_{10},Q_{11}\)，商通常不是素数。其实际载体是
\[
 a<b<c<d,\quad m\geq1,\quad P^-(m)\geq b,\quad
                         p=N-abcdm\text{ 为素数}.                \tag{8.6}
\]
平方自由好补数上有自动互素条件；做上界时可放宽，但不改变标签重数。
单位商的补数满足 \(abcd\leq N^{2\beta+\lambda}\)，而
\(2\beta+\lambda<1\)，因此有界标签重数下为 \(o(\Theta)\)。
非单位商必须保留全部粗数，不能代换成素数。

引用 Buchstab 粗数渐近式：对固定紧区间
\(1+\varepsilon\leq\log X/\log y\leq C\)，
\(\#\{1<m\leq X:P^-(m)\geq y\}\) 的主项为
\(X\omega(\log X/\log y)/\log y\)，误差在本处的固定指数域均匀为
\(o(X/\log y)\)。这里 \(X=N/(abcd),y=b\)。
再使用 §8.2 的实际上筛引用和四次素数分部求和，得到核
\[
 K(x,y,z,t)=
     \frac{\omega((1-x-y-z-t)/y)}{xy^2zt}.
                                                               \tag{8.7}
\]
两个完整域是
\[
\begin{aligned}
 {\cal D}_{10}&=\{\alpha\leq x\leq y\leq z\leq t\leq\beta\},\\
 {\cal D}_{11}&=\{\alpha\leq x\leq y\leq z\leq\beta\leq t
                                                   \leq\lambda-z\},
\end{aligned}
\]
\[
 C_{10}=\int_{{\cal D}_{10}}b(x)K,\qquad
 C_{11}=\int_{{\cal D}_{11}}b(x)K.                               \tag{8.8}
\]
于是 \(Q_i\leq(C_i+o(1))\Theta\) 是相应的文献计数上界。
由于 \(2\beta<\lambda\)，两域无缝合并为
\[
        \alpha\leq x\leq y\leq z\leq\beta,\qquad z\leq t\leq\lambda-z.
                                                               \tag{8.9}
\]
这与 §3.5 产生的负包一致；没有新增 \(cd\geq V\) 的主质量。

粗数参数在 \({\cal D}_{10}\) 的下确界为 \(1/\beta-4\)；
在 \({\cal D}_{11}\) 的下确界为
\[
                  \frac{1-\lambda}{\beta}-2
                  =\frac{1/2+2\alpha}{\beta}-2<\frac{17}{5}.
                                                               \tag{8.10}
\]
因此原打印说明的 \(\omega(s)\leq .561522\)（\(s\geq3.4\)）不能直接覆盖
整个第十一域。须分出角区或用另一个已证明的界。这里只作精确域检查，
没有求积，也没有因此断言原定理错误。

## 9. 最终有号常数账：条件推论与数值身份

### 9.1 所有解析箭头齐备时的实际消费者

把 (3.4)、(5.2)、(5.4)、(A6)、(8.5)、(8.8) 合在同一个充分大阈值，得到
\[
\begin{aligned}
 4D_{1,2}(N)/\Theta(N)\geq{}&
 3C_1+C_2-C_3-C_4+C_5+C_6-2C_7-C_8-C_9-C_{10}-C_{11}\\
 &+G_2+G_3+G_4+G_5+\widehat G_6-o(1).
\end{aligned}                                                     \tag{9.1}
\]
这是用本节真实计数推出的同结论组合式，不要求完整原单条母式。
若 (9.1) 的常数右端有严格下界 \(4(0.899+\eta)\)，\(\eta>0\)，
先把有限个筛法/分布误差取为总计小于 \(2\eta\)，再扩大 \(N_0\) 支付
\(O(N^{1-\alpha})/\Theta\)，便对**每个**充分大偶数 \(N\) 推出 (T)。
只有等于 \(4\cdot0.899\) 的界还不够吸收无符号 \(o(1)\)。

(9.1) 在本文仍是明确标注的条件推论，因为 (A6-hi) 尚缺；它不是又一个
宣称任务完成的 `hpay` 接口。

### 9.2 作者打印的数值输入

以下数值来自 Wu08 §5 最后计算，方向按 (9.1)：

| 输入 | 打印下界 | 输入 | 打印上界 |
|---|---:|---|---:|
| \(C_1\) | 14.900897 | \(C_3\) | 23.652925 |
| \(C_2\) | 9.103015 | \(C_4\) | 19.643510 |
| \(C_5\) | 1.654808 | \(C_7\) | .585179 |
| \(C_6\) | 3.819092 | \(C_8\) | 5.279581 |
| \(G_2\) | .005283 | \(C_9\) | 5.372410 |
| \(G_3\) | .039890 | \(C_{10}\) | .104305 |
| \(G_4\) | .008860 | \(C_{11}\) | .543858 |
| \(G_5\) | .001359 | | |
| \(\widehat G_6\) 的最后阶梯式 | .060469 | | |

最后一行的**积分支持**已在 (6.3) 核对；它的数值和实际下筛适用性不是同一件事。
其余表值也不能只因作者打印就作为本阶段已认证的有向输入。

只对这些有限小数作精确有理数加减，得到
\[
\begin{aligned}
 &3C_1+C_2-C_3-C_4+C_5+C_6-2C_7-C_8-C_9
                                  &&\rightsquigarrow 4.160822,\\
 &G_2+G_3+G_4+G_5+\widehat G_6 &&\rightsquigarrow .115861,\\
 &C_{10}+C_{11} &&\rightsquigarrow .648163,\\
 &\text{有号总账}/4 &&\rightsquigarrow .90713.
\end{aligned}                                                     \tag{9.2}
\]
符号 \(\rightsquigarrow\) 表示“代入打印数所得”，不是已证明的积分不等式。
因此原文只写 \(>.899\) 在纯加减层面有余量；不能把 .90713 声称为新证明的常数。

### 9.3 已有精确证书与其使用限制

本阶段只读了已有证书的声明、对象定义和源恒等式，没有重新运行内核：
`WSrcFourSourceCount.original_pair_source` 的对象正是 (8.8) 合并成 (8.9)
的 \(b(x)\omega/(xy^2zt)\) 积分；外权由
`Wu08OriginalFourWeights.original` 固定。没有无权/有权替换，也没有截去
第十一项角区。
所用 `LiLiuPrereqBuchstabFunction` 明确给出 \(1\leq t\leq2\) 时
\(\omega(t)=1/t\)，以及全部 \(t\geq2\) 的积分方程
\(t\omega(t)=1+\int_2^t\omega(v-1)\,dv\)。
逐个单位区间的积分递推唯一性把它与本文标准 Buchstab 函数识别；
四重域参数全部大于 3，故该实现对 \(t<1\) 的连续延拓不参与 (8.8)。
这与 §7 中可能碰到 \(t<1\) 的 Psi 积分是两个不同的对象核对问题。

已有 `WSrcFourEnclosureFine.original_pair_upper` 给出的出口为
\[
                           C_{10}+C_{11}<851/1250=.6808.          \tag{9.3}
\]
它用 .561522 控制外变量较小的部分，并对剩余角区用 \(4/7\)，没有把
\(s\geq3.4\) 的细界套到全域。
`WSrcFourEnclosureResult.original_pair_lower56` 自身带
\(\omega(s)\geq14/25\ (s\geq3)\) 的前提；
`WSrcFourEnclosureAccepted.original_pair_enclosure` 明确用
`WSrcBuchstabLowerRoot.buchstab_lower56` 消费该前提，给出已存的另一端
\(16959/25000\)。本文不把“下界声明存在”说成已经本轮重放其证明。

就已匹配的字面四重积分而言，打印对界 .648163 与这一已有证书包不能同时作为
同一对象的有向界使用。这仅定位为**数值来源兼容性尚未解决**：
不从旧对界冲突直接推出作者定理有错，也不据此拒绝可能的有效组合补证。
本轮已经从原文到核、域、外权逐项核清了这里使用的对象。

即使暂时接受表中其余全部打印方向，仅将负四重包换成 (9.3)，精确加减也只给出
\[
 \frac{4.276683-.6808}{4}
                  =\frac{3595883}{4000000}=.89897075<.899.       \tag{9.4}
\]
同一账本要严格超过 .899，四重包需小于 .680683，或需来自已证明且已认证的
其他实际增益。这只是有号代数阈值，**不是**新设费用 cap，更不是已经证明的界。
本文未重算积分、未调参数、未用扫描补齐这个差额。

数值分账因此是：

* **打印值**：本节表、初始 \(H\) 表、\(\Psi\) 表以及扩展 \(H/h\) 表。
* **已有精确证书出口**：(9.3) 及上述带供应者的另一端，限于已匹配的四重积分；
  本阶段无内核重验声明。
* **本阶段确切核算**：固定参数的有理不等式、(6.3) 的符号积分截面、
  (9.2)/(9.4) 的有限有理数加减；没有认证其输入积分。
* **仍需认证**：足以使 (9.1) 严格超过 \(4\cdot.899\) 的同对象有向数值包，
  特别是 \(H/h/\Psi\) 的实际强度和四重包的兼容消费。

## 10. 本文究竟接通到哪里

已经给出完整自然语言推导的承重片段为：

1. 包括单位补数、素补数及高因子在内的 lower-weight 分类和例外费用；
2. 通过 (3.5)–(3.10) 直接导出的有效十一槽组合 (3.4)，不是旧未付残项的改名；
3. 固定第九门的素商/单位商判定，以及它与原 \(C_9\) 的解析积分匹配；
4. 第六项经典积分在移动域外为零，且作者最后使用的 \(G_6\) 正是同一移动域的
   \(s\geq2\) 截面；因此此前必须先恢复 full U6 的工程目标不是 (T) 的必要前提；
5. 全部槽、增益、归一化、负四重粗商核及最后有号加减的明确连接。

这还不是 (T) 的证明。沿本条组合路线，首个未证解析命题是 (A6-hi)：
来源位置为 Wu08 §5 对第六项两块直接应用 Proposition 4.3 的一句简写，
但其最大标签超出该命题的 \(N^{1/4}\) 条件。它需要真正的额外平均下筛或
有号组合论证，不能由现有单标签上界、普通线性筛或标签换序代替。
随后还有 §9 的有向数值认证；若要求从 Fouvry 原始陈述而非 Wu04 已组织的
专门计数上界重建，§8.2 所列偏移/短箱运输也尚未独立补证。

完整原参数 Wu08 单条母式仍另列开放。本文既没有证明它错误，也没有证明某个有限
正残量给出无限族。当前得到的是一条避开旧不必要有限目标、直接通向普通 0.899
输入的实质数学重建，但解析与数值闭合仍未完成。
