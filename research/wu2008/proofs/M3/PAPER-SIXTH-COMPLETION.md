> **Checkpoint status:** historical partial sixth-term exploration; no full gain proved.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# 原第六项：实际 Buchstab 总和已展开，原阶梯改善尚未接通

**结论：尚未证明原第六项的 \(C_6+G_{6,\mathrm{step}}\) 下界。**
本文沿 Wu04 的实际 Buchstab 分解和 switching 方法继续展开，不把
Proposition 4.3 的资格核对作为终点。所得实际计数恒等式、经典主项抵消、
换位后的计数对象及其主常数如下；尚缺的正改善在 §7 明确保留。
这里没有建立一个带新自由数学假设的“完成”接口。

父级 `../ORIGINAL-NUMERIC-COMPLETION.md` 已接通原有号数值账：
保留原全部项，以本组已接纳的 \(G_2\) 下界及同对象四重上界
\(851/1250\)，得到系数
\(179839833/200000000>899/1000\)。
这笔数值账不再列为前进阻塞。`PROOF.md` 中已父核的 1.894 后半桥、
`PAPER-NUMERICS.md` 及撤下方案的历史审查均保持不动。
本文不使用撤下的低域剪收益组合，不研究 1.8938。

## 1. 唯一计数目标与归一化

沿 M1 `PAPER-COMPLETION.md` §7 的记号，固定
\[
 \alpha=\frac{100}{1327},\quad \beta=\frac{25}{206},\quad
 \sigma=\frac12-3\alpha,\quad \lambda=\frac12-2\alpha,\quad z=N^\alpha,
 \qquad \Theta(N)=\frac{C_NN}{\log^2N}.
 \tag{1}
\]
\(C_N\) 是 Wu 的奇异因子，即
\[
 C_N=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
       \prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2}.
\]
令
\[
 Q_N(d;t)=\#\{p<N:p\text{ 为素数},\ d\mid N-p,\
  \ell\mid (N-p)/d,\ \ell\nmid N\Longrightarrow\ell\ge t\}.
 \tag{2}
\]
商为 1 时满足筛条件；商为 0 不会出现。两个标签 \(a,b\) 为素数，
\((ab,N)=1\)，来自不交窗口，始终 \(a<b\)。原实际第六项是
\[
 \Upsilon_6(N)=
 \sum_{N^\alpha\le a<N^\beta}
 \sum_{\substack{N^\beta\le b<N^\sigma\\(ab,N)=1}}
       Q_N(ab;z).
 \tag{3}
\]
它是带标签的计数，不是 distinct \(p\) 计数；一个 \(p\) 可对应多个
\((a,b)\)。以下每次重排都保留这些标签，不除以 2，也不除以 4。
与 distinct \(p\) 母式的最后拼接由 M1 处理。

写
\[
 \nu=\tfrac12-x-y,\quad s=\nu/\alpha,\quad
 k(x,y)=\frac4{xy\nu},\quad
 {\cal R}=\{x\ge\alpha,\ x\le\beta,\ y\ge\beta,\ x+y\le\lambda\}.
 \tag{4}
\]
经典项恰为
\[
 C_6=\iint_{\cal R}k(x,y)a(s)\,dx\,dy.
 \tag{5}
\]
这里 \(a(s)=s f(s)/(2e^\gamma)\)、\(A(s)=sF(s)/(2e^\gamma)\)
是原线性筛归一化；\(a(s)=0\) 于 \(s\le2\)。
式 (5) 只解释经典部分的支持，不宣称实际 \(h\) 在域外为零。

设 \(s_i=2+i/10\)，在 \((s_{i-1},s_i]\) 取
\(h_{\mathrm{step}}(s)=h(s_i)\)。原最后使用的是
\[
 G_{6,\mathrm{step}}
 =\iint_{\cal R}k(x,y)h_{\mathrm{step}}(s)\,dx\,dy
 =8\sum_{i=1}^{21}g_6^i h(s_i).
 \tag{6}
\]
这里的 \(h(s_i)\) 保留原对象，不换成另选较低数列。
原变量替换及第 15 格跨界、第 21 格截断，直接复用 M1 (P43)–(P44)
及本组 `PAPER-NUMERICS.md` 的接线，不重新积分。
目标仍严格为
\[
 \forall\epsilon>0\ \exists N_0\ \forall N\ge N_0,\ N\text{ 偶}:
 \quad\Upsilon_6(N)\ge
 (C_6+G_{6,\mathrm{step}}-\epsilon)\Theta(N).
 \tag{S}
\]
不要求更强的全域逐盒最优 \(h\) 结论。

## 2. 合法部分的复用，以及总和展开的范围

对 \({\cal R}\cap\{y<1/4\}\) 的固定严格内区，原两标签短箱合法：
大标签在先，有 \(2y<1/2\)，并且
\[
 y+2x\le\lambda+\beta<1/2.
 \tag{7}
\]
固定内区后选正 \(\delta\)，原 Proposition 4.3／Wu04 定义给实际
\(a+h\) 下筛。阶梯只需有限节点，阈值可统一。
微箱误差是统一的 \(\epsilon{\cal T}(N,\eta)\)，求和仍为
\(O(\epsilon\Theta(N))\)，不是每箱一份 \(\epsilon\Theta(N)\)。
这些已由 M1 §7.1 展开，本文直接复用。

下面不再重复“\(\phi_4<1/4\)”诊断，而在真实高域
\[
 {\cal H}=\{\,\alpha<x<1/4-2\alpha,\quad
                   1/4<y<\lambda-x\,\}
 \tag{8}
\]
作实际总和。它有正面积，并且
\[
             2<s(x,y)<\frac{927}{400}<2.4.
 \tag{9}
\]
因此只涉及原前四个阶梯的一部分；仍不能当作边界或删除。

先固定一个正面积严格内区 \(D\Subset{\cal H}\)，可取由
\(x,y,x+y\) 的严格内门确定的多边形，随后用这种内区穷尽 \({\cal H}\)。
取足够小的固定 \(\delta>0\)，使在 \(D\) 上
\[
 Q=N^{1/2-\delta},\quad
 \nu_\delta=\tfrac12-\delta-x-y,\quad s_\delta=\nu_\delta/\alpha\ge2.
 \tag{10}
\]
记 \({\cal B}_D(N)\) 为对应素数标签对集合。以下有限计数先固定
\(D,\delta\)，再令 \(N\to\infty\)，最后才让 \(\delta\downarrow0\)、
内区穷尽。尤其不会在 \(s_\delta<2\) 的条带上错误使用下文的延迟恒等式。

## 3. 沿 Wu04 (3.14) 的实际三标签总和

对 \(d=ab\)，设
\[
 L_d=\log(Q/d),\qquad s_d=\frac{L_d}{\alpha\log N},\qquad
                       z_0(d)=(Q/d)^{1/6}.
 \tag{11}
\]
参数 6 只是 Wu04 Proposition 2 中较低筛门的一个固定合法选择，
不是新优化参数。此处 \(2\le s_d<6\)，故 \(z_0(d)<z\le a<b\)。
对每个实际 \(p\)，按 \((N-p)/(ab)\) 中最小的、
不整除 \(N\) 的素因子分解，有**精确等式**
\[
 Q_N(ab;z)=Q_N(ab;z_0(ab))-
 \sum_{\substack{z_0(ab)\le q<z\\q\ {\rm prime},\ (q,N)=1}}
                                      Q_N(abq;q).
 \tag{12}
\]
这不是权类假设。若商已 \(z\)-粗，右侧仅第一项计一次；
否则它在第一项中出现，当且仅当最小相关素因子 \(q\ge z_0(ab)\)，
并在唯一一个负项中抵消。商为 1 只在第一项出现。
即使 \(q^2\mid N-p\)，唯一最小素因子仍是 \(q\)，负项筛门严格为 \(q\)，
所以仍只计一次。这里无需先排除非平方自由补数。

由于 \(q<z\le a<b\)，三个**选中标签**互异。这使 \(abq\) 平方自由，
但并不要求其余商平方自由。对全部标签求和，令
\[
 \begin{split}
 T_D(N)&=\sum_{(a,b)\in{\cal B}_D(N)}Q_N(ab;z),\\
 B_D(N)&=\sum_{(a,b)\in{\cal B}_D(N)}Q_N(ab;z_0(ab)),\\
 L_D(N)&=\sum_{(a,b)\in{\cal B}_D(N)}
       \sum_{z_0(ab)\le q<z}Q_N(abq;q).
 \end{split}
\]
所有素数和均保留与 \(N\) 互素条件。于是
\[
                              T_D=B_D-L_D.                    \tag{13}
\]
这是原方法在高域上的实际平均分解；负号落在 \(L_D\)，其改善必须来自
**上界的减小**，不能用一个下界替代。

### 3.1 分布余项确实可以支付，但它支付到哪里

取 \(\delta\le\alpha/2\)。对式 (12) 的所有标签，有
\[
 q\ge N^{\alpha/4},\qquad
 abq\le N^{\lambda+\alpha}=N^{1/2-\alpha}<Q.
 \tag{14}
\]
所以三标签卷积有界阶、与筛层之间有固定幂次余量。
对 \(B_D\) 用普通下筛、对 \(L_D\) 用普通上筛，局部层分别为
\(Q/(ab)\)、\(Q/(abq)\)，总 AP 模数不超过 \(Q\)。

所用是普通素数 BV 的带固定除数权形式：对每个固定整数 \(K\)
及每个 \(A_0>0\)，足够大的对数损失使
\[
 \sum_{\substack{v\le N^{1/2}/\log^{B_0}N\\v\ {\rm squarefree}}}
 \tau_K(v)\max_{(c,v)=1}
 \left|\pi(N;v,c)-\frac{\operatorname{li}(N)}{\varphi(v)}\right|
 \ll_{A_0,K}\frac{N}{\log^{A_0}N}.                             \tag{15}
\]
这是 Wu04 Lemma 2.3 所含 BV 与其 §3 Proposition 1 使用的标准
除数权推论。这里 \(c=N\bmod v\)，\(v\) 与 \(N\) 互素；
最大值允许这个随 \(N\) 变化的剩余类。Rosser 权绝对值至多 1，
展开总模数的分解数由固定 \(\tau_K\) 控制，故 (15) 适用。
固定 \(\delta>0\) 后，\(Q\) 最终低于该对数层。
筛门随 \(ab,q\) 移动仅改变模数系数的截断，不扩大绝对除数权上界。

Mertens 主项也统一：所有选中标签至少 \(N^{\alpha/4}\)，
\[
 \frac{C_{abN}}{\varphi(ab)}=\frac{C_N}{(a-2)(b-2)}.
 \tag{16}
\]
加入 \(q\) 时再乘 \(1/(q-2)\)。
固定幂次大标签与 \(N\) 大素因子的局部修正为 \(1+o(1)\)；
排除整除 \(N\) 的标签的倒数素数质量也是 \(o(1)\)。

定义真正由原 \({\cal T}\) 给出的权
\[
             w_d(N)=\frac{4\operatorname{li}(N)C_{dN}}
                                      {\varphi(d)\log(Q/d)}.
 \tag{17}
\]
上述经典筛和 (15) 给
\[
 \begin{split}
 B_D(N)&\ge a(6)\sum_{{\cal B}_D}w_{ab}(N)-o(\Theta(N)),\\
 L_D(N)&\le
  \sum_{{\cal B}_D}w_{ab}(N)
       \int_{s_{ab}-1}^{5}\frac{A(t)}t\,dt+o(\Theta(N)).
 \end{split}                                                   \tag{18}
\]
对第二行，局部上筛参数为
\(t=\log(Q/(abq))/\log q=L_{ab}/\log q-1\)。
素数分部求和中的精确变量替换是
\[
 \frac{d q}{q\log q}\frac{L_{ab}}{L_{ab}-\log q}
                    =-\frac{dt}{t}.                            \tag{19}
\]
上下端分别给 5 和 \(s_{ab}-1\)。式 (18) 的系数没有遗漏一个
\(t+1\)、\(2e^\gamma\) 或外面的 4。

### 3.2 经典抵消是精确的，不含隐藏收益

原延迟方程给，在 \(2\le v\le6\) 上
\[
             a(6)-\int_{v-1}^{5}\frac{A(t)}t\,dt=a(v).
 \tag{20}
\]
把 (18) 代入**实际**等式 (13)，得到
\[
 T_D(N)\ge\sum_{{\cal B}_D}w_{ab}(N)a(s_{ab})-o(\Theta(N)).
 \tag{21}
\]
随后相同的素数分部求和给极限主项
\[
 4\iint_D\frac{a(s_\delta)}{xy\nu_\delta}\,dx\,dy
                  \ \longrightarrow\ \iint_D k(x,y)a(s)\,dx\,dy.
 \tag{22}
\]
因此聚合 BV、归一化和 Buchstab 顺序在高域确实工作；
但式 (20) 把它们恰好消成经典 \(a\)，**没有生产 \(h(s_i)\)**。
这比仅指出原短箱不合法更精确：未付的是 (13) 中真实有号总和的
额外改善，而非 AP 余项或积分运输。

## 4. 改先后次序：小的合法前缀不能直接吞掉大标签

式 (12) 的新标签满足 \(q<a<b\)。若先把 \(a,q\) 当卷积前缀，
则它的平方前缀条件有固定余量，确实是合法小前缀。
但剩余对象是
\[
          \sum_b Q_N(aqb;q),                                  \tag{23}
\]
其中 \(b\) 是一个指定的大素因子，**不是**商的最小素因子。
它不等于 \(\Phi(N,\pi_a*\pi_q,\cdot)\) 的一个 Buchstab 单项。

这一差异可以在计数层继续展开。先去除含素数平方
\(\ell^2\mid N-p\)、\(\ell\ge N^{\alpha/4}\) 的补数。
每个输出的 \((a,b,q)\) 标签数由固定常数控制，故总费用
\[
 O_\alpha\left(N\sum_{\ell\ge N^{\alpha/4}}\ell^{-2}\right)
                         =O_\alpha(N^{1-\alpha/4})
                         =o(\Theta(N)).
 \tag{24}
\]
这里不把较小下门产生的例外误写成 \(O(N^{1-\alpha})\)。
在余下计数上再按最小素因子分解，得到
\[
 Q_N(abq;q)=Q_N(abq;b)+
       \sum_{\substack{q<r<b\\r\ne a,\ (r,N)=1}}
                                      Q_N(abqr;r),             \tag{25}
\]
等式在未排除计数上相差至多 (24)。
选中标签不会再次成为商的素因子；\(r=a,q\) 正是平方例外。

式 (25) 后一项全部为正，且有真实非空区间 \(q<r<b\)。
在对 \(L_D\) 作上界时，丢掉它的方向错误。
因此“先把 \(a,q\) 合成合法权，再把 \(b\) 当 Buchstab 最小素因子”
不是可用的原样重排。需要继续控制这笔四标签和，不能只更换标签顺序。
这并不排除保留所有项的更精细 Chen 有号组合。

## 5. 实际直接换位：一个可用上界为何仍不提供收益

本节继续核真实 prime 变量，不假设高层 prime AP 分布。
把 (12) 的负项写成
\[
              N-p=abqm,\qquad P^-(m)\ge q.                     \tag{26}
\]
若 \((N-p,N)>1\)，则 \(p\mid N\)，输出至多 \(\omega(N)\) 个；
原三个大标签的重数有界，所以可付 \(O_\alpha(\log N)\)。
其余对象中 \(m\) 与 \(N\) 互素，(26) 的普通粗糙条件与原筛条件相同。
允许 \(m=1\) 和重复因子，不另加无来源平方自由条件。

令 \(e=aqm\)，把 \(b\) 当素数变量、把 \(p=N-eb\) 当待筛输出。
先只保留这样的 \((a,q,m)\)：存在满足原 \(D\)、(11) 和 \(b\le N/e\)
的实数 \(b\)。令 \(f_N(e)\) 为这类三元组的个数，并限制 \((e,N)=1\)。
那么
\[
 0\le f_N(e)\ll_\alpha1,\qquad
 e\le N^{3/4},\qquad P^-(e)\ge N^{\alpha/4}.                   \tag{27}
\]
有界性来自 \(a,q\) 都是 \(e\) 的固定幂次大素因子，选定二者后 \(m\)
唯一；不来自错误的“所有分解唯一”。
在这一载体上放宽 \(b\) 的窗口，得真正的单边不等式
\[
 L_D(N)\le
 \sum_e f_N(e)\#\{b\le N/e:b\text{ 素数},\ N-eb\text{ 素数}\}
                      +O_\alpha(\log N).                      \tag{28}
\]
这是上界放宽，不是把放宽后主项当成原负项的精确计数。

对 (28) 可以直接用 Wu04 Lemma 2.3 的**第一条**，
取它的支持参数为 \(1/5\)、\(x=N\)、\(y=N\)；
\(e\le N^{3/4}\le N^{4/5}\) 满足支持，\(f_N\) 一致有界。
余项含所有既约剩余类的最大值，故 \(N\bmod d\) 准入。
无需引用任何对移动端点的含糊版本，也不使用只准固定剩余类的 BFI。
若将系数除以固定上界归一化，结论再乘回该常数。

设
\[
                         X_N=\sum_e f_N(e)\operatorname{li}(N/e).
\]
用模数层 \(D_s=N^{1/2}/\log^{B_0}N\)、筛门 \(z_s=\sqrt{D_s}\)
的一维上筛。其 \(F(2)=e^\gamma\) 与
\(V_N(z_s)\sim2e^{-\gamma}C_N/\log z_s\) 给主常数 **8**：
\[
 L_D(N)\le(8+o(1))\,\frac{C_NX_N}{\log N}+o(\Theta(N)).
 \tag{29}
\]
主项中 \((e,d)=1\) 的排除可统一去掉：由 (27)，每个 \(e\) 的相关
素因子个数有界，且
\(\sum_{\ell\mid e}1/(\ell-1)\ll_\alpha N^{-\alpha/4}\)。
其总局部修正及 Rosser 权和至多增加对数因子，仍为 \(o(\Theta)\)。
\(X_N\ll_\alpha N/\log N\)：对 \(a,q\) 作倒数素数和，粗糙 \(m\)
的倒数和有界，而 \(\log(N/e)\ge\frac14\log N\)。
小输出 \(p<z_s\) 的例外至多 \(O_\alpha(z_s\log N)\)：
固定输出后 \(a,q\) 的选择有界，\(b\) 是 \(N-p\) 的素因子，
选择至多 \(O(\log N)\)。这些费用均为 \(o(\Theta)\)。

### 5.1 不求积即可比较这份换位预算

式 (29) 使用放宽后的 \(X_N\)。它至少包含原 \(b\) 窗口的
对数积分质量，记为 \(X_{D,N}^{\rm window}\)。把这个较小质量中
\(m\) 的和用标准 Buchstab 粗糙数定理求主项、对 \(a,q\) 用 PNT：
\[
 \frac{\log N}{N}X_{D,N}^{\rm window}
 \longrightarrow
 \iint_D\int_{\nu_\delta/6}^{\alpha}
 \frac{\omega((1-x-y-r)/r)}{xy r^2}\,dr\,dx\,dy.
 \tag{30}
\]
这是渐近表达，不是新数值求积。
具体地，先将素数 \(b\) 的 \(\operatorname{li}\) 差写成
\(db/\log b\)，再交换非负求和；
内层为 \(\#\{m\le N/(abq):P^-(m)\ge q\}\)。
在当前固定域，\(q\ge N^{\alpha/4}\)，其 Buchstab 参数远大于 2，
并位于固定紧区间；标准
\(\Phi(U,q)=(\omega(\log U/\log q)+o(1))U/\log q\)
一致适用。排除 \(N\) 的大素因子只造成幂次小误差。
由 \(da/(a\log a)\)、\(db/(b\log b)\)、\(dq/(q\log q)\)
和粗糙密度 \(1/\log q\)，得到准确分母 \(xy r^2\)。

让 \(\delta\downarrow0\)。式 (18) 的经典负项预算为
\[
 {\cal L}_{\rm cl}(D)=
 4\iint_D\int_{\nu/6}^{\alpha}
          \frac{A(\nu/r-1)}{xy r(\nu-r)}\,dr\,dx\,dy.             \tag{31}
\]
式 (29) 的上界右侧，单是 (30) 这一子质量就支付
\[
 {\cal L}_{\rm sw,window}(D)=
 8\iint_D\int_{\nu/6}^{\alpha}
          \frac{\omega((1-x-y-r)/r)}{xy r^2}\,dr\,dx\,dy.
 \tag{32}
\]
在此域设 \(t=\nu/r-1\)，则 \(1\le t\le5\)，而
\[
 \frac{1-x-y-r}{r}=t+\frac1{2r}>2.
 \tag{33}
\]
Buchstab 方程直接给 \(\omega(u)\ge1/2\) 于 \(u\ge1\)：
初段 \(1/u\) 满足此界，之后用
\(u\omega(u)=1+\int_1^{u-1}\omega(v)\,dv\) 逐单位区间延续。
另外 \(A(t)\le t\) 于 \(1\le t\le5\)：
\(t\le3\) 时 \(A=1\)，而 \(3\le t\le5\) 时
\[
 A(t)=1+\int_2^{t-1}\frac{\log(v-1)}v\,dv\le t-2<t.
 \tag{34}
\]
所以逐点有
\[
 \frac{8\omega((1-x-y-r)/r)}{xy r^2}
 \ \ge\ \frac4{xy r^2}
 \ \ge\ \frac{4A(t)}{xy r(\nu-r)}.                             \tag{35}
\]
在正面积严格内区的三维内部，第二个不等式严格。
因此
\[
                    {\cal L}_{\rm sw,window}(D)>
                    {\cal L}_{\rm cl}(D).                     \tag{36}
\]
这里比较的是**两份可用上界的预算**，绝不据此比较真实计数的大小。
结论仅是：采用 (28) 的直接正项放宽、再用 (29)，即使只看它的原窗口
子质量，其预算已不小于原经典费用，故这份具体上界不能从 (13) 的
经典起点中支付正 \(h\) 收益。它不排除原作者的多项有号 switching。

## 6. 作者有号双筛与上述总和的交点

Wu08 Proposition 4.4 实际写的是单标签上筛，且明确说其
\(\Psi_1/\Psi_2\) 改善是非迭代版本。原证明的方向为
\[
 S\le\Omega_1-\tfrac12\Omega_2+\tfrac12\Omega_3
                         +O(N^{1-\eta}).
 \tag{37}
\]
所以 \(\Omega_2\) 要下界、\(\Omega_1,\Omega_3\) 要上界。
不能照搬该处统一打印的“\(\le\)”把负项也上估。
Wu04 Lemma 5.1、5.2 的证明采用的正是对应有号方向；
本文按其证明读法，而非按一个不合符号的排版行使用。

若要把 (37) 用于 (13) 的 \(L_D\)，承载序列已经是
\(\mathcal A_{abq}\)，筛门为 \(q\)，局部剩余层为 \(Q/(abq)\)。
它不是 Proposition 4.4 的单标签 \(\mathcal A_b\)；
额外的 \(a,q\) 不能只吸收到外系数而保持同一个 \(\Psi\)、同一个主核。
按 Wu04 证明继续展开时，正、负项仍带这些标签；
式 (25) 展示了试图移去大标签时首先出现的实际附加正项。
本文尚未完成这份新承载序列的原有号组合和其全部主项比较。

另一个不能省略的步骤是“有限深度”与原节点的方向。
Wu04 Proposition 2 给的是
\[
 h(s_i)\ \ge\ h(6)+\int_{s_i-1}^{5}\frac{H(t)}t\,dt
 \quad(2\le s_i\le6).
 \tag{38}
\]
即使后来能为高权证明右侧的一次传递，它也不会因 (38) 自动达到
左侧的实际 \(h(s_i)\)。较小的一次收益不是原节点的上界。
如果从作者产生原节点下界的有限迭代出发，必须把该迭代在当前实际总和
上运输完整，或另证其总收益已经达到 (S)；不能用“节点只有四个”
替代这一步。本文没有把这种运输假定为真。

只读检索的同对象结果分工也明确：
`Wu08G6HighActual.unrestricted_AP_and_theta` 支付 §3 的 AP／质量；
`TruncatedSixthLowerSieve.truncatedSixthLower_pair_signed` 给普通下筛；
`TruncatedSixthLowerGain.truncatedSixthLower_finite_grid_gain` 给合法域有限节点。
`WSrcSixthGainOriginal`、`WSrcSixthGainSource` 给原积分／剖面运输。
保留 `published-highLoss` 或 `conservative` 的实际消费者不等于 (S)，
本轮不消费它们。`SixthSlotAssembly.SixthLower` 是显式待供给的计数输入，
不是生产者。名称含 HighSix 的单标签上筛反馈也没有被当成两标签下筛。

## 7. 当前最早未证处与交接

现在已有的是实际等式 (13)、两条经典单边界 (18)，以及准确抵消 (20)。
例如，若沿“先保留合法域原阶梯，再在高域使用这份分解”的接法，
还需证明高域实际总和中的额外下界：
\[
 B_D(N)-L_D(N)
 -\sum_{{\cal B}_D}w_{ab}(N)a(s_{ab})
 \quad\text{在总和与极限中足以支付}\quad
 \iint_D k(x,y)h_{\rm step}(s)\,dx\,dy\,\Theta(N).
 \tag{39}
\]
式 (39) 是本次实际推导停止的位置，**不是新增的获准假设或已证定理**。
不要求分箱逐一成立，也不要求分别从 \(B_D\) 或 \(L_D\) 单独支付。
更一般的原有号总和还可保留合法域未花的实际收益；本文没有把高域单独
支付列为 (S) 的逻辑必要条件。原最终系数、负费用域和全部阶梯保持不变。

实质上已经排查到三条不同接法的准确落点：

1. 在原大标签总和上直接实施 Wu04 (3.14)，经典余项可控，但主项按
   (20) 精确回到 \(a\)，不能自动产生 \(h\)；
2. 先选合法小前缀 \(a,q\) 时，必须保留 (25) 的实际四标签正项，
   不能把大标签冒充最小素因子；
3. 将大标签直接换成 prime 变量时，(28)–(29) 是可用上界，但其
   原窗口子预算已由解析不等式 (35) 证明不优于经典费用。
   要改善必须使用尚未接通的有号组合，而非此直接正项放宽。

这些结果没有证明作者定理错误，也没有排除其方法中的进一步平均论证。
但截至本文，尚无可引用的同对象定理或已完成的原有号展开能推出 (39)
或直接推出 (S)。因此本组不能把原数值式接成实际 Chen 下界：
**`sixth_actual_lower_complete=false`、`math_complete=false`、
`global_complete=false`。** M1 的原有限母式单独继续；本组不接管或预判它。

所有渐近步骤的顺序均为：给最终 \(\epsilon\)，选内区与固定误差容差，
选足够小的正 \(\delta\) 和所需有限节点／筛深度，再选统一 \(N_0\)。
筛余项、(24)、小输出、素数分部求和误差合计为 \(o(\Theta)\)；
最后以内区极限恢复完整系数。核在本固定域分母有正下界，
有限阶梯有界，故仅消去边界条带是合法的。
这个顺序不能消去 (8) 的正面积高域，本文也没有这样做。

## 8. 实读来源与保存状态

本轮沿下列实际原文和交接推导，不用 Wu08 最终 0.899 结论遮住本项：

| 来源 | 实际使用 |
| --- | --- |
| Wu04.tex 488–532，735–1200 | Pan–Ding／BV；原 \({\cal U}_k,\Phi,{\cal T}\)；经典基线；Proposition 2 的 (3.14)–(3.20) |
| Wu04.tex 555–735 | 较高分布层的序列、剩余类资格；未误用于移动的 prime AP |
| Wu04.tex Lemmas 5.1、5.2；switching 证明 | 原 \(\Omega/\Gamma\) 有号方向及待筛 prime 变量；没有把原类结论自动推广 |
| Wu08.tex 565–700，1174–1490 | 实际双筛定义；Propositions 4.1–4.4 及非迭代上筛 |
| Wu08.tex 1606–1675，2070–2135 | 原第六项分区及最后 21 节点阶梯 |
| M1/PAPER-COMPLETION.md §7 | 同一 (S)、原主核、两标签重数、合法下筛运输 |
| ORIGINAL-NUMERIC-COMPLETION.md | 原有号数值账已接通，仅其解析适用尚须证明 |

读取时 SHA-256：

```text
Wu04.tex
ad4e1c38d6a676c83630e4b18e43ac8ecf032832e4869451fca7c88ecaab2c50
Wu08.tex
fba6f873fbc7f954470db4d23a1099e4df7a4075e96243fdd96f489f3c99bc3b
M1/PAPER-COMPLETION.md
1662e99a88ca038ecec2957408a75a1e79e4dc738512ee04ce441ce6bd571bfc
ORIGINAL-NUMERIC-COMPLETION.md
af36d1701dbf669cda73b1bc0e555fe15d8edc48a174444a1b207ddfd20c6e81
```

本轮仅作自然语言推导及固定有理指数关系核对；没有修改或运行 Lean、
Lake、gate、构建、内核，也没有新求积、扫描、优化或外部通信。
上述解析比较不是一份新数值证书。旧成功／失败日志和全部旧证明保留。
