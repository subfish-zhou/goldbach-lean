> **Checkpoint status:** parent-reviewed finite correction and coefficient support; not the literal full-sixth lemma.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# Wu 原方法的有限母式补正：成对缩域，保留最终全部第六项系数

**本轮有限步骤已接通。** 沿 Wu04 (9.6) 后、(9.7) 前的原操作，
把 Wu08 中间式的正第六项与第二负三重项同时改成移动乘积域，
可证明下文 (F) 的实际计数不等式，没有未付有号残项。
它保留原参数、原移动第九筛门、原两个负四重域，以及作者最后使用的
**全部 \(C_6\) 和 \(8\sum_{i=1}^{21}g_6^ih(s_i)\) 的积分支持**。

这是**原方法的明示中间式补正**，不是原 full-\(\Upsilon_6\) 字面
Lemma 2.2 的证明，也不是把撤下的 \(y<1/4\) 剪收益路线换名复活。
本文不证明第六项实际计数的双筛下界；那一解析调用由 M3 接续。
父级原有号数值账已接通，本文不再把数值列为未解前置。
全路线尚未宣称完成。

旧 `PROOF.md`、`PAPER-COMPLETION.md` 及历史日志均保留。
后者 (P32a) 的上筛门以父级
[`NINTH-SIEVE-CORRECTION.md`](../NINTH-SIEVE-CORRECTION.md) 为准，
本稿 §6 实际消费该补正。

## 1. 对象、原文依据与逐字改动

### 1.1 不变的对象

对充分大偶数 \(N\)，保持
\[
\begin{gathered}
 \alpha=\frac{100}{1327},\qquad\beta=\frac{25}{206},\qquad
 \sigma=\frac12-3\alpha=\frac{727}{2654},\qquad
 \lambda=\frac12-2\alpha=\frac{927}{2654},\\
 z=N^\alpha,\quad w=N^\beta,\quad u=N^\sigma,\quad
 v=N^{1/3},\quad V=N^\lambda=zu,\quad B(a)=\sqrt{N/a}.
 \tag{1}
\end{gathered}
\]
原输出指标为素数 \(p\leq N\)，补数 \(n=N-p>0\)，
\[
 D_{1,2}(N)=\#\{p\leq N:p\text{ 素},\ \Omega(N-p)\leq2\},
 \qquad \Omega(1)=0.
\]
单位补数、素补数都计入；目标归属是原 1.894 及其 Wu 方法，本稿不研究 1.8938。

在 Wu04 (9.2) 已明写的剩余商意义下，记
\[
 Q(d;t)=\sum_{\substack{p\leq N\\p\ {\rm prime}}}
 {\bf1}_{d\mid N-p}\,
 {\bf1}_{\,\ell\mid (N-p)/d,\ \ell\nmid N\ \Longrightarrow\ \ell\geq t}.
 \tag{2}
\]
最后一个条件对所有素数 \(\ell\) 量化，单位商满足它。
下文 \(a,b,c,d,q\) 用作自由标签时均为与 \(N\) 互素的素数。
未缩放子列须排除低于筛门的已选标签，才能表达 (2)；
具体运输及严格／闭门处理沿用已接纳的 `PAPER-COMPLETION.md` §2。
不声称原文某个未排除标签的字面简写与商筛相等。

原十一槽在这个明确意义下为
\[
\begin{aligned}
 \Upsilon_1&=Q(1;z),&\Upsilon_2&=Q(1;w),\\
 \Upsilon_3&=\sum_{z\leq a<v}Q(a;z),&
 \Upsilon_4&=\sum_{z\leq a<u}Q(a;z),\\
 \Upsilon_5&=\sum_{z\leq a<b<w}Q(ab;z),&
 \Upsilon_6&=\sum_{z\leq a<w\leq b<u}Q(ab;z),\\
 \Upsilon_7&=\sum_{u\leq a<b<B(a)}Q(ab;b),&
 \Upsilon_8&=\sum_{z\leq a<v\leq b<B(a)}Q(ab;b),\\
 \Upsilon_9&=\sum_{w\leq a<u\leq b<B(a)}
                                      Q(ab;\sqrt{N/(ab)}),\\
 \Upsilon_{10}&=\sum_{z\leq a<b<c<d<w}Q(abcd;b),\\
 \Upsilon_{11}&=\sum_{z\leq a<b<c<w\leq d<V/c}Q(abcd;b).
 \tag{3}
\end{aligned}
\]
标签顺序和重数不变。第九项仍是原移动平方根门，不是旧稿的固定门替代。

### 1.2 准确的改动清单

定义
\[
 K_6(N)=\sum_{\substack{z\leq a<w\leq b<u\\ab<V}}Q(ab;z).
 \tag{4}
\]
这是唯一改变的最终有限槽，必须与原 \(\Upsilon_6\) 区分命名。

| 位置 | Wu08 原展示形式 | 本稿明确补正 |
|---|---|---|
| (2.4)、(2.6) 的正第六槽 | \(+\Upsilon_6\)，全矩形 | \(+K_6\)，加 \(ab<V\) |
| 同一式的第二负三重项 | \(z\leq a<b<w\leq c<u\) | 同时加 \(bc<V\)，即 \(c<V/b\) |
| 三域归并后 | \(-\Upsilon_{10}-\Upsilon_{11}\) | 完全不变 |
| 第九槽及其门 | 原 \(-\Upsilon_9\) | 完全不变 |
| 最终第六系数 | 原 \(C_6\) 和原 21 格 \(G_6\) 下界 | 完全不变，§5 证明支持身份 |

这不是在负号后单独缩域。原文依据是 **Wu04 (9.6) 后的正二重和**：
作者先利用 \(N^\rho\geq V/a\) 缩小正域，再作 Buchstab，得到移动正二重项
与移动负三重项，进入 (9.7)，再与 (9.8) 合成 (9.9)。
此处该局部操作的上门取 \(N^\rho=u\)，有
\(3\alpha+\rho=1/2\)，故其所需条件有等号也成立。
只消费这一有证明的局部操作，不把 Wu04 整条十五项母式连同其余严格参数条件
机械代入边界。

## 2. 从已接通的 Wu08 (2.6) 出发

### 2.1 精确恒等式先在同一好补数集合上写

记
\[
 {\cal G}_N=\{p\leq N:p\text{ 素},\ (N-p,N)=1,\
       N-p\text{ 平方自由},\ P^-(N-p)\geq z\},
 \tag{5}
\]
约定 \(P^-(1)=+\infty\)。带上标 \({}^{\circ}\) 表示把 (2) 及所有槽的
输出指标限制到这个**同一个**集合；没有给每项选择不同的例外集合。
§2–§3 的等式均使用此上标。

Wu04 Lemma 9.1 的逐补数权证明，以及已接通的 Wu08 (2.3)–(2.6)，给出
\[
\begin{aligned}
 4D_{1,2}(N)\geq{}&
 3\Upsilon_1^\circ+\Upsilon_2^\circ
 -\Upsilon_3^\circ-\Upsilon_4^\circ
 +\Upsilon_5^\circ+\Upsilon_6^\circ
 -2\Upsilon_7^\circ-\Upsilon_8^\circ-\Upsilon_9^\circ
 +\Delta_2^\circ,\\
 \Delta_2^\circ={}&
 \sum_{z\leq a<b<c<v}Q^\circ(abc;b)-T_0^\circ-T_1^\circ-T_2^\circ,
 \tag{6}
\end{aligned}
\]
其中
\[
\begin{aligned}
 T_0^\circ&=\sum_{z\leq a<b<c<w}Q^\circ(abc;a),\\
 T_1^\circ&=\sum_{z\leq a<b<w\leq c<u}Q^\circ(abc;a),\\
 T_2^\circ&=\sum_{w\leq a<u\leq b<c<\sqrt{N/(ab)}}Q^\circ(abc;c).
 \tag{7}
\end{aligned}
\]
在好集合上原两套 lower weight 是逐指标不等式，故 (6) 不需例外项。
原 (2.3) 舍弃的 \(S_4(\beta,\sigma)\)、两次 lower-weight slack、
移动第九门的非负差仍在已知不等式的正确一侧；
本文不声称它们为零，也不把实际 prime remainder 删除。
这一步直接复用前稿 §3–§4 的展开，不重复因子分类。

### 2.2 承重恒等式：正第六项与负三重项一起换

对每个 \(z\leq c<w\leq d<u\)，按商的最小素因子展开：
\[
 Q^\circ(cd;z)=Q^\circ(cd;c)+
                           \sum_{z\leq a<c}Q^\circ(acd;a).
 \tag{8}
\]
因补数平方自由，新标签不会等于已选的 \(c,d\)；单位商在第一项中保留。
对全矩形求和，得到
\[
 \Upsilon_6^\circ-T_1^\circ
                  =\sum_{z\leq c<w\leq d<u}Q^\circ(cd;c).
 \tag{9}
\]
在**右边这个正和**按 \(cd<V\) 分区。令
\[
\begin{aligned}
 T_{1,\mathrm{mov}}^\circ
   &=\sum_{\substack{z\leq a<b<w\leq c<u\\bc<V}}Q^\circ(abc;a),\\
 O_6^\circ
   &=\sum_{\substack{z\leq c<w\leq d<u\\cd\geq V}}Q^\circ(cd;c)\geq0.
\end{aligned}
\]
在保留的正域再次使用 (8)，得到精确等式
\[
 \boxed{\ \Upsilon_6^\circ-T_1^\circ
           =K_6^\circ-T_{1,\mathrm{mov}}^\circ+O_6^\circ.\ }
 \tag{10}
\]
这就是 Wu04 原局部步骤在当前对象上的完整算式。
它既不是“删去一个负余项”，也不是倒用某个四重上界；
被舍弃的量若需舍弃，明确是 \(O_6^\circ\geq0\)。
全过程在同一 \(p\) 上成立，商为 1、素数或多因子粗数时均有效。

定义
\[
 \Delta_{2,\mathrm{mov}}^\circ=
 \sum_{z\leq a<b<c<v}Q^\circ(abc;b)
                 -T_0^\circ-T_{1,\mathrm{mov}}^\circ-T_2^\circ .
 \tag{11}
\]
那么 (10) 等价于
\[
 \Upsilon_6^\circ+\Delta_2^\circ
               =K_6^\circ+\Delta_{2,\mathrm{mov}}^\circ+O_6^\circ.
 \tag{12}
\]
因此可以在已接通的 (6) 中直接代入 (12)，不用返回一个尚未证明的
full-\(\Upsilon_6\) 最终母式。

## 3. 移动三重域确实产生原两个负四重项

令 \({\cal T}\) 为 \(z\leq a<b<c<v\) 的标签域，
\({\cal T}_0,{\cal T}_{1,\mathrm{mov}},{\cal T}_2\) 分别为
\(T_0^\circ,T_{1,\mathrm{mov}}^\circ,T_2^\circ\) 的域。
它们互不相交：依次是第三标签小于 \(w\)、第二标签小于 \(w\) 而第三标签
至少 \(w\)、第一标签至少 \(w\)。

它们都包含在 \({\cal T}\) 中。前两域使用 \(w<u<v\)；
第二域的 \(c<V/b\) 还自动给出 \(c<u\)，因为 \(b\geq z,V=zu\)。
第三域则使用原 Lemma 2.2 条件：
\[
 c<\sqrt{N/(ab)}
 \leq N^{(1-\beta-\sigma)/2}
 =N^{(1/2+3\alpha-\beta)/2}<v.
 \tag{13}
\]
对这三个域分别使用正三重项，只有前两域产生负差：
\[
 Q^\circ(abc;a)-Q^\circ(abc;b)
            =\sum_{a<q<b}Q^\circ(abcq;q).
 \tag{14}
\]
这里 \(q\) 是剩余商在 \([a,b)\) 内的最小素因子，等号 \(q=a\) 已由平方自由性
排除。单位商不在这个差中贡献，但并没有从其他槽中删掉。

第一域中把有序标签 \((a,q,b,c)\) 改名为 \((a,b,c,d)\)，给出
\[
 \sum_{{\cal T}_0}
       \{Q^\circ(abc;a)-Q^\circ(abc;b)\}=\Upsilon_{10}^\circ.
 \tag{15}
\]
第二域同样改名。原来的 \(bc<V\) 精确变成新标签的 \(cd<V\)，故
\[
 \sum_{{\cal T}_{1,\mathrm{mov}}}
       \{Q^\circ(abc;a)-Q^\circ(abc;b)\}=\Upsilon_{11}^\circ .
 \tag{16}
\]
在 (16) 的右端 \(d<V/c\leq u\)，不再需要额外的 \(d<u\)；
没有放宽原负四重域。反向换名把每个原 \(\Upsilon_{11}\) 标签唯一送回
\((a,c,d)\) 和新最小因子 \(b\)，所以无漏项、无额外重数。

第三域的差方向为
\[
                  Q^\circ(abc;b)-Q^\circ(abc;c)\geq0.
 \tag{17}
\]
因此，若把尚未使用的正量明确保留，
\[
\begin{aligned}
 R^\circ={}&
 \sum_{{\cal T}\setminus({\cal T}_0\cup{\cal T}_{1,\mathrm{mov}}\cup{\cal T}_2)}
                                              Q^\circ(abc;b)\\
 &+\sum_{{\cal T}_2}
                  \{Q^\circ(abc;b)-Q^\circ(abc;c)\}\geq0,
\end{aligned}
\]
便有**精确有限恒等式**
\[
 \boxed{\ \Delta_{2,\mathrm{mov}}^\circ
          =-\Upsilon_{10}^\circ-\Upsilon_{11}^\circ+R^\circ.\ }
 \tag{18}
\]
原未接通的有号缩域在这里已经付款：不是为旧 \(\Delta_2\) 宣称新下界，
而是先用原正项恒等式 (12)，再用新域的精确消去 (18)。
没有新增未付余额或付款假设。

## 4. 已证明的实际有限母式

把 (12)、(18) 代入 (6)，暂时保留 \(O_6^\circ+R^\circ\geq0\)，得
\[
\begin{aligned}
 4D_{1,2}(N)\geq{}&
 3\Upsilon_1^\circ+\Upsilon_2^\circ
 -\Upsilon_3^\circ-\Upsilon_4^\circ+\Upsilon_5^\circ+K_6^\circ\\
 &-2\Upsilon_7^\circ-\Upsilon_8^\circ-\Upsilon_9^\circ
 -\Upsilon_{10}^\circ-\Upsilon_{11}^\circ+O_6^\circ+R^\circ .
 \tag{19}
\end{aligned}
\]
取下界时可以舍弃最后两个非负项。平方重复及非互素异常仍使用原已付界，
而不假设所有补数都平方自由：

若 \((N-p,N)>1\)，则 \(p\mid N\)，只有 \(O(\log N)\) 个指标；
其余任何有贡献而不在 (5) 中的补数含某个 \(\ell\geq z\) 的平方，
指标数至多
\[
                 N\sum_{m\geq z}m^{-2}=O(N/z).
 \tag{20}
\]
每个标签至少为 \(z\)，所以每个补数的固定阶标签重数
有仅依赖 \(\alpha\) 的上界。所有相关商门都至少为 \(z\)；
第九门这一点由
\(\sqrt{N/(ab)}>N^{(1-\sigma)/4}>N^\alpha\) 保证。
所以 (20) 控制的是全部有号槽的带标签费用。
此处只对这个已识别的异常集合用整数上界，并未把主计数的素数指示函数
换成无条件 floor 大界。

因此存在常数 \(C>0,N_0\)，对所有偶数 \(N\geq N_0\)，有
\[
 \boxed{\begin{aligned}
 4D_{1,2}(N)\geq{}&
 3\Upsilon_1+\Upsilon_2-\Upsilon_3-\Upsilon_4+\Upsilon_5+K_6\\
 &-2\Upsilon_7-\Upsilon_8-\Upsilon_9-\Upsilon_{10}-\Upsilon_{11}
                       -C N^{1-\alpha}.
 \end{aligned}} \tag{F}
\]
这就是本轮实际消费者：它消费 (10)、(18)，删除未付的有号域义务，
不附加 `hpay` 或非单位商假设。误差量级、所有负系数和负域都保留原值。
单位商、高因子以及素补数或者仍在原槽中，或者只随已明确的非负量被取下界；
没有把它们当异常凭空删除。

本固定有理参数下，\(ab=V\) 不可能发生于互素素标签：
若发生，\((ab)^{2654}=N^{927}\)，则 \(a\mid N\)，矛盾。
同理固定幂次门的素数端点与 \(N\) 互素条件不相容。
原第九平方根门也不等于整数，否则 \(N=abq^2\)。
选中标签等于商筛门的差别只发生于 (20) 的重复异常。
这些端点事实确保计数开闭门没有被积分的零测边界理由替代。

**没有证明的更强式。** 从 \(K_6\leq\Upsilon_6\) 不能把 (F) 的正项换回
\(\Upsilon_6\)。本稿不作该推论；原 full-\(\Upsilon_6\) 字面最终命题
另列未证，但不再把它强加为消费作者最终系数的前置。

## 5. 原 \(C_6\) 与原 21 格 \(G_6\) 一个也不减少

本节证明积分的对象、域、权和阶梯支持一致，不用积分身份冒充实际下筛定理。

### 5.1 \(K_6\) 的指数域与经典项

令
\[
\begin{gathered}
 x=\frac{\log a}{\log N},\quad y=\frac{\log b}{\log N},\quad
 s(x,y)=\frac{1/2-x-y}{\alpha},\\
 {\cal D}=[\alpha,\beta]\times[\beta,\sigma],\qquad
 {\cal R}=\{(x,y)\in{\cal D}:x+y\leq\lambda\},\\
 {\cal K}_f(E)=4\iint_E
          \frac{f(s(x,y))}{xy(1/2-x-y)}\,dx\,dy .
 \tag{21}
\end{gathered}
\]
这里 \({\cal K}_f\) 只是积分表达式，不是计数下界的新假设。
离开零测边界，原正第六项的指数域为 \({\cal D}\)，
\(K_6\) 的指数域为 \({\cal R}\)。
由于 \(x\geq\alpha\)，\(x+y\leq\lambda\) 自动给出 \(y\leq\sigma\)；
而
\[
             {\cal R}={\cal D}\cap\{s\geq2\}.                   \tag{22}
\]

Wu08 (3.2)–(3.3) 定义 \(a(s)=sf(s)/(2e^\gamma)\)，其中经典下筛
\(f(s)=0\) 对 \(0<s\leq2\)。这里 \(C_6\) 指原 (5.5) 后 \(F_6\) 的
\(a\)-积分部分；用 \(y=1/2-x-\alpha s\) 将其写回原矩形，正是
\({\cal K}_a({\cal D})\)。原 \({\cal D}\) 上 \(s>0\)，故
\[
 \boxed{\ C_6={\cal K}_a({\cal D})={\cal K}_a({\cal R}).\ }       \tag{23}
\]
这证明整个原经典系数不变，不是用某个较小的新经典预算代替它。
等式本身没有声称 \(K_6\) 的实际计数下界已经由此自动证明。

### 5.2 原作者实际取用的 \(h\) 域

设 \(L=1/2-2\beta\)。原 §5 定义 \(G_6\) 的两块域是
\[
 {\cal A}=[\alpha,\beta]\times[\beta,L],\qquad
 {\cal B}=[\alpha,3\alpha/2]\times[L,\sigma].
 \tag{24}
\]
这就是 (5.5) 后那两个双积分，换元 \(y=1/2-x-\alpha s\) 后的实际域。
固定参数满足
\[
 \frac{3\alpha}{2}<\beta<L<\sigma,\qquad
 \frac{7\alpha}{2}-2\beta=\frac{2875}{136681}>0.
 \tag{25}
\]
所以 \({\cal A}\cup{\cal B}\subset{\cal D}\)。
反过来，若 \((x,y)\in{\cal R}\)，当 \(y\leq L\) 时它在 \({\cal A}\)；
当 \(y>L\) 时
\[
        x\leq\lambda-y<\lambda-L=2\beta-2\alpha<3\alpha/2,
 \tag{26}
\]
所以它在 \({\cal B}\)。由 (22) 得到准确的集合等式
\[
       ({\cal A}\cup{\cal B})\cap\{s\geq2\}={\cal R}.            \tag{27}
\]

据 Wu08 Lemma 3.1，\(h\geq0\)，且在 \([2,10]\) 上非增。
原作者最后估计 \(G_6\) 时已从 \(s=2\) 开始，仅使用
\[
 \widehat G_6={\cal K}_h({\cal R})
       \leq {\cal K}_h({\cal A}\cup{\cal B})=G_6.
 \tag{28}
\]
因此 (4) 删除的是 \(s<2\) 的正标签尾部，
**不是**删除作者最后 \(G_6\) 数值下界使用的任何部分。
这里无须恢复 (5.5) 最初较大的整个 \(G_6\) 积分，也没有把它冒认为不变。
真正保持的是作者最后取用的 \(\widehat G_6\) 及其原阶梯下界。

### 5.3 两个对数核和全部阶梯权的精确匹配

为核对 (28) 确是原最后表达式，而不只同名，令
\[
 S(s)=\frac12-\alpha s,\quad
 r_0=\frac{1/2-2\beta}{\alpha}=\frac{70331}{20600},\quad
 r_1=\frac{1/2-\alpha-\beta}{\alpha}=\frac{41453}{10300}.
 \tag{29}
\]
在 \(s\geq2\) 的截面 \(x+y=S(s)\) 上，\({\cal R}\) 的边界是
\[
       2\leq s\leq r_1,\qquad
       \alpha\leq x\leq\min\{\beta,S(s)-\beta\}.                 \tag{30}
\]
因为原 \(y\leq\sigma\) 的下门
\(x\geq S(s)-\sigma=\alpha(3-s)\leq\alpha\)，它不产生另一条截线。
在 \(s\leq r_0\) 时上门是 \(\beta\)，在 \(s\geq r_0\) 时上门是 \(S(s)-\beta\)。

反向参数化 \((x,s)\mapsto(x,y)=(x,1/2-x-\alpha s)\) 的绝对
Jacobian 为 \(\alpha\)，即 \(dx\,dy=\alpha\,dx\,ds\)，因此
\[
 {\cal K}_h({\cal R})
  =4\int_2^{r_1}\frac{h(s)}s
       \int_{\alpha}^{\min(\beta,S(s)-\beta)}
                                 \frac{dx}{x(S(s)-x)}\,ds .
 \tag{31}
\]
用代数恒等式
\[
 \frac1{x(S-x)}=\frac1S\left(\frac1x+\frac1{S-x}\right)
\]
写出截面端点差，不作新的数值求积，得
\[
\begin{aligned}
 w_-(s)&=\frac{1}{s(1-2\alpha s)}
  \log\frac{\beta(1-2\alpha-2\alpha s)}
                 {\alpha(1-2\beta-2\alpha s)},\\
 w_+(s)&=\frac{1}{s(1-2\alpha s)}
  \log\frac{(1-2\alpha-2\alpha s)(1-2\beta-2\alpha s)}
                 {4\alpha\beta},\\
 \boxed{\ \widehat G_6
      =8\int_2^{r_0}w_-(s)h(s)\,ds
                      +8\int_{r_0}^{r_1}w_+(s)h(s)\,ds.\ }
 \tag{32}
\end{aligned}
\]
正系数和因子 8 均由 (31) 确定，不是重命名原打印数。
两个 \(w_\pm\) 是非负截面积分的表达式，所以其非负性不依赖小数近似。
这正好是 Wu08 最后 \(G_6\geq\cdots\) 的两个对数核和原分界。

令原 \(s_i=2+i/10\)。精确关系是
\[
 s_{14}<r_0<s_{15},\qquad s_{20}<r_1<s_{21}.
 \tag{33}
\]
于是原所有权可完整写为
\[
\begin{aligned}
 g_6^i&=\int_{s_{i-1}}^{s_i}w_-(s)\,ds &&(1\leq i\leq14),\\
 g_6^{15}&=\int_{s_{14}}^{r_0}w_-(s)\,ds
                             +\int_{r_0}^{s_{15}}w_+(s)\,ds,\\
 g_6^i&=\int_{s_{i-1}}^{s_i}w_+(s)\,ds &&(16\leq i\leq20),\\
 g_6^{21}&=\int_{s_{20}}^{r_1}w_+(s)\,ds .
 \tag{34}
\end{aligned}
\]
对每格，\(2\leq s\leq s_i\leq4.1<10\)，原非增性给
\(h(s)\geq h(s_i)\)。第 15 格的两个子段使用同一个右端点；
第 21 格虽提前在 \(r_1\) 截止，仍用原 \(h(s_{21})\)，没有换成更强值。
所以
\[
 \boxed{\ \widehat G_6\geq
           G_{6,\mathrm{step}}:=8\sum_{i=1}^{21}g_6^ih(s_i).\ }   \tag{35}
\]
式 (34) 的积分定义、域、权、取值点与原文逐项一致。
原 \(G_{6,\mathrm{step}}\geq0.060469\) 的输入等级和其余原数值方向，
按父级已完成的数值来源账消费；本轮不重算、不把打印值改成新认证。

特别地，保留域仍含
\[
 \alpha<x<1/4-2\alpha,\qquad 1/4<y<\lambda-x,
 \quad\text{宽度 }1/4-3\alpha=\frac{127}{5308}>0.                \tag{36}
\]
所以本文没有实施任何 \(y<1/4\) 剪收益。
该高域的解析适用性没有因 (27)–(35) 的集合／积分身份被自动解决。

## 6. 第九项直接消费父级小补正

前稿已证明：在 (3) 的同一标签域上，以固定门 \(v\) 定义 \(J_9\)，有
\[
 \Upsilon_9=J_9+O(N^{1-\eta_9}),\qquad
                    \eta_9=\frac{473}{15924}>0.                \tag{37}
\]
单位商在差中抵消，小商差保留标签至多
\(2N^{5/6+\sigma/2}\)；这些已接纳的推导不重做。
有限式 (F) 不换第九门，只有解析上界使用 (37)。

前稿 (P32a) 曾把 \(z_{\rm sieve}=N^{1/2}\) 直接用于 Wu04 Lemma 2.2，
不满足该引理的 \(z_{\rm sieve}\leq\sqrt Q\)。
按父级补正，令
\[
 Q_{\rm lev}=\frac{N^{1/2}}{\log^B N},\qquad
                 z_*=\sqrt{Q_{\rm lev}}.
 \tag{38}
\]
原输出素数 \(p>\sqrt N\) 仍通过 \(z_*\) 筛；
若先写 \(S({\cal B};\sqrt N)\)，使用
\[
                S({\cal B};\sqrt N)\leq S({\cal B};z_*).
 \tag{39}
\]
在 \(z_*\) 上合法调用同一原线性上筛，
\(\log Q_{\rm lev}/\log z_*=2,\ F(2)=e^\gamma\)。
Mertens 局部乘积给
\[
 V_N(z_*)\leq(2e^{-\gamma}+o(1))C_N/\log z_*,
       \qquad\log z_*/\log N\longrightarrow1/4.
 \tag{40}
\]
故主系数仍为 \(8C_N X/\log N\)。原小输出费用不变；
非互素标签余项仍单独付
\(R_4=O(N^{1-\beta}\log^2N)\)，不假定它不存在。
其余模数平均按前稿已代入的 Wu04 Lemma 2.3 第一条消费。
于是原
\[
 C_9=8\int_\beta^\sigma
       \frac{\log((1-x-\sigma)/\sigma)}{x(1-x)}\,dx
\]
仍给出 \(\Upsilon_9\leq(C_9+o(1))\Theta(N)\)。
这只是修正已用引理的筛门，不另造筛法，也不改变 (F) 的负计数对象。

## 7. 交给父级和 M3 的已证明结论及边界

令
\[
 \Theta(N)=C_NN/\log^2N,\quad
 C_N=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
        \prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2},
\]
乘积中的 \(\ell\) 均为素数。因 \(C_N\) 有正绝对下界，
(F)、(37) 的上幂次误差均为 \(o(\Theta)\)。

**本轮已经证明的有限输入**是 (F)，而不是一个带付款假设的版本。
**已经证明的系数支持输入**是 (23)、(27)、(32)–(35)：
新实际正槽 \(K_6\) 的域完整承载原 \(C_6+G_{6,\mathrm{step}}\)，
原两个负四重积分的对象和系数均不变。

解析合装时，第六项需作用于这个精确实际对象：
\[
\begin{gathered}
 \forall\varepsilon>0\ \exists N_0\
 \forall N\geq N_0\ (N\text{ 偶}),\\
 \sum_{\substack{z\leq a<w\leq b<u\\ab<V}}Q(ab;z)
       \geq (C_6+G_{6,\mathrm{step}}-\varepsilon)\Theta(N).
 \tag{A6}
\end{gathered}
\]
这是移交 M3 的原第六项解析调用在最终实际使用支持上的精确表述，
**本稿没有证明 (A6)，也没有把它添作有限定理 (F) 的假设**。
仅有全 \(\Upsilon_6\) 的总下界不能倒推 (A6)；
可用的解析证明必须确实作用于 (4) 的保留域，或者给出等价的有号消费。
反过来，不需要为本稿恢复 \(s<2\) 上作者最终没有使用的更大收益。
这划清有限支持证明与计数适用证明，不重复 M3 的解析工作。

父级
[`ORIGINAL-NUMERIC-COMPLETION.md`](../ORIGINAL-NUMERIC-COMPLETION.md)
已经在原系数账上，用修正方向的 \(G_2\) 和同对象四重上界 \(851/1250\)，得到
\[
 c_{\rm bound}=\frac{179839833}{200000000},\qquad
 c_{\rm bound}-\frac{899}{1000}=\frac{39833}{200000000}>0.
 \tag{41}
\]
由于 (23)、(35) 没有更换该账中任何第六项数值，有限补正无需重算预算，
也无需查原计算工作表才继续。这里引用的是父级已明确等级的数值结论；
它不能代替 (A6)。

结论分账如下：

| 命题 | 本轮状态 |
|---|---|
| Wu08 字面 full-\(\Upsilon_6\) 最终 Lemma 2.2 | 未证明，不据此判错 |
| Wu04 原操作支持的明确中间式补正 | (10)、(12)、(18) 已证明 |
| 实际无残项有限母式，唯一改动正槽为 \(K_6\) | (F) 已证明 |
| 原最终全部 \(C_6,G_{6,\mathrm{step}}\) 支持不减 | (23)、(27)、(32)–(35) 已证明 |
| 原第九实际上界及合法筛门 | 消费已接纳的 (37) 与父级补正 (38)–(40) |
| 原有号数值账 | 父级已接通，本轮无需重做 |
| 第六项实际解析下界 | (A6) 由 M3 继续，本文不声称已证 |
| Wu 计数下界及 1.894 全路线 | 尚未在本文合装完成 |

## 原文定位与本阶段记录

以下路径相对于 `research/wu2008/`：

* `sources/Wu08.tex`，Lemma 2.2 全文，尤其 (2.3)–(2.6) 和随后三个三重域；
  §3 (3.2)–(3.3)、Lemma 3.1(iv)、原 \(s_i\)；
  §5 (5.5) 后两块 \(G_6\) 积分及最后的 \(g_6^1,\ldots,g_6^{21}\) 定义。
* `sources/Wu04.tex`，(9.2) 的逐补数商条件，
  (9.6) 后“\(N^\rho\geq N^{1/2-2\kappa_1}/p_1\)”至 (9.7)，
  以及 (9.8)–(9.9) 的三域归并；Lemma 2.2 的 \(z\leq\sqrt Q\)。
* `proofs/NINTH-SIEVE-CORRECTION.md`，
  `proofs/ORIGINAL-NUMERIC-COMPLETION.md`。

本阶段只做上述自然语言推导、原文阅读和固定有理符号核算。
未修改或运行 Lean/Lake/gate/构建／内核，未新增数值求积、扫描、优化、
代理或外部通信。旧稿不改，旧失败证据不删。
