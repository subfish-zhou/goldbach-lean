> **Checkpoint status:** parent-reviewed back-half implication under explicitly cited classical inputs.
> 本文保存该阶段的数学正文；文中旧的完成声明不覆盖本检查点状态。引用输入、候选证明和已确认结果分别记账。

# 在 Wu 输入下的 1.894 后半桥

## 0. 结论、引用边界与目标

本证明以 Wu 的**实际普通 Chen 计数定理**
\[
 D_{1,2}(N)\ge \frac{899}{1000}\frac{C_NN}{\log^2N}
 \tag{W}
\]
为明确文献输入，证明对所有充分大的偶数 \(N\)，
\[
 D_{1,947/500}(N)>
 \frac1{400}\frac{C_NN}{\log^2N}>0.                 \tag{T}
\]
这里两边均计不同的素数 \(p\)，而不是未经排序的因子对重数；
右侧计数的每个 \(p\) 均给出
\[
 N=p+rq,\qquad p,q\text{ 为素数},\quad
 r=1\text{ 或素数},\quad r\le q^{447/500}.
\]
因此指数是 \(947/500=1.894\)，不是 1.8938。

这是**在 (W) 下完成的自然语言后半桥**。另外引用两个经典定理：
Pan–Ding 加权 Bombieri–Vinogradov 定理和 Rosser–Iwaniec 一维上筛，
其实际使用形式、参数和适用资格在第 3 节逐项写出。
素数定理和 Mertens 定理也按其标准无条件形式引用。
从这些引用到 (T) 的计数分解、坏表示上界、归一化和正余量在本文证明。
本文没有独立重建 (W)；该上游工作属于 M1。因此不能把本文称为
项目中整条 1.894 路线已独立重建，更不能称为“只剩 Lean”。

Li–Liu 正文 Theorem 1.1 的指数为 1.9，紧随的 remark 才声称可改为
1.894。本文不把该 remark 当作 (T) 的证明，也不把旧 0.8982 预算、
原四行全核反馈或最优 \(H/h\) 恢复当作必要前提。

## 1. 相同计数对象与相同奇异级数

所有对数均为自然对数，素因子按重数计入 \(\Omega\)，且
\(\Omega(1)=0\)。令
\[
 C_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right),\qquad
 C_N=C_2\prod_{\substack{\ell\mid N\\\ell>2}}
                  \frac{\ell-1}{\ell-2},\qquad
 \Theta(N)=\frac{C_NN}{\log^2N}.                    \tag{1}
\]
产品中的 \(\ell\) 均为素数。这正是 Wu08 (1.2) 和 Li–Liu (1.3)
的规范；**没有另外乘 2**。例如二素数 Hardy–Littlewood 主项在此
规范下是 \(2\Theta(N)\)，不是 \(\Theta(N)\)。

这里 \(C_N\ge C_2\ge1/2\)。最后一个下界可直接由
\[
 \prod_{k=2}^{M}(1-k^{-2})=\frac{M+1}{2M}\longrightarrow\frac12
\]
得到，因为 \(C_2\) 只取上述 \((1-k^{-2})\) 因子的一部分。
故所有固定的 \(O(N^b\log^jN)\)、\(b<1\)，均为 \(o(\Theta(N))\)，
对偶数 \(N\) 一致；特别地 \(\Theta(N)\to\infty\)。

对偶数 \(N\ge4\)，定义
\[
 W(N)=\#\{p<N:p\text{ 素数},\ \Omega(N-p)\le2\}.
\]
Wu 用 \(p\le N\)；由于这样的 \(N\) 不可能为素数，两个定义相同。
因此不存在 \(p=N\) 或对零补数调用 \(\Omega\) 的问题。
唯一的单位补数为 \(N-p=1\)，其贡献
\[
 U_N=\mathbf1_{\{N-1\text{ 为素数}\}}\le1            \tag{2}
\]
必须另扣。单位补数不是目标中的 \(r=1\) 情形：后者要求
\(N-p=q\) 本身为素数。

固定 \(3/2<a<2\)，置
\[
 \beta=a-1,\qquad \tau=\frac{\beta}{1+\beta}
                  =\frac{a-1}{a},\qquad
 \frac13<\tau<\frac12.
\]
令
\[
 G_a(N)=\#\{p<N:p\text{ 素数},\
       N-p=rq,\ q\text{ 素数},\
       r=1\text{ 或素数},\ r\le q^\beta\}.
\]
这就是 Li–Liu (4.4) 的 \(D_{1,a}(N)\)。

若补数为素数 \(q\)，则取 \(r=1\)，且 \(1\le q^\beta\)，全数为好表示。
若补数有恰好两个素因子，则唯一写成有序形式 \(rq\)，其中
\(r,q\) 为素数且 \(r\le q\)。由于 \(0<\beta<1\)，任何满足目标的
非单位分解必有 \(r\le q^\beta<q\)，所以倒换两个素因子不能把一个
坏表示变成好表示。平方 \(r=q\) 是坏表示，且只计一次。

令 \(B_a(N)\) 为以下有序三元组的数目：
\[
 p,r,q\text{ 素数},\quad N=p+rq,\quad
 r\le q,\quad q^\beta<r.                           \tag{3}
\]
由唯一分解，\((p,r,q)\mapsto p\) 在 (3) 上单射。于是有**精确等式**
\[
 W(N)=G_a(N)+B_a(N)+U_N.                           \tag{4}
\]
这不是把一个不同重数的三元组和普通 Chen 计数作形式相减。
当补数为素数时，交换两个加数可能给出另一个 \(p\)，但 Wu 和
Li–Liu 都以 \(p\) 为计数索引，两侧一致，不应再除以 2。

## 2. 坏域与固定比例截断

固定 \(0<\eta<1/2\)，先于 \(N\) 的极限选择它。按
\[
 rq\le\eta N,\qquad rq>\eta N
\]
把 (3) 精确分成 \(B_{\rm small}\) 和 \(B_{\rm large}\)。
下端闭、上端开，等号不会遗漏或重复。

记 \(v=rq\)。坏条件给出
\[
 q<r^{1/\beta},\qquad
 v<r^{1+1/\beta}=r^{1/\tau},
 \qquad r>v^\tau,\qquad r\le\sqrt v.                \tag{5}
\]
因此大乘积坏表示满足
\[
 \eta^\tau N^\tau<r\le\sqrt N.                      \tag{6}
\]
在乘积块 \(H<v\le2H\) 中则满足
\[
 H^\tau<r\le\sqrt{2H}.                             \tag{7}
\]
本文保留 (6) 中真实的固定系数 \(\eta^\tau\)，不把它冒充为 1。

先统一处理 \((r,N)>1\)。由于 \(r\) 为素数，必有 \(r\mid N\)，进而
\(r\mid p=N-rq\)，所以 \(p=r\)，且 \(q=N/r-1\) 被唯一确定。
这种坏表示总共至多
\[
 \omega(N)\le\log_2N=o(\Theta(N)).                  \tag{8}
\]
以下上筛只对 \((r,N)=1\) 的表示进行。这个异常项全局只需扣一次。
当 \(p=2\) 时，偶数乘积 \(N-2=rq\) 的小素因子为 \(r=2\)，也已在
(8) 内。**不额外假设 \((q,N)=1\)**，因此没有未付的第二个互素截断。

## 3. 实际换位序列及常数 8

### 3.1 两个经典定理的准确使用形式

**加权均值定理。** 引用 Wu04 作者 TeX Lemma 2.3 的第一条；
Wu 将其归于 Pan–Ding，并注明使用 Pan–Pan 的 Corollary 8.12 形式。
设固定 \(\alpha\in(0,1)\)、\(A>0\)，且 \(|f(m)|\le1\)。定义
\[
 E(y;d,b,m)=
 \#\{q:q\text{ 素数},\ mq\le y,\ mq\equiv b\pmod d\}
 -\frac{\operatorname{li}(y/m)}{\varphi(d)}.
\]
存在 \(B\) 使得
\[
 \sum_{d\le x^{1/2}/\log^Bx}\!
 \mu^2(d)3^{\omega(d)}
 \max_{y\le x}\max_{(b,d)=1}
 \left|\sum_{\substack{m\le x^{1-\alpha}\\(m,d)=1}}
                  f(m)E(y;d,b,m)\right|
 \ll_{A,\alpha}\frac{x}{\log^Ax}.                  \tag{9}
\]
常数对这类有界系数一致。只用第一条的普通乘积端点 \(y\)，不需要
第二、三条移动素数端点的额外资格，更不使用分布水平 \(>1/2\)。
本文所有实际调用均在
\(\operatorname{li}(t)=\int_2^t du/\log u\)、\(t>2\) 的范围内，
不依赖它在小参数处的延拓约定。
本文固定 \(\alpha=1/3\)、\(A=4\)，支持实际在 \(m\le\sqrt x\)
内，故满足 \(m\le x^{2/3}\)。两次调用分别取 \(y=y_+\) 和 \(y=y_-\)。
因为 (9) 对所有既约剩余类取最大值，下面可以令 \(b=N\bmod d\)，
**即使在小乘积块中 \(N\) 远大于 \(x\)**。这不是仅对小固定剩余类
成立的 BFI 定理。

**一维上筛。** 引用 Wu04 Lemma 2.2，即 Rosser–Iwaniec 线性筛：
若有限序列（保留索引重数）
\[
 |\mathcal A_d|=g(d)X+R_d,\quad
 V(z)=\prod_{\ell<z}(1-g(\ell)),
\]
其中 \(g\) 在无平方因子筛模数上为乘法函数，满足
\(0\le g(\ell)<1\) 及
\[
 \frac{V(w)}{V(z)}
 \le\frac{\log z}{\log w}\left(1+\frac K{\log w}\right)
 \quad(2\le w\le z),                               \tag{10}
\]
则对固定筛误差参数 \(0<\rho<1/8\)、\(z\le D^{1/2}\)，
\[
 S(\mathcal A,z)\le XV(z)\{F(\log D/\log z)+E_\rho\}
       +\sum_{\ell<L_\rho}\sum_{d\mid P(z)}
                          \lambda_\ell^+(d)R_d,    \tag{11}
\]
其中 \(\lambda_\ell^+\) 为 level \(D\)、order 1 的权，因而
\(|\lambda_\ell^+(d)|\le1\)、\(d>D\) 时为零；
\(L_\rho\) 仅依赖 \(\rho\)，
\[
 E_\rho\ll\rho+\rho^{-8}e^K(\log D)^{-1/3},
 \qquad F(2)=e^\gamma.
\]
因此余项绝对值至多
\(L_\rho\sum_{d\le D,\ d\mid P(z)}|R_d|\)。
不把 well-factorability 当作免费的更高分布水平使用。
筛不等式对索引序列成立，因为筛权逐项求和；相同整数的不同索引
不能先合并。若 \(X\le1\)，直接用模数 \(d=1\) 的余项控制整个序列，
见下文，因而不用违背原文 \(X>1\) 的假设。

### 3.2 在本问题上核对余项和局部密度

以下 \(N\) 为偶数，\(x\le N\)。取素数载体
\(\mathcal R\subseteq[2,\sqrt x]\)，其中每个 \(r\) 满足 \((r,N)=1\)。
考虑有索引的实际素数对序列
\[
 \mathcal A=\bigl(N-rq\bigr)_{
    r\in\mathcal R,\ q\ {\rm prime},\
    y_-<rq\le y_+},\qquad
 0<y_-<y_+\le x,                                   \tag{12}
\]
并令
\[
 X=\sum_{r\in\mathcal R}
      \{\operatorname{li}(y_+/r)-\operatorname{li}(y_-/r)\}.
                                                               \tag{13}
\]
所有应用中 \(y_-/r\to\infty\)，故 (13) 是非负的真实两端质量。
令
\[
 D=\frac{\sqrt x}{\log^Bx},\qquad
 z=\sqrt D,\qquad
 P_N(z)=\prod_{\substack{\ell<z\\\ell\nmid N}}\ell.
                                                               \tag{14}
\]
稍后选用的载体均满足 \(r>z\)。于是对每个 \(d\mid P_N(z)\)，
\((r,d)=1\) 自动成立；同时 \((N,d)=1\)。故
\[
 |\mathcal A_d|=\frac X{\varphi(d)}+R_d,\qquad
 R_d=\sum_{r\in\mathcal R}
       \{E(y_+;d,N,r)-E(y_-;d,N,r)\}.               \tag{15}
\]
这是共同 \(X\) 的精确分解，没有遗漏 \(r\mid d\) 的主项。
将 \(f=\mathbf1_{\mathcal R}\) 代入 (9)，用三角不等式并去掉非负权，
得到
\[
 \sum_{\substack{d\le D\\d\mid P_N(z)}}|R_d|
       \ll\frac{x}{\log^4x}.                       \tag{16}
\]
两个乘积端点均是“严格下端、闭上端”，因此 (15) 不含未付端点原子。

实际局部密度为
\[
 g_N(\ell)=
 \begin{cases}1/(\ell-1),&\ell\nmid N,\\0,&\ell\mid N.\end{cases}
\]
特别地 \(g_N(2)=0\)，筛维数为 1。令
\[
 V_N(z)=\prod_{\substack{2<\ell<z\\\ell\nmid N}}
                      \left(1-\frac1{\ell-1}\right).
\]
从全部奇素数的产品中删除 \(\ell\mid N\) 的因子，只会减小
\(V_N(w)/V_N(z)\)。Mertens 乘积定理故给出 (10)，其中 \(K\) 对
\(N\) 一致。再利用逐因子恒等式
\[
 1-\frac1{\ell-1}
   =(1-1/\ell)\left(1-\frac1{(\ell-1)^2}\right)
\]
及 Mertens 定理，得到真正需要的**单边**关系
\[
 V_N(z)\le
   (2e^{-\gamma}+o(1))\frac{C_N}{\log z}.           \tag{17}
\]
一致性可直接核对：有限乘积只含 \(\ell\mid N,\ell<z\) 的修正因子，
完整 \(C_N\) 还含其余大素因子的、均大于 1 的修正因子；而
\(C_2\) 的截断误差为 \(1+O(1/z)\)。所以 (17) 对偶数 \(N\) 一致，
无需错误地宣称有限产品与完整 \(C_N\) 恒等。

此处 \(\log D/\log z=2\)，且
\[
 \log z=\tfrac14\log x-\tfrac B2\log\log x.
\]
先固定很小的 \(\rho\)，再令 \(x\to\infty\)，由 (11)、(16)、(17)，
对任意固定 \(\kappa>0\) 得到
\[
 S(\mathcal A;P_N,z)
 \le(8+\kappa)\frac{C_NX}{\log x}
           +O_\kappa\!\left(\frac{x}{\log^4x}\right)
 \quad(x\ge x_0(\kappa)).                          \tag{18}
\]
常数对上述载体和偶数 \(N\ge x\) 一致。主常数完整地来自
\[
 \underbrace{2e^{-\gamma}}_{\text{奇素数局部产品}}
 \ \underbrace{e^\gamma}_{F(2)}\
 \underbrace{4}_{\log x/\log z}\ =8.               \tag{19}
\]
固定 \(L_\rho\) 先于 \(x\)，因而不会把 (16) 的误差放大成主项。
如 \(X\le1\)，(15) 在 \(d=1\) 给
\(|\mathcal A|\le1+O(x/\log^4x)=O(x/\log^4x)\)，
也满足 (18) 这种带余项的上界。空载体同样无问题。

序列 (12) 并不全是素数，但我们只把真实素数输出送入它。
素数 \(p=N-rq\ge z\) 一定通过筛。遗漏的 \(p<z\) 至多贡献
\[
 2\lceil z\rceil                                  \tag{20}
\]
个索引：对于每个固定 \(p\)，整数 \(N-p\) 至多有两个有序素因子对。
即使为了上界放宽了 \(r\le q\)，也不会超过这个重数。
平方时只有一个索引。不需先把一个 quotient-sifted 集合误认成素数集，
因此没有该路线中的复合余因子异常。

## 4. 大乘积坏表示的尖锐单边上界

在 (12) 中取
\[
 x=N,\quad y_-=\eta N,\quad y_+=N,\quad
 \mathcal R=\{r\text{ 素数}:
             \eta^\tau N^\tau<r\le\sqrt N,\ (r,N)=1\}.
                                                               \tag{21}
\]
这里 \(\eta\) 固定且 \(\tau>1/3>1/4\)，所以最终所有 \(r>z\)，
满足第 3 节全部条件；\(y_-/r\ge\eta\sqrt N\to\infty\)。
原大乘积坏表示的非异常部分由 (6) 注入此序列的素数输出。
不再要求新序列中的每个索引都满足 \(r\le q\) 或 \(q^\beta<r\)：
这里只作正向上界扩张，方向合法。
上端 \(rq=N\) 不会出现，因为载体要求 \((r,N)=1\)。

记其质量为 \(X_N\)。丢掉非负的下端质量，再去掉互素限制，给
\[
 X_N\le
 \sum_{\eta^\tau N^\tau<r\le\sqrt N\atop r\ {\rm prime}}
                         \operatorname{li}(N/r).
\]
素数定理和分部求和给出
\[
 \sum_{cN^\tau<r\le\sqrt N\atop r\ {\rm prime}}
                         \operatorname{li}(N/r)
 =\frac N{\log N}
      \left\{\int_\tau^{1/2}\frac{du}{u(1-u)}
                   +o_{c,\tau}(1)\right\}          \tag{22}
\]
对每个固定 \(c>0\) 成立。为明确端点与测度，设 \(L=\log N\)：
在这个区间内，
\[
 \operatorname{li}(N/r)=
 \frac{N}{rL(1-\log r/L)}(1+O(1/L)).
\]
由素数定理分部求和，对任何固定 \(0<u_0<v_0<1\)，
\[
 \sum_{N^{u_0}<r\le N^{v_0}\atop r\ {\rm prime}}
       \frac1{r(1-\log r/L)}
 \longrightarrow\int_{u_0}^{v_0}\frac{du}{u(1-u)}.
\]
这也可由 Mertens 和连续测试函数分部求和得到。实际下端指数为
\(\tau+\log c/L\to\tau\)；夹在任意固定的
\(\tau-h,\tau+h\) 之间，再令 \(h\downarrow0\)，证明 (22)。
所以没有忽略固定 \(c=\eta^\tau\) 引起的端点变化。

置
\[
 I(\tau)=\int_\tau^{1/2}\frac{du}{u(1-u)}.
\]
由 (18)、(20)、(22)、(8)，先把筛精度固定得足够好，再令 \(N\)
充分大，得到对每个固定 \(a,\eta\) 和每个 \(\epsilon>0\)，
\[
 B_{\rm large}(N)
 \le\{8I(\tau)+\epsilon\}\Theta(N).                \tag{23}
\]
其阈值可以依赖 \(a,\eta,\epsilon\)。这里 (16) 的
\(O(N/\log^4N)\)、(20) 的 \(O(N^{1/4})\) 及 (8) 的
\(O(\log N)\) 都除以 \(\Theta(N)\) 后趋于零。
本节没有假设 \(p\) 被限制在某个固定比例的区间内。

## 5. 小乘积不能直接丢弃：一致的 \(O_a(\eta)\) 上界

先证明对 \(H\) 充分大、\(2H\le N\)，在块
\[
 H<rq\le2H
\]
内、满足 (3) 且 \((r,N)=1\) 的实际坏表示数有上界
\[
 C_a\,\frac{C_NH}{\log^2H},                        \tag{24}
\]
其中 \(C_a>0\)、最低 \(H_0(a)\) 与 \(N/H\) **无关**。

具体在 (12) 取
\[
 x=2H,\quad y_-=H,\quad y_+=2H,\quad
 \mathcal R_H=\{r\text{ 素数}:
                     H^\tau<r\le\sqrt{2H},\ (r,N)=1\}.
\]
(7) 保证实际坏表示被包含。所有 \(r\le\sqrt x\le x^{2/3}\)；
\(r>H^\tau>z_x\) 最终成立，且
\[
 H/r\ge\sqrt{H/2}\longrightarrow\infty.
\]
因此 (9)–(20) 全部适用。唯一可能很大的参数是剩余类 \(N\)；
(9) 对既约剩余类的最大值以及 (17) 的一致单边估计已经支付它，
不能在此改用只控制小剩余类的定理。

质量用解析上界即可，不作任何求积：
\[
 \begin{aligned}
 X_H
 &\le\sum_{H^\tau<r\le\sqrt{2H}\atop r\ {\rm prime}}
                  \int_{H/r}^{2H/r}\frac{dt}{\log t}\\
 &\ll\frac H{\log H}
       \sum_{H^\tau<r\le\sqrt{2H}\atop r\ {\rm prime}}\frac1r
 \ll_a\frac H{\log H}.                            \tag{25}
 \end{aligned}
\]
最后一步由 Mertens
\(\sum_{r\le t,\ r\ {\rm prime}}1/r=\log\log t+M+o(1)\)：
两端差趋于 \(\log(1/(2\tau))\)，故一致有界。
将 (25) 代入 (18)，固定例如 \(\kappa=1\)，用 \(C_N\ge1/2\)
吸收 \(O(H/\log^4H)\) 与 \(2\lceil z_x\rceil=O(H^{1/4})\)，
即得 (24)。这里只需由已写出的估计存在一个固定 \(C_a\)，没有把
一个未经证明的预算常数当作输入。

现固定 \(\eta\)，取二进乘积块
\[
 H_j=\frac{\eta N}{2^{j+1}},\qquad
 j=0,\ldots,J,\qquad H_J\ge\sqrt N>H_{J+1}.
\]
对充分大 \(N\)，这个有限列表存在；各块 \((H_j,2H_j]\)
两两不交，覆盖 \((H_J,\eta N]\)，且
\[
 H_J<2\sqrt N,\qquad
 \log H_j\ge\tfrac12\log N,\qquad
 \sum_{j=0}^J H_j<\eta N.
\]
用 (24) 求和可得
\[
 \sum_{j=0}^J B(H_j,2H_j)
 \le4C_a\,\eta\,\Theta(N).
\]
剩余 \(rq\le H_J<2\sqrt N\) 的坏表示至多 \(2\sqrt N+1\) 个，
因为每个整数补数只有一个排好序的素因子对，对应唯一的 \(p\)。
再加上全局例外 (8)，得到
\[
 B_{\rm small}(N)
 \le K_a\eta\,\Theta(N)+O(\sqrt N+\log N),\qquad
 K_a=4C_a.                                        \tag{26}
\]
所有块都满足 \(H_j\ge\sqrt N\)，故只要 \(N\) 足够大，就同时满足
同一个 \(H_0(a)\)；并未对增长的块数无根据地使用逐块 \(o(1)\)。

这里先有固定 \(K_a\)，然后才选固定 \(\eta\)；绝不令
\(\eta=\eta(N)\)。例如给定总容差 \(\epsilon>0\)，先取
\[
 0<\eta<\min\left(\frac12,\frac{\epsilon}{4K_a}\right).
\]
再把 \(N\) 取大，使 (26) 的余项至多
\(\epsilon\Theta(N)/4\)，则
\(B_{\rm small}\le\epsilon\Theta(N)/2\)。
另以容差 \(\epsilon/2\) 调用 (23)。两部分的互素异常即使保守地
各上界一次也仍为 \(o(\Theta)\)；在精确分解中它们本来不交。
因此已经证明：
\[
 \boxed{\quad
 \forall a\in(3/2,2)\ \forall\epsilon>0\
 \exists N_0(a,\epsilon)\
 \forall N\ge N_0,\ N\ {\rm even}:\quad
 B_a(N)\le
       \left(8\int_\tau^{1/2}\frac{du}{u(1-u)}
                                  +\epsilon\right)\Theta(N).
 \quad}                                           \tag{27}
\]

## 6. 实际 Chen 计数消费者及最弱标量需求

积分在此可精确解析求出，无须数值积分：
\[
 I(\tau)
  =[\log u-\log(1-u)]_\tau^{1/2}
  =\log\frac{1-\tau}{\tau}
  =\log\frac1{a-1}.                                \tag{28}
\]
由精确计数等式 (4)、(27) 和 \(U_N\le1=o(\Theta(N))\)，得到对任意
\(\epsilon>0\)、所有充分大偶数 \(N\) 的**真实计数不等式**
\[
 \boxed{\quad
 G_a(N)\ge W(N)-
       \left(8\log\frac1{a-1}+\epsilon\right)\Theta(N).
 \quad}                                           \tag{29}
\]
单位补数可具体用 \(\epsilon/2\) 付款，(27) 也用 \(\epsilon/2\)；
没有隐藏的单位或零补数约定。

故一个足够且只涉及普通计数的输入是
\[
 W(N)\ge c\,\Theta(N)\quad\text{最终成立},\qquad
 c>c_*(a):=8\log\frac1{a-1}.                        \tag{30}
\]
更弱地，只需
\(\liminf_{N\to\infty,\ N\ {\rm even}}W(N)/\Theta(N)>c_*(a)\)。
这就是本文扣除证书所需的最小类型输入：**一个同对象、同规范的
实际普通 Chen 计数下界**。它不要求完整 \(H\) 函数、任何自选节点表、
全核功能比较或逐盒 Gamma5 改善作为本后半桥的附加前提。
如何独立产生这个标量属于上游；不能用条件接口代替它。

\(c_*(a)\) 是此单边扣除法的严格分离阈值，不是所有证明方法的
必要阈值，也不声称 \(c=c_*(a)\) 时实际表示不存在。
若输入只是一个较弱下界 \(c\le c_*(a)\)，只能说**仅凭这个下界和
(27) 不能推出正余量**，不能说真实计数不够。

## 7. 1.894 的严格正余量：完全有理的解析证书

现在固定
\[
 a=\frac{947}{500},\quad \beta=\frac{447}{500},
 \quad\tau=\frac{447}{947}.
\]
其范围资格可精确核对：
\[
 \tau-\frac13=\frac{394}{2841}>0,\qquad
 \frac12-\tau=\frac{53}{1894}>0.
\]
置 \(t=53/947\)，则
\[
 \log\frac{500}{447}
    =\log\frac{1+t}{1-t}
    =2\sum_{j=0}^{\infty}\frac{t^{2j+1}}{2j+1},
 \qquad 0<t<1.                                    \tag{31}
\]
这可由等比级数 \(1/(1-u^2)\) 在 \([0,t]\) 一致收敛后积分得到。
对于 \(j\ge1\)，\(1/(2j+1)\le1/3\)，所以
\[
 16\left(t+\frac{t^3}{3}\right)
 <8\log\frac{500}{447}
 \le16\left(t+\frac{t^3}{3(1-t^2)}\right).
\]
固定有理式的精确值和差为
\[
 \begin{aligned}
 16\left(t+\frac{t^3}{3}\right)
      &=\frac{2283864128}{2547834369},\\
 \frac{2283864128}{2547834369}-\frac{112}{125}
      &=\frac{125566672}{318479296125}>0,\\
 16\left(t+\frac{t^3}{3(1-t^2)}\right)
      &=\frac{142294877}{158740875},\\
 \frac{2241}{2500}-\frac{142294877}{158740875}
      &=\frac{8867}{3174817500}>0.
 \end{aligned}                                    \tag{32}
\]
因此，严格地
\[
 \frac{112}{125}
  <c_*\!\left(\frac{947}{500}\right)
  <\frac{2241}{2500}.                              \tag{33}
\]
这些是有理数恒等式与解析级数余项，不是小数扫描、求积或优化结果。

取 (29) 的总容差 \(\epsilon=1/10000\)，输入 Wu 的 (W)，便得到
\[
 \begin{aligned}
 G_{947/500}(N)
 &\ge\left\{\frac{899}{1000}
             -8\log\frac{500}{447}-\frac1{10000}\right\}\Theta(N)\\
 &>\left\{\frac{899}{1000}
             -\frac{2241}{2500}-\frac1{10000}\right\}\Theta(N)
   =\frac1{400}\Theta(N)>0.                        \tag{34}
 \end{aligned}
\]
最终阈值取为 (W) 的阈值与 (29) 的阈值之较大者；再增大到 \(N\ge4\)。
所有先后关系是
\[
 a,\epsilon
 \ \longrightarrow\ K_a
 \ \longrightarrow\ \text{固定 }\eta
 \ \longrightarrow\ \text{固定筛精度 }\rho
 \ \longrightarrow\ N_0
 \ \longrightarrow\ \text{所有偶数 }N\ge N_0.
\]
均值定理的 \(A=4\)、相应 \(B\) 也先于最后的 \(N\) 极限固定。
不存在随 \(N\) 重新选截断比例或在错误顺序下交换两个极限。
由于 \(G_a(N)\) 是整数，严格正值便给出目标表示。这完成 (T)。

## 8. 输入强度与本轮完成分账

由 (33)，一个真正已知的实际系数 \(c=897/1000\) 就足以供给本桥；
但本文没有声称这个数有独立生产者，而是直接使用更强的文献 (W)。
Wu08 引言同时明确指出不使用双筛得到的系数为 0.870，Cai 的
已有系数为 0.867；二者都小于 \(112/125<c_*(947/500)\)，所以这些
较弱的现成标量**不能仅凭本文坏项上界保证** 1.894。
这没有否定它们可能与更精细、不同的坏项估计组合。
旧 0.8982 不作为输入或必要标准，也不借本文证明其已被生产。

| 对象 | 本文结论 |
| --- | --- |
| 同规范普通 Chen 计数到真实 \(D_{1,1.894}\) 的后半桥 | 在文献 (W) 与所列经典定理下完成，见 (34) |
| 坏表示主常数、固定比例小输出、异常和端点 | 在第 1–5 节逐项证明 |
| Wu 的 0.899 输入独立重建 | 本文未完成，由 M1 负责 |
| 1.894 整条路线的项目内独立重建 | 不据本文宣称完成 |
| 原 Gamma5 单项 (5.15) / 原全核整功能比较 | 均仍未证明；不是本后半桥新增的必要输入 |
| 1.8938 | 本文不研究、不宣称 |
| 新 Lean 或构建验收 | 本阶段没有；此前对象和失败日志全部保留 |

## 9. 实际读过的来源和引用定位

以下路径均相对 `research/wu2008/research/wu2008/`。

1. `sources/Wu08.tex`，引言的 \(\Omega(1)\)、\(D_{1,2}\)、(1.2)、
   主 Theorem 及双筛前后系数说明。另实读
   `sources/wu08-journal.txt` 开头两页交叉核对：刊本是
   **Acta Arithmetica 131.4 (2008), 367–383**，
   *Chen's double sieve, Goldbach's conjecture and the twin prime problem, 2*。
   (W) 以这份刊本的同一计数和规范为准，不沿用 Li–Liu 书目中的卷号。
2. `sources/Wu04.tex`，约 414–532 行：
   (2.1)–(2.6)、Lemma 2.2、Lemma 2.3 第一条完整表述；
   4757–4786 行所列 Iwaniec [17]、Pan–Ding [21]、Pan–Pan [22]。
   上筛使用 Iwaniec, *A new form of the error term in the linear sieve*,
   Acta Arith. 37 (1980), 307–320 的 Wu 转述形式。
   加权均值使用 *A new mean value theorem*,
   Sci. Sinica (1979), Special Issue II on Math., 149–161，
   具体以 Wu 给出的 Pan–Pan Corollary 8.12 表述为准；
   本文没有声称已逐页独立重证这些经典祖先。
3. `parent-fixes/liliu-source-target/arxiv-2606.05224v1-mathtext.txt`：
   Theorem 1.1 和其后 1.894 remark（字符偏移约 6327、6562）；
   §4.1 (4.4) 的 distinct-\(p\) 定义（约 29598）；
   §1 WEH 形式、Lemma 3.1（约 10739、22324）；
   §5.3 全段及 (5.42)–(5.43)（约 99651、99732）。
   后两式给出作者对 1.9 坏项使用的
   \(8\int_{9/19}^{1/2}du/[u(1-u)]=8\log(10/9)\)。
   本文复用这一换位上筛机制，但以实际素数对索引直接证明
   (15)，不引用其 \(G_8/G_{10}\) quotient-sifted 识别段作为承重步骤；
   固定比例小输出由第 5 节另行支付。
4. 素数定理只用于第 4 节的素数加权和，Mertens 乘积与倒素数和
   分别用于 (10)、(17)、(25)。所需形式已在正文写出；
   不引用数值积分证书，也不以现有 Lean 证明体替代这些推导。

本次只读原文绑定：

| 文件 | SHA-256 |
| --- | --- |
| Wu04.tex | `ad4e1c38d6a676c83630e4b18e43ac8ecf032832e4869451fca7c88ecaab2c50` |
| Wu08.tex | `fba6f873fbc7f954470db4d23a1099e4df7a4075e96243fdd96f489f3c99bc3b` |
| wu08-journal.txt | `f60bb8738110f6c51bb49740975dba22d9cd4aeaa8850234c17cab99a2de3c29` |
| Li–Liu mathtext | `ef19f37c59c081a18fe1616c893d9c3201b8f806415b9cdf5b2e0188acae14dc` |
