import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel31
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(103/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((103/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (103/40) (1/40)

def c3 : Certificate := ⟨(90247619047619/20000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((103/40)+(1/40)*x)) := (SharedCertificates.h2 (103/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((103/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-89952380952381/25000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((103/40)+(1/40)*x)) := (SharedCertificates.h4 (103/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(10609/1600),(103/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((103/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(401345767195767/50000000000000),(15586243386243/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((103/40)+(1/40)*x)) := (SharedCertificates.h8 (103/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((103/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((103/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1092727/64000),(31827/64000),(309/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((103/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(16634365587384259/100000000000000),(121124021267361/25000000000000),(4703845486111/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((103/40)+(1/40)*x)) := (SharedCertificates.h13 (103/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((103/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((103/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(112550881/2560000),(1092727/640000),(31827/1280000),(103/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((103/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(12282338204365079/100000000000000),(476984007936507/100000000000000),(6946369047619/100000000000000),(2248015873/5000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((103/40)+(1/40)*x)) := (SharedCertificates.h18 (103/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((103/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(11321035881835937/100000000000000),(137391212158203/25000000000000),(1092727/10240000),(10609/10240000),(503906251/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((103/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(73754452282034863/100000000000000),(447539152196813/12500000000000),(34760322500723/50000000000000),(33747885923/5000000000000),(3282855913/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((103/40)+(1/40)*x)) := (SharedCertificates.h22 (103/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((103/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(29151667395727537/100000000000000),(1698155382275389/100000000000000),(2060868182373/5000000000000),(133389526367/25000000000000),(1950122073/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((103/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(327300731289597/500000000000),(1906606201686971/50000000000000),(11569212388877/12500000000000),(1198106137357/100000000000000),(175160171/2000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((103/40)+(1/40)*x)) := (SharedCertificates.h26 (103/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((103/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(75065543543998407/100000000000000),(1020308358850463/20000000000000),(74294297974547/50000000000000),(1202173106383/50000000000000),(11739793709/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((103/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(17813172634647241/100000000000000),(605301982730731/50000000000000),(17630154836817/50000000000000),(570555172711/100000000000000),(1114348673/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((103/40)+(1/40)*x)) := (SharedCertificates.h30 (103/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((103/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((103/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((103/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((103/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((103/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (103/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((103/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((103/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (103/40) (1/40))

def c43 : Certificate := ⟨(20449/1600),(143/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((103/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((103/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(37258778517/100000000000000),(-260550899/50000000000000),(2733051/50000000000000),(-25483/50000000000000),(457/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((103/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1038738999913321/100000000000000),(122875819433/100000000000000),(-872003903/100000000000000),(6187759/100000000000000),(12681383/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((103/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((103/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (103/40) (1/40))

def c52 : Certificate := ⟨(76249999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((103/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (103/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((103/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (103/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((103/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (103/40) (1/40))

def c56 : Certificate := ⟨(5524861878453/25000000000000),(-1271837449/3125000000000),(37475873/50000000000000),(-138033/100000000000000),(257/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((103/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(46408839779/400000000000),(162795193471/100000000000000),(-299806987/100000000000000),(55213/10000000000000),(323/25000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((103/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((103/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((103/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((103/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((103/40)+(1/40)*x)) := (SharedCertificates.h61 (103/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-2664181496291/1562500000000),(-78305837191/3125000000000),(3024572149/100000000000000),(-660419/25000000000000),(18057/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((103/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((103/40)+(1/40)*x)) := (SharedCertificates.h61 (103/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-45553397694767/25000000000000),(-569487511143/20000000000000),(980108321/100000000000000),(691729/20000000000000),(51803/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((103/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((103/40)+(1/40)*x)) := (SharedCertificates.h67 (103/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-208323874870639/25000000000000),(-12022664193869/100000000000000),(17011000913/100000000000000),(-29121491/100000000000000),(111963/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((103/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((103/40)+(1/40)*x)) := (SharedCertificates.h67 (103/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-45441769472131/5000000000000),(-14147123304263/100000000000000),(367881239/6250000000000),(1069323/6250000000000),(279507/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((103/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((103/40)+(1/40)*x)) := (SharedCertificates.h72 (103/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(111278705426343/10000000000000),(558903041479/4000000000000),(-12775725183/25000000000000),(10693709/10000000000000),(14057/6250000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((103/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((103/40)+(1/40)*x)) := (SharedCertificates.h72 (103/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(168417491809049/6250000000000),(20526186758863/50000000000000),(-17998330613/50000000000000),(-97118157/100000000000000),(1163459/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((103/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((103/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((103/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(1556881658069/1250000000000),(181683033597/50000000000000),(-25259981/6250000000000),(51247/20000000000000),(5591/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((103/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(231209828557433/2000000000000),(12436755725177/100000000000000),(-30208475453/50000000000000),(135048337/100000000000000),(1071361/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((103/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(432507565201/50000000000000),(-93058171/10000000000000),(5521823/100000000000000),(-20909/100000000000000),(29/20000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((103/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(23309388582269/100000000000000),(165016522157/50000000000000),(-544606993/100000000000000),(11983/1000000000000),(23713/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((103/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((103/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((103/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (103/40) (1/40))

def c87 : Certificate := ⟨(17937219730941/100000000000000),(-80435962919/100000000000000),(72139877/20000000000000),(-1617487/100000000000000),(7289/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((103/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(9417040358743/100000000000000),(53623975279/50000000000000),(-240466257/50000000000000),(2156647/100000000000000),(1737/10000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((103/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((103/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((103/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((103/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((103/40)+(1/40)*x)) := (SharedCertificates.h61 (103/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-68579701984747/50000000000000),(-405666575317/25000000000000),(6586403129/100000000000000),(-26440683/100000000000000),(304793/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((103/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((103/40)+(1/40)*x)) := (SharedCertificates.h61 (103/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-144754921450021/100000000000000),(-360275819609/20000000000000),(3136333627/50000000000000),(-519333/2500000000000),(195809/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((103/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((103/40)+(1/40)*x)) := (SharedCertificates.h67 (103/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-336412227243113/50000000000000),(-1958059955581/25000000000000),(6604041381/20000000000000),(-2813053/2000000000000),(85637/6250000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((103/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((103/40)+(1/40)*x)) := (SharedCertificates.h67 (103/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-722552975534471/100000000000000),(-2241628040603/25000000000000),(15805358531/50000000000000),(-105639773/100000000000000),(486151/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((103/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((103/40)+(1/40)*x)) := (SharedCertificates.h72 (103/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(184149226469727/20000000000000),(9641731481527/100000000000000),(-6707816041/12500000000000),(69485399/25000000000000),(1172509/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((103/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((103/40)+(1/40)*x)) := (SharedCertificates.h72 (103/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1075496272552851/50000000000000),(5262592764109/20000000000000),(-4963894403/5000000000000),(67422747/20000000000000),(371929/6250000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((103/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((103/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((103/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(119720887208667/100000000000000),(234695066691/100000000000000),(-937423017/100000000000000),(1843949/50000000000000),(45011/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((103/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1423363238618759/12500000000000),(1768106332011/20000000000000),(-55132821409/100000000000000),(303737919/100000000000000),(7898143/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((103/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(54887605553/6250000000000),(-681815579/100000000000000),(4781399/100000000000000),(-30439/100000000000000),(339/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((103/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(73789268977/390625000000),(108207545191/50000000000000),(-948418441/100000000000000),(4240817/100000000000000),(82169/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((103/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((103/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-219171027993411/50000000000000),(-5624316979921/100000000000000),(3953027327/25000000000000),(-60486647/100000000000000),(2998887/25000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((103/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(3883495145631/10000000000000),(-188519181827/50000000000000),(3660566637/100000000000000),(-17769741/50000000000000),(87107/25000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((103/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-85114962327537/50000000000000),(-265741526901/50000000000000),(353145457/3125000000000),(-66602527/50000000000000),(9064677/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((103/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((103/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((103/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((103/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((103/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((103/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((103/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((103/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((103/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((103/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (103/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((103/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((103/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(2406906711/100000000000000),(-46736053/50000000000000),(113437/5000000000000),(-22027/50000000000000),(169/20000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((103/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(28031826148849/25000000000000),(-194211286227/50000000000000),(815788839/25000000000000),(-26301161/100000000000000),(19336451/25000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((103/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((103/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (103/40) (1/40))

def c134 : Certificate := ⟨(40809/1600),(203/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((103/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((103/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1165501165501/25000000000000),(-32601431203/100000000000000),(56995509/25000000000000),(-39857/2500000000000),(11229/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((103/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(4756293706293/4000000000000),(10983243883/3125000000000),(227982031/50000000000000),(-3188561/100000000000000),(276159/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((103/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((103/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (103/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((103/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (103/40) (1/40))

def c140 : Certificate := ⟨(5967906850573/25000000000000),(-10014163189/50000000000000),(-917953/10000000000000),(211203/100000000000000),(31849/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((103/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(4513490390831/100000000000000),(80113305509/100000000000000),(18359059/50000000000000),(-422407/50000000000000),(27887/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((103/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((103/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(203715955081/100000000000000),(7231812691/100000000000000),(33747977/50000000000000),(-1743/10000000000000),(7077/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((103/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((103/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(2426202060857/100000000000000),(85802530779/100000000000000),(792121711/100000000000000),(-158801/50000000000000),(33857/20000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((103/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-315889574159731/50000000000000),(-11210046371609/100000000000000),(-1258788521/25000000000000),(29726307/25000000000000),(610191/3125000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((103/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1292292600583353/100000000000000),(-11721914533773/50000000000000),(-19721050347/100000000000000),(59775527/25000000000000),(20511761/50000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((103/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(335873259624237/20000000000000),(14375094664791/50000000000000),(-6009764209/100000000000000),(-327951389/100000000000000),(1693137/3125000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((103/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(4814962946865103/100000000000000),(17352400734043/20000000000000),(96768957/156250000000),(-910302369/100000000000000),(18973153/12500000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((103/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(5173810690230209/100000000000000),(99665812133079/100000000000000),(186696371281/100000000000000),(-110954497/12500000000000),(176902057/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((103/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(109230696736743/100000000000000),(167458423709/100000000000000),(14093219/10000000000000),(-853529/50000000000000),(9157/3125000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((103/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((103/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((103/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((103/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(2291040874972157/4000000000000),(85319915288591/100000000000000),(5857555001/12500000000000),(-28997717/3125000000000),(19819041/12500000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((103/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(17459313117/10000000000000),(-260078663/100000000000000),(7643/3125000000000),(2677/100000000000000),(99/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((103/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(9033118084881/100000000000000),(160553684439/100000000000000),(79403427/100000000000000),(-206631/12500000000000),(340863/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((103/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((103/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((103/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (103/40) (1/40))

def c175 : Certificate := ⟨(21895155888153/100000000000000),(-50547297779/100000000000000),(51117359/100000000000000),(491957/100000000000000),(41079/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((103/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(517474018641/12500000000000),(67396397037/100000000000000),(-212989/312500000000),(-655943/100000000000000),(14061/10000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((103/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((103/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(171378790379/100000000000000),(2790070753/50000000000000),(3977967/10000000000000),(-7309/5000000000000),(12673/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((103/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((103/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(2042356033129/100000000000000),(16567169823/25000000000000),(466774431/100000000000000),(-1785823/100000000000000),(37967/25000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((103/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-144871587895801/25000000000000),(-9431375725217/100000000000000),(1920900279/20000000000000),(23003529/25000000000000),(19690973/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((103/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-23662626644879/2000000000000),(-4912995861119/25000000000000),(844998179/6250000000000),(102087757/50000000000000),(20572401/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((103/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1544840799408171/100000000000000),(12168336850657/50000000000000),(-19059447113/50000000000000),(-213818873/100000000000000),(27243749/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((103/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(176429398188593/4000000000000),(36407435817427/50000000000000),(-14448303717/25000000000000),(-46875179/6250000000000),(38104391/25000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((103/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(4711972275332657/100000000000000),(82740338452183/100000000000000),(15787454659/100000000000000),(-24646457/2500000000000),(174963713/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((103/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(21690192617727/20000000000000),(7018646779/5000000000000),(-9653329/10000000000000),(-729033/50000000000000),(293893/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((103/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((103/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((103/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((103/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(14219552276923559/25000000000000),(14342744177329/20000000000000),(-66684814167/100000000000000),(-730652191/100000000000000),(1982223/1250000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((103/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(175814255703/100000000000000),(-221671791/100000000000000),(485617/100000000000000),(693/50000000000000),(497/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((103/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(8284318984807/100000000000000),(135024196881/100000000000000),(-16596657/12500000000000),(-1301167/100000000000000),(167623/50000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((103/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((103/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(3883515082249/20000000000000),(52831735351/20000000000000),(-321419243/50000000000000),(1985297/100000000000000),(2890363/20000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((103/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7540805984949/100000000000000),(29374185293/100000000000000),(-13370807/2500000000000),(1192707/20000000000000),(146529/2500000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((103/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((103/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((103/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((103/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((103/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((103/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (103/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((103/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((103/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((103/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (103/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((103/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(35703295793/100000000000000),(-51196157/100000000000000),(1579181/100000000000000),(-553/12500000000000),(19/25000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((103/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(26176024723237/6250000000000),(-12972629013/781250000000),(-7848780557/100000000000000),(-58780533/100000000000000),(1999689/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((103/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((103/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((103/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((103/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (103/40) (1/40))

def c223 : Certificate := ⟨(33489/1600),(183/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((103/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3964059441/2560000),(18583467/640000),(245387/1280000),(323/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((103/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((103/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(43468574937/50000000000000),(-243180839/20000000000000),(12754239/100000000000000),(-118921/100000000000000),(1063/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((103/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(13461876161393/10000000000000),(25663408117/4000000000000),(555115699/50000000000000),(-605419/20000000000000),(837393/25000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((103/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((103/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (103/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((103/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (103/40) (1/40))

def c231 : Certificate := ⟨(23008670778191/100000000000000),(-33965452057/100000000000000),(-1727131/20000000000000),(129883/50000000000000),(178453/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((103/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1593063377447/20000000000000),(135861808223/100000000000000),(6908523/20000000000000),(-1039067/100000000000000),(837361/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((103/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((103/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(31723136557/5000000000000),(21643647107/100000000000000),(95043583/50000000000000),(-7167/10000000000000),(17311/12500000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((103/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((103/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(3756239419773/50000000000000),(254551810049/100000000000000),(2191514681/100000000000000),(-683451/50000000000000),(1651681/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((103/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-278636492866811/25000000000000),(-9495085351657/50000000000000),(-4312971313/100000000000000),(74173901/50000000000000),(733171/625000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((103/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1159532923453539/50000000000000),(-20534087943349/50000000000000),(-36200856659/100000000000000),(301916629/100000000000000),(253853707/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((103/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1440963029027843/50000000000000),(22942430511591/50000000000000),(-1847265541/4000000000000),(-103816173/25000000000000),(162349679/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((103/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(1718627454915337/20000000000000),(75112605036019/50000000000000),(95926726407/100000000000000),(-60046801/5000000000000),(232776909/25000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((103/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(4866261980273517/50000000000000),(189936310056303/100000000000000),(465685443497/100000000000000),(-43858999/4000000000000),(295710361/25000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((103/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(11656509650561/10000000000000),(293367263553/100000000000000),(64793099/25000000000000),(-537451/25000000000000),(181321/10000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((103/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((103/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((103/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((103/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(30481856802784463/50000000000000),(72742193238453/50000000000000),(22875138929/50000000000000),(-64568269/5000000000000),(499736619/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((103/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(164032002129/100000000000000),(-97861883/25000000000000),(50691/6250000000000),(229/12500000000000),(2719/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((103/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(15964453910169/100000000000000),(27345860731/10000000000000),(49654189/50000000000000),(-380539/20000000000000),(1113117/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((103/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((103/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((103/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (103/40) (1/40))

def c259 : Certificate := ⟨(19846929175727/100000000000000),(-37908119237/50000000000000),(158425489/100000000000000),(50739/20000000000000),(20113/5000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((103/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(687076109903/10000000000000),(25272079491/25000000000000),(-105616993/50000000000000),(-338261/100000000000000),(40743/5000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((103/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((103/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(472073580799/100000000000000),(3472768413/25000000000000),(14632343/20000000000000),(-118387/25000000000000),(56933/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((103/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((103/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(5600012873691/100000000000000),(163829616369/100000000000000),(8417969/1000000000000),(-5703541/100000000000000),(680131/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((103/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-480760895179067/50000000000000),(-14135447214591/100000000000000),(29784379367/100000000000000),(9490123/20000000000000),(114139057/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((103/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-124367310803689/6250000000000),(-6049585608609/20000000000000),(48933704609/100000000000000),(40298287/25000000000000),(1220511/500000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((103/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(627130832539199/25000000000000),(34829206381479/100000000000000),(-104336791901/100000000000000),(935851/100000000000000),(39366829/12500000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((103/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(1477330759822001/20000000000000),(111071589465549/100000000000000),(-199055011939/100000000000000),(-108527707/20000000000000),(89838993/10000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((103/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(8229337825480043/100000000000000),(68169874571517/50000000000000),(-55794317403/100000000000000),(-675698901/50000000000000),(552041/50000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((103/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(114213595778859/100000000000000),(10803385479/5000000000000),(-349306257/100000000000000),(-115007/10000000000000),(871793/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((103/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((103/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((103/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((103/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(1494807463433123/2500000000000),(108116617145101/100000000000000),(-43728480341/20000000000000),(-23310857/5000000000000),(477181743/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((103/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(167245619329/100000000000000),(-302414041/100000000000000),(144799/12500000000000),(-1897/100000000000000),(2687/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((103/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(13763207012899/100000000000000),(10156779239/5000000000000),(-205148053/50000000000000),(-334093/50000000000000),(2075539/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((103/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((103/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(124504317965797/100000000000000),(751213921797/50000000000000),(-1443694551/12500000000000),(-60484241/100000000000000),(9452867/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((103/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(48351191443027/100000000000000),(114038080589/100000000000000),(-699053807/12500000000000),(6161283/20000000000000),(1716739/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((103/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((103/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((103/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((103/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((103/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((103/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (103/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((103/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(542384569845125629/50000000000000),(1555486936420587/100000000000000),(-45749615777077/100000000000000),0,(35063/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((103/40)+(1/40)*x)) := (SharedCertificates.h297 (103/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4609275667/50000000000000),(-13218791/100000000000000),(203871/50000000000000),(-1143/100000000000000),(11/50000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((103/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(328224359649101/50000000000000),(1383499503741/100000000000000),(985711773/10000000000000),(22077369/50000000000000),(2563219/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((103/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((103/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (103/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((103/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (103/40) (1/40))

def c307 : Certificate := ⟨(106171714907111/3125000000000),(11091229182759/50000000000000),0,0,(541/50000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((103/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (103/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((103/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (103/40) (1/40))

def c311 : Certificate := ⟨(2177505122972189/100000000000000),(2817541634481/100000000000000),0,0,(541/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((103/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (103/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(459241169837/10000000000000),(-1485566099/25000000000000),(96111/1250000000000),(-9949/100000000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((103/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(78013476092067/50000000000000),(81682168453/10000000000000),(-528455511/50000000000000),(273513/20000000000000),(23/800000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((103/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((103/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (103/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((103/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (103/40) (1/40))

def c316 : Certificate := ⟨(21928528461103/100000000000000),(-39277716967/100000000000000),(3029393/2500000000000),(-4673/1250000000000),(1213/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((103/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(6142943077793/50000000000000),(19638858483/12500000000000),(-484702881/100000000000000),(299071/20000000000000),(31/500000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((103/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((103/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(37735749657/2500000000000),(38604924727/100000000000000),(127738159/100000000000000),(-1155607/100000000000000),(269/3125000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((103/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((103/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(8871133067967/50000000000000),(56128778177/12500000000000),(278959563/20000000000000),(-13655617/100000000000000),(105133/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((103/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1717844267163159/100000000000000),(-21912479130357/100000000000000),(3432462231/5000000000000),(-52686797/25000000000000),(901601/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((103/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3651100514558007/100000000000000),(-9876421055687/20000000000000),(59025264621/50000000000000),(-256213589/100000000000000),(589927/20000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((103/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(2140748058627999/50000000000000),(4868437918689/10000000000000),(-231994720347/100000000000000),(914463349/100000000000000),(4246923/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((103/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(6713100101043603/50000000000000),(177674414367039/100000000000000),(-96340943331/20000000000000),(229206547/20000000000000),(10604079/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((103/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(16199235807064283/100000000000000),(250812203127991/100000000000000),(-199164140847/100000000000000),(-245686229/25000000000000),(2444601/10000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((103/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(31520300574363/25000000000000),(70565332091/20000000000000),(-841667603/100000000000000),(1835103/100000000000000),(1313/6250000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((103/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((103/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((103/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((103/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(16398288087920543/25000000000000),(84112120486381/50000000000000),(-16609725843/3125000000000),(21469413/1562500000000),(1970481/12500000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((103/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(152454938381/100000000000000),(-390995331/100000000000000),(279767/12500000000000),(-6051/50000000000000),(3/3125000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((103/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(6174133741963/25000000000000),(319037334067/100000000000000),(-230434661/25000000000000),(1466783/50000000000000),(8413/10000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((103/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((103/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((103/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (103/40) (1/40))

def c344 : Certificate := ⟨(4400781985811/25000000000000),(-75932588401/100000000000000),(212896607/50000000000000),(-1193821/50000000000000),(1357/10000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((103/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(9862496075673/100000000000000),(63277157/62500000000),(-567724287/100000000000000),(1591761/50000000000000),(2081/6250000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((103/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((103/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(486344144213/50000000000000),(9985131401/50000000000000),(-9481207/100000000000000),(-260809/50000000000000),(16343/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((103/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((103/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((103/40)+(1/40)*x)) := (SharedCertificates.h144 (103/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(5740198386281/50000000000000),(58433613617/25000000000000),(-35324277/25000000000000),(-5972509/100000000000000),(96959/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((103/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((103/40)+(1/40)*x)) := (SharedCertificates.h148 (103/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-275923439382611/20000000000000),(-14139407966697/100000000000000),(15927785717/20000000000000),(-447386659/100000000000000),(4679247/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((103/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((103/40)+(1/40)*x)) := (SharedCertificates.h151 (103/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-28975635930933/1000000000000),(-31139436955343/100000000000000),(10020898991/6250000000000),(-51158001/6250000000000),(1451691/12500000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((103/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((103/40)+(1/40)*x)) := (SharedCertificates.h154 (103/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(877822223368787/25000000000000),(3297400958193/10000000000000),(-54459336647/25000000000000),(173974789/12500000000000),(1576189/10000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((103/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((103/40)+(1/40)*x)) := (SharedCertificates.h157 (103/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(5350960804390589/50000000000000),(56556317109183/50000000000000),(-151036278911/25000000000000),(3183999299/100000000000000),(41421973/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((103/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((103/40)+(1/40)*x)) := (SharedCertificates.h160 (103/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6233287038415969/50000000000000),(3005741430893/2000000000000),(-7596932813/1250000000000),(1072243623/50000000000000),(2840067/4000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((103/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((103/40)+(1/40)*x)) := (SharedCertificates.h41 (103/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(30174420109943/25000000000000),(111228582601/50000000000000),(-1144929781/100000000000000),(2922713/50000000000000),(16587/20000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((103/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((103/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((103/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((103/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((103/40)+(1/40)*x)) := (SharedCertificates.h167 (103/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(62996468387237857/100000000000000),(13564470277217/12500000000000),(-30398466851/5000000000000),(3327923601/100000000000000),(1982207/4000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((103/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(7936952861/5000000000000),(-1068121/390625000000),(250373/12500000000000),(-579/4000000000000),(93/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((103/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(3957864431439/20000000000000),(40895161599/20000000000000),(-281495977/25000000000000),(3135833/50000000000000),(176297/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((103/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((103/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(146013419683099/50000000000000),(4052056928983/100000000000000),(-362884687/20000000000000),(25835829/25000000000000),(1511807/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((103/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(113408481307259/100000000000000),(18902444991/4000000000000),(-5292602547/100000000000000),(91517817/100000000000000),(257373/6250000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((103/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((103/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(15717554670898437/100000000000000),(180075860595703/25000000000000),(1347343/10240000),(12257/10240000),(542968751/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((103/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(49729/1600),(223/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((103/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(11089567/64000),(149187/64000),(669/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((103/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(2723451181235799489/100000000000000),(6457942570826349/4000000000000),(4123243062256041/100000000000000),(14796645353729/25000000000000),(524625870829/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((103/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(917952933/25000000000000),(-108834103/50000000000000),(7344521/100000000000000),(-92821/50000000000000),(5851/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((103/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5563281022217/100000000000000),(-14877704887/100000000000000),(-107699437/50000000000000),(2603647/50000000000000),(16915739/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((103/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((103/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((103/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel31

namespace Hf4Quad.Panel32
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(21/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((21/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (21/8) (1/40)

def c3 : Certificate := ⟨(23/5),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((21/8)+(1/40)*x)) := (SharedCertificates.h2 (21/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((21/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-368571428571429/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((21/8)+(1/40)*x)) := (SharedCertificates.h4 (21/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(441/64),(21/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((21/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(417083333333333/50000000000000),(1986111111111/12500000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((21/8)+(1/40)*x)) := (SharedCertificates.h8 (21/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((21/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((21/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(9261/512),(1323/2560),(63/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((21/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1804523/10240),(257789/51200),(2397591145833/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((21/8)+(1/40)*x)) := (SharedCertificates.h13 (21/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((21/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((21/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(194481/4096),(9261/5120),(1323/51200),(21/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((21/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(33957/256),(1617/320),(231/3200),(45833333333/100000000000000),(21825397/20000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((21/8)+(1/40)*x)) := (SharedCertificates.h18 (21/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((21/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(6231843566894531/50000000000000),(148377227783203/25000000000000),(9261/81920),(441/409600),(128417969/25000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((21/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(81198613586425777/100000000000000),(966650161743163/25000000000000),(18412384033203/25000000000000),(140284830729/20000000000000),(104577411/3125000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((21/8)+(1/40)*x)) := (SharedCertificates.h22 (21/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((21/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(32717178726196287/100000000000000),(934776535034179/50000000000000),(556414604187/1250000000000),(565246582031/100000000000000),(126652527/3125000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((21/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(14693302276611327/20000000000000),(419808636474609/10000000000000),(99954437255857/100000000000000),(1269262695311/100000000000000),(1820150941/20000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((21/8)+(1/40)*x)) := (SharedCertificates.h26 (21/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((21/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(85882594156265253/100000000000000),(2862753138542173/50000000000000),(81792946815489/50000000000000),(519320297241/20000000000000),(24871298843/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((21/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(2038007591485977/10000000000000),(1358671727657317/100000000000000),(38819192218779/100000000000000),(308088827133/50000000000000),(1180399739/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((21/8)+(1/40)*x)) := (SharedCertificates.h30 (21/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((21/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((21/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((21/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((21/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((21/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (21/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((21/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((21/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (21/8) (1/40))

def c43 : Certificate := ⟨(841/64),(29/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((21/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((21/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(4529754827/12500000000000),(-62479377/12500000000000),(5170707/100000000000000),(-47547/100000000000000),(21/5000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((21/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1038496687612201/100000000000000),(119460586071/100000000000000),(-417964569/50000000000000),(5855963/100000000000000),(23970703/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((21/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((21/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (21/8) (1/40))

def c52 : Certificate := ⟨(30833333333333/20000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((21/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (21/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((21/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (21/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((21/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (21/8) (1/40))

def c56 : Certificate := ⟨(22018348623853/100000000000000),(-40400639677/100000000000000),(37064807/50000000000000),(-68009/50000000000000),(63/25000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((21/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(5963302752293/50000000000000),(80801279353/50000000000000),(-296518457/100000000000000),(54407/10000000000000),(1277/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((21/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((21/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((21/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((21/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((21/8)+(1/40)*x)) := (SharedCertificates.h61 (21/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-87753556097963/50000000000000),(-2493720217831/100000000000000),(1504355109/50000000000000),(-2645473/100000000000000),(1779/5000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((21/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((21/8)+(1/40)*x)) := (SharedCertificates.h61 (21/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-11744032373019/6250000000000),(-2843475978673/100000000000000),(500295349/50000000000000),(842279/25000000000000),(12811/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((21/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((21/8)+(1/40)*x)) := (SharedCertificates.h67 (21/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-428636507952197/50000000000000),(-478198711239/4000000000000),(8418835067/50000000000000),(-28657/100000000000),(5551/5000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((21/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((21/8)+(1/40)*x)) := (SharedCertificates.h67 (21/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-234276489006301/25000000000000),(-2824675216731/20000000000000),(47895147/800000000000),(16491919/100000000000000),(27537/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((21/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((21/8)+(1/40)*x)) := (SharedCertificates.h72 (21/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(142566080930803/12500000000000),(688472105599/5000000000000),(-12616362459/25000000000000),(105549153/100000000000000),(223547/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((21/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((21/8)+(1/40)*x)) := (SharedCertificates.h72 (21/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(277663986085851/10000000000000),(40907238364113/100000000000000),(-9141680139/25000000000000),(-92922681/100000000000000),(142891/12500000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((21/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((21/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((21/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(3914864068681/3125000000000),(2826191537/781250000000),(-201306109/50000000000000),(51911/20000000000000),(2753/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((21/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2896281087141651/25000000000000),(12196701825711/100000000000000),(-29805832629/50000000000000),(133382161/100000000000000),(527471/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((21/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(215793972061/25000000000000),(-227185713/25000000000000),(5398217/100000000000000),(-10149/50000000000000),(71/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((21/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(11983642891151/50000000000000),(81967225461/25000000000000),(-21499507/4000000000000),(117487/10000000000000),(5829/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((21/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((21/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((21/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (21/8) (1/40))

def c87 : Certificate := ⟨(17777777777777/100000000000000),(-79012345679/100000000000000),(17558299/5000000000000),(-780369/50000000000000),(6971/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((21/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(2407407407407/25000000000000),(52674897119/50000000000000),(-468221309/100000000000000),(2080983/100000000000000),(3369/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((21/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((21/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((21/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((21/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((21/8)+(1/40)*x)) := (SharedCertificates.h61 (21/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-140378600823021/100000000000000),(-1596634659341/100000000000000),(401889957/6250000000000),(-6404803/25000000000000),(29509/10000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((21/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((21/8)+(1/40)*x)) := (SharedCertificates.h61 (21/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-148332754153303/100000000000000),(-1776535690687/100000000000000),(24598151/400000000000),(-810881/4000000000000),(75811/20000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((21/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((21/8)+(1/40)*x)) := (SharedCertificates.h67 (21/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-13767159378367/2000000000000),(-9627284569/125000000000),(32190618207/100000000000000),(-135911067/100000000000000),(265737/20000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((21/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((21/8)+(1/40)*x)) := (SharedCertificates.h67 (21/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-740360397006827/100000000000000),(-1768265355689/20000000000000),(7746127011/25000000000000),(-103106807/100000000000000),(301/16000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((21/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((21/8)+(1/40)*x)) := (SharedCertificates.h72 (21/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(939817146954739/100000000000000),(4715186608507/50000000000000),(-10405467701/20000000000000),(33400841/12500000000000),(2267471/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((21/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((21/8)+(1/40)*x)) := (SharedCertificates.h72 (21/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(550806010779209/25000000000000),(1295993383901/5000000000000),(-48638822817/50000000000000),(164825957/50000000000000),(2873073/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((21/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((21/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((21/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(60093278463647/50000000000000),(230989178477/100000000000000),(-915632783/100000000000000),(3576207/100000000000000),(43569/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((21/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(456174753848493/4000000000000),(2155898999113/25000000000000),(-10669434119/20000000000000),(291577387/100000000000000),(7623159/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((21/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(876856942707/100000000000000),(-663049409/100000000000000),(2301561/50000000000000),(-14501/50000000000000),(651/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((21/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(19319122985459/100000000000000),(106335847639/50000000000000),(-923430229/100000000000000),(2044859/50000000000000),(19791/25000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((21/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((21/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-112381980309869/25000000000000),(-5561785998709/100000000000000),(15455473303/100000000000000),(-29200747/50000000000000),(5810321/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((21/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(19047619047619/50000000000000),(-45351473923/12500000000000),(1727675197/50000000000000),(-32908099/100000000000000),(158213/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((21/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-171248731900753/100000000000000),(-30489707171/6250000000000),(1053384997/10000000000000),(-122570569/100000000000000),(8492881/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((21/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((21/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((21/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((21/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((21/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((21/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((21/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((21/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((21/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((21/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (21/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((21/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((21/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(2228696651/100000000000000),(-8490273/10000000000000),(2021493/100000000000000),(-7701/20000000000000),(723/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((21/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(13920413164607/12500000000000),(-375678680941/100000000000000),(1555145869/50000000000000),(-3090749/12500000000000),(71022671/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((21/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((21/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (21/8) (1/40))

def c134 : Certificate := ⟨(1665/64),(41/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((21/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((21/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(183908045977/4000000000000),(-3170828379/10000000000000),(218677819/100000000000000),(-1508123/100000000000000),(419/4000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((21/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(119612068965509/100000000000000),(70650019813/20000000000000),(27334727/6250000000000),(-3016249/100000000000000),(525933/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((21/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((21/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (21/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((21/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (21/8) (1/40))

def c140 : Certificate := ⟨(11915767847971/50000000000000),(-5015640021/25000000000000),(-7949617/100000000000000),(49727/25000000000000),(30227/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((21/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1168464304057/25000000000000),(40125120167/50000000000000),(6359693/20000000000000),(-198909/25000000000000),(26551/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((21/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((21/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(27306176597/12500000000000),(7501563297/100000000000000),(105271/156250000000),(-11669/50000000000000),(6947/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((21/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((21/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(1300486463013/50000000000000),(88966922491/100000000000000),(79000443/10000000000000),(-48413/12500000000000),(166169/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((21/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-5233747556089/800000000000),(-11228788172809/100000000000000),(-4342638183/100000000000000),(56006257/50000000000000),(9295521/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((21/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-669628628261259/50000000000000),(-1175994834693/5000000000000),(-18325699827/100000000000000),(113081511/50000000000000),(9779147/25000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((21/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(347368011263989/20000000000000),(3590287371583/12500000000000),(-1978686223/25000000000000),(-61455819/20000000000000),(51586673/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((21/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(19487216802133/390625000000),(43499504956657/50000000000000),(56620466807/100000000000000),(-860816863/100000000000000),(144666809/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((21/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(2686941038839313/50000000000000),(100402102975337/100000000000000),(181487614421/100000000000000),(-424531953/50000000000000),(42339063/25000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((21/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(6847885240327/6250000000000),(33600408793/20000000000000),(13097037/10000000000000),(-161461/10000000000000),(69851/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((21/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((21/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((21/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((21/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(57446841826667653/100000000000000),(42748214039511/50000000000000),(4144662039/10000000000000),(-877253767/100000000000000),(30265441/20000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((21/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(271990583/156250000000),(-259069123/100000000000000),(129987/50000000000000),(1229/50000000000000),(47/10000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((21/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4677265021699/50000000000000),(6434074423/4000000000000),(69782549/100000000000000),(-1555069/100000000000000),(326119/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((21/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((21/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((21/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (21/8) (1/40))

def c175 : Certificate := ⟨(10897134805073/50000000000000),(-50337099273/100000000000000),(53939109/100000000000000),(449167/100000000000000),(77483/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((21/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(427430718647/10000000000000),(67116132363/100000000000000),(-71918813/100000000000000),(-598891/100000000000000),(133703/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((21/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((21/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(182697019243/100000000000000),(5737499337/100000000000000),(3889769/10000000000000),(-18467/12500000000000),(2473/20000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((21/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((21/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(217674616727/10000000000000),(17028569251/25000000000000),(228004139/50000000000000),(-72079/4000000000000),(18521/12500000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((21/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-299154982643971/50000000000000),(-1878377233909/20000000000000),(1266534399/12500000000000),(84011749/100000000000000),(3744797/20000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((21/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1222379618055269/100000000000000),(-9797758817687/50000000000000),(7348589439/50000000000000),(188418549/100000000000000),(1958387/5000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((21/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(1593360006930469/100000000000000),(24181724418807/100000000000000),(-19666586537/50000000000000),(-38248337/20000000000000),(10360291/20000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((21/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(4556127647076067/100000000000000),(14514988355413/20000000000000),(-62112061729/100000000000000),(-690342411/100000000000000),(145045129/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((21/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(4877508328680937/100000000000000),(41395942104767/50000000000000),(10041087839/100000000000000),(-465093619/50000000000000),(83534181/50000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((21/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(108731311392183/100000000000000),(139969764063/100000000000000),(-3279373/3125000000000),(-672759/50000000000000),(279771/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((21/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((21/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((21/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((21/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(14255341022113353/25000000000000),(8929807474139/12500000000000),(-69223989/97656250000),(-670276079/100000000000000),(30213361/20000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((21/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(87686432619/50000000000000),(-219713569/100000000000000),(493277/100000000000000),(117/10000000000000),(59/12500000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((21/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(8553826108229/100000000000000),(26895590379/20000000000000),(-70118017/50000000000000),(-593949/50000000000000),(319843/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((21/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((21/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(9971668669183/50000000000000),(32701395573/12500000000000),(-1232321/195312500000),(98381/5000000000000),(3428897/25000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((21/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7597461843187/100000000000000),(6826154143/25000000000000),(-100081049/20000000000000),(5515333/100000000000000),(681809/12500000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((21/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((21/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((21/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((21/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((21/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((21/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (21/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((21/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((21/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((21/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (21/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((21/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(1424287439/4000000000000),(-11232551/25000000000000),(1554367/100000000000000),(-963/25000000000000),(37/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((21/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(207731766615869/50000000000000),(-211575625751/12500000000000),(-8207536143/100000000000000),(-60845961/100000000000000),(978441/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((21/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((21/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((21/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((21/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (21/8) (1/40))

def c223 : Certificate := ⟨(1369/64),(37/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((21/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(6583521/4096),(30525/1024),(9971/51200),(13/25600),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((21/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((21/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(84555423437/100000000000000),(-1166281703/100000000000000),(12064983/100000000000000),(-110943/100000000000000),(489/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((21/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(135906349087251/100000000000000),(322995253667/50000000000000),(546294333/50000000000000),(-2857777/100000000000000),(3200123/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((21/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((21/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (21/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((21/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (21/8) (1/40))

def c231 : Certificate := ⟨(22940707381159/100000000000000),(-33996933587/100000000000000),(-7118641/100000000000000),(246159/100000000000000),(169489/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((21/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(8237170475363/100000000000000),(16998466793/12500000000000),(88983/312500000000),(-3077/312500000000),(799663/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((21/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((21/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(678509774401/100000000000000),(11201541503/50000000000000),(37923527/20000000000000),(-8477/10000000000000),(34147/25000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((21/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((21/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(8030337279193/100000000000000),(52660171131/20000000000000),(545714017/25000000000000),(-303677/20000000000000),(407177/25000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((21/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-1152542393979387/100000000000000),(-19005673994091/100000000000000),(-1723144677/50000000000000),(8793053/6250000000000),(112031163/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((21/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-300168076861819/12500000000000),(-10302352918033/25000000000000),(-34430320367/100000000000000),(14426903/5000000000000),(243032239/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((21/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(2973507783384941/100000000000000),(1827810163821/4000000000000),(-48596896167/100000000000000),(-9755741/2500000000000),(62027143/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((21/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(1778792380869351/20000000000000),(75297361452683/50000000000000),(44440956411/50000000000000),(-287092131/25000000000000),(111344131/12500000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((21/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(10114250607280917/100000000000000),(19178600374071/10000000000000),(5739834173/1250000000000),(-1070705791/100000000000000),(1139509123/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((21/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(117152850725127/100000000000000),(147189275847/50000000000000),(49313351/20000000000000),(-41081/2000000000000),(867957/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((21/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((21/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((21/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((21/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(3828428447787279/6250000000000),(72826059891559/50000000000000),(38171471929/100000000000000),(-1235934463/100000000000000),(95837783/10000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((21/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(32650473087/20000000000000),(-194091171/50000000000000),(821289/100000000000000),(791/50000000000000),(1291/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((21/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(16511753362409/100000000000000),(68458363199/25000000000000),(88221031/100000000000000),(-179531/10000000000000),(2141789/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((21/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((21/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((21/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (21/8) (1/40))

def c259 : Certificate := ⟨(3939186466977/20000000000000),(-75179680909/100000000000000),(159807719/100000000000000),(103973/50000000000000),(378397/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((21/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(884011277519/12500000000000),(6264973409/6250000000000),(-213076961/100000000000000),(-138631/50000000000000),(97033/12500000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((21/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((21/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(500144600819/100000000000000),(1772258287/12500000000000),(70341733/100000000000000),(-58299/12500000000000),(111461/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((21/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((21/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(237239754201/4000000000000),(20891092329/12500000000000),(807858853/100000000000000),(-1402141/25000000000000),(665647/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((21/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-989673185584901/100000000000000),(-7007887868987/50000000000000),(15021399301/50000000000000),(19428637/50000000000000),(108735529/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((21/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2050175842211777/100000000000000),(-30050333368171/100000000000000),(623070181/1250000000000),(143104531/100000000000000),(232958499/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((21/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(1288882224762771/50000000000000),(34411961970549/100000000000000),(-13032922137/12500000000000),(23054339/100000000000000),(300010573/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((21/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(152159931173861/2000000000000),(6891821149077/6250000000000),(-8084105081/4000000000000),(-474478967/100000000000000),(53563993/6250000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((21/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(8501783492313263/100000000000000),(136100665937887/100000000000000),(-63671714671/100000000000000),(-637757157/50000000000000),(132319249/12500000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((21/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(114644325041123/100000000000000),(26832151923/12500000000000),(-355812189/100000000000000),(-255229/25000000000000),(1663989/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((21/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((21/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((21/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((21/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(15001913403752607/25000000000000),(107236735438787/100000000000000),(-110615051433/50000000000000),(-79523323/20000000000000),(227953707/25000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((21/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(20830676167/12500000000000),(-930637/312500000000),(1146561/100000000000000),(-2043/100000000000000),(51/2000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((21/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(113342655213/800000000000),(25185859269/12500000000000),(-206970433/50000000000000),(-8581/1562500000000),(1987769/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((21/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((21/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(127462488918799/100000000000000),(291099685701/20000000000000),(-11916580833/100000000000000),(-7738343/12500000000000),(4514977/25000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((21/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(12139284658933/25000000000000),(46013326211/50000000000000),(-5416094151/100000000000000),(27998327/100000000000000),(1002753/12500000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((21/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((21/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((21/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((21/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((21/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((21/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (21/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((21/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(4248816855859313/390625000000),(686244236656141/50000000000000),(-45749615777077/100000000000000),0,(140607/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((21/8)+(1/40)*x)) := (SharedCertificates.h297 (21/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(1838747177/20000000000000),(-11600929/100000000000000),(50167/12500000000000),(-199/20000000000000),(21/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((21/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(659255506409941/100000000000000),(1423470155957/100000000000000),(5065513323/50000000000000),(23521669/50000000000000),(2446629/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((21/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((21/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (21/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((21/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (21/8) (1/40))

def c307 : Certificate := ⟨(3441859793758589/100000000000000),(11091229182759/50000000000000),0,0,(217/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((21/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (21/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((21/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (21/8) (1/40))

def c311 : Certificate := ⟨(17055782861259/781250000000),(2817541634481/100000000000000),0,0,(271/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((21/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (21/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4580557845717/100000000000000),(-5911627849/100000000000000),(1525899/20000000000000),(-9847/100000000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((21/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(39414094705397/25000000000000),(812610394943/100000000000000),(-524373933/50000000000000),(1353489/100000000000000),(143/5000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((21/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((21/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (21/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((21/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (21/8) (1/40))

def c316 : Certificate := ⟨(21850454757669/100000000000000),(-38797463539/100000000000000),(118960081/100000000000000),(-364753/100000000000000),(589/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((21/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(12598180969321/100000000000000),(155189854151/100000000000000),(-19033613/4000000000000),(1459009/100000000000000),(303/5000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((21/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((21/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1587141637357/100000000000000),(39102197343/100000000000000),(120944457/100000000000000),(-221859/20000000000000),(2089/25000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((21/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((21/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(2330724712107/12500000000000),(454447871363/100000000000000),(657299557/50000000000000),(-13081611/100000000000000),(5093/5000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((21/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1761396304367917/100000000000000),(-5410097757411/25000000000000),(67399793839/100000000000000),(-205759583/100000000000000),(880299/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((21/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3749394565421083/100000000000000),(-48912963142433/100000000000000),(116524181623/100000000000000),(-252572067/100000000000000),(179679/6250000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((21/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(87558883211659/2000000000000),(47767270276371/100000000000000),(-28323177841/12500000000000),(177755257/20000000000000),(4138501/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((21/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(13779631345873111/100000000000000),(43940319792423/25000000000000),(-14840001547/3125000000000),(282217543/25000000000000),(2064197/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((21/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(4175013951375951/25000000000000),(15625248405159/6250000000000),(-204895576863/100000000000000),(-92813161/10000000000000),(5965901/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((21/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(126783503575999/100000000000000),(69896381129/20000000000000),(-830736193/100000000000000),(1808723/100000000000000),(5119/25000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((21/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((21/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((21/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((21/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(263709942953659/400000000000),(166114599252679/100000000000000),(-523330947103/100000000000000),(1352733327/100000000000000),(7657447/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((21/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(30336360891/20000000000000),(-191093001/50000000000000),(135439/6250000000000),(-11607/100000000000000),(23/25000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((21/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(1266547299539/5000000000000),(315385264089/100000000000000),(-452187643/50000000000000),(1427273/50000000000000),(81799/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((21/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((21/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((21/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (21/8) (1/40))

def c344 : Certificate := ⟨(17452947049993/100000000000000),(-37128822373/50000000000000),(411782781/100000000000000),(-570867/25000000000000),(6419/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((21/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(402509490667/4000000000000),(99010192993/100000000000000),(-54904371/10000000000000),(3044623/100000000000000),(31919/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((21/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((21/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(1012586812981/100000000000000),(2490783897/12500000000000),(-12467469/100000000000000),(-237237/50000000000000),(7783/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((21/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((21/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((21/8)+(1/40)*x)) := (SharedCertificates.h144 (21/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(11947253854597/100000000000000),(46619973833/20000000000000),(-87719741/50000000000000),(-5416361/100000000000000),(184767/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((21/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((21/8)+(1/40)*x)) := (SharedCertificates.h148 (21/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-140758099656853/10000000000000),(-13826141792519/100000000000000),(7701366237/10000000000000),(-427882029/100000000000000),(4486423/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((21/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((21/8)+(1/40)*x)) := (SharedCertificates.h151 (21/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-2959207612169337/100000000000000),(-1220311640879/4000000000000),(38880216639/25000000000000),(-393121841/50000000000000),(2779779/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((21/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((21/8)+(1/40)*x)) := (SharedCertificates.h154 (21/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(3576376560481827/100000000000000),(4014886034753/12500000000000),(-104845325831/50000000000000),(1324448121/100000000000000),(3763569/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((21/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((21/8)+(1/40)*x)) := (SharedCertificates.h157 (21/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(1365719438369623/12500000000000),(13841717430401/12500000000000),(-58543121411/10000000000000),(611010823/20000000000000),(3965091/10000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((21/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((21/8)+(1/40)*x)) := (SharedCertificates.h160 (21/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(12764734272137463/100000000000000),(147881616400881/100000000000000),(-297507836953/50000000000000),(420353601/20000000000000),(33955049/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((21/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((21/8)+(1/40)*x)) := (SharedCertificates.h41 (21/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(121138061346331/100000000000000),(108973328581/50000000000000),(-1110554889/100000000000000),(1403693/25000000000000),(19851/25000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((21/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((21/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((21/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((21/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((21/8)+(1/40)*x)) := (SharedCertificates.h167 (21/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(63211094375895233/100000000000000),(106123257731093/100000000000000),(-147105415353/25000000000000),(1594582307/50000000000000),(47461057/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((21/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(158200077039/100000000000000),(-265597483/100000000000000),(959281/50000000000000),(-3419/25000000000000),(11/6250000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((21/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4038763890469/20000000000000),(100023009067/50000000000000),(-217837153/20000000000000),(149921/2500000000000),(167689/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((21/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((21/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(300124522964011/100000000000000),(2023020279733/50000000000000),(-149190551/12500000000000),(6475647/6250000000000),(23531/800000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((21/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(114333151605337/100000000000000),(45246162641/10000000000000),(-4763834313/100000000000000),(4242023/5000000000000),(961603/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((21/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((21/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(8605879211425781/50000000000000),(193596954345703/25000000000000),(56889/409600),(2541/2048000),(69091797/12500000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((21/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(2025/64),(9/32),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((21/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(91125/512),(1215/512),(27/2560),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((21/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(765830803848803021/25000000000000),(178668703794479279/100000000000000),(561389688849449/12500000000000),(63477551651/100000000000),(277116823601/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((21/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(3264428627/100000000000000),(-95199101/50000000000000),(6319041/100000000000000),(-157063/100000000000000),(973/20000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((21/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(345794030377/6250000000000),(-783959309/5000000000000),(-92961637/50000000000000),(231383/5000000000000),(628491/4000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((21/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((21/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((21/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel32

namespace Hf4Quad.Panel33
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(107/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((107/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (107/40) (1/40)

def c3 : Certificate := ⟨(29297619047619/6250000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((107/40)+(1/40)*x)) := (SharedCertificates.h2 (107/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((107/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-377333333333333/100000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((107/40)+(1/40)*x)) := (SharedCertificates.h4 (107/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(11449/1600),(107/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((107/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(866247089947089/100000000000000),(8095767195767/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((107/40)+(1/40)*x)) := (SharedCertificates.h8 (107/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((107/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((107/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1225043/64000),(34347/64000),(321/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((107/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(9324292857349537/50000000000000),(522857543402777/100000000000000),(2443259548611/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((107/40)+(1/40)*x)) := (SharedCertificates.h13 (107/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((107/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((107/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(131079601/2560000),(1225043/640000),(34347/1280000),(107/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((107/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(3576080384424603/25000000000000),(133685248015873/25000000000000),(7496369047619/100000000000000),(23353174603/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((107/40)+(1/40)*x)) := (SharedCertificates.h18 (107/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((107/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(13696794245117187/100000000000000),(160009278564453/25000000000000),(1225043/10240000),(11449/10240000),(523437501/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((107/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(89232078063559747/100000000000000),(833944654799623/20000000000000),(77938752785011/100000000000000),(364199779369/50000000000000),(3410098389/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((107/40)+(1/40)*x)) := (SharedCertificates.h22 (107/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((107/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(1465556984227539/4000000000000),(256814892095947/12500000000000),(9600556713867/20000000000000),(598165527343/100000000000000),(4208447271/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((107/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(82272802130445443/100000000000000),(4613428156847403/100000000000000),(6736898593527/6250000000000),(1343182274097/100000000000000),(9450079483/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((107/40)+(1/40)*x)) := (SharedCertificates.h26 (107/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((107/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(9800912332021667/10000000000000),(6411811805995477/100000000000000),(4494260611679/2500000000000),(22401298999/800000000000),(13158472909/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((107/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1453607533370277/6250000000000),(1521533119041783/100000000000000),(42659807075937/100000000000000),(33224148813/5000000000000),(6245053017/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((107/40)+(1/40)*x)) := (SharedCertificates.h30 (107/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((107/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((107/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((107/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((107/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((107/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (107/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((107/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((107/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (107/40) (1/40))

def c43 : Certificate := ⟨(21609/1600),(147/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((107/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((107/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(35258677491/100000000000000),(-239854949/50000000000000),(2447499/50000000000000),(-111/250000000000),(97/25000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((107/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1038261064060439/100000000000000),(116185742063/100000000000000),(-801772569/100000000000000),(2779747/50000000000000),(4543869/20000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((107/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((107/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (107/40) (1/40))

def c52 : Certificate := ⟨(155833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((107/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (107/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((107/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (107/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((107/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (107/40) (1/40))

def c56 : Certificate := ⟨(21937842778793/100000000000000),(-40105745483/100000000000000),(73319461/100000000000000),(-3351/2500000000000),(249/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((107/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(489945155393/4000000000000),(20052872741/12500000000000),(-293277847/100000000000000),(134039/25000000000000),(631/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((107/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((107/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((107/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((107/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((107/40)+(1/40)*x)) := (SharedCertificates.h61 (107/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-180482538961041/100000000000000),(-124085856771/5000000000000),(2992828051/100000000000000),(-105937/4000000000000),(701/2000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((107/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((107/40)+(1/40)*x)) := (SharedCertificates.h61 (107/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-96793720393399/50000000000000),(-1419716769871/50000000000000),(1020540931/100000000000000),(1640631/50000000000000),(25343/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((107/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((107/40)+(1/40)*x)) := (SharedCertificates.h67 (107/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-220278957281839/25000000000000),(-11887959156823/100000000000000),(3333419337/20000000000000),(-2820233/10000000000000),(110069/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((107/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((107/40)+(1/40)*x)) := (SharedCertificates.h67 (107/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-965328629893009/100000000000000),(-2819846604277/20000000000000),(190126221/3125000000000),(1589313/10000000000000),(54261/20000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((107/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((107/40)+(1/40)*x)) := (SharedCertificates.h72 (107/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(2280989280297/195312500000),(3392210350141/25000000000000),(-12459069397/25000000000000),(104177527/100000000000000),(22213/10000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((107/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((107/40)+(1/40)*x)) := (SharedCertificates.h72 (107/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(2858307335543779/100000000000000),(40759872824543/100000000000000),(-46389971/125000000000),(-88849927/100000000000000),(561593/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((107/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((107/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((107/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(125997546865231/100000000000000),(18007259763/5000000000000),(-401045393/100000000000000),(52537/20000000000000),(5423/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((107/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5804640184650583/50000000000000),(11959849125917/100000000000000),(-29408168997/50000000000000),(6586447/5000000000000),(519413/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((107/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(430689917113/50000000000000),(-13865487/1562500000000),(2639107/50000000000000),(-4927/25000000000000),(69/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((107/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(769402593393/3125000000000),(81433239529/25000000000000),(-265253509/50000000000000),(1152071/100000000000000),(11447/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((107/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((107/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((107/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (107/40) (1/40))

def c87 : Certificate := ⟨(17621145374449/100000000000000),(-77626191077/100000000000000),(341965599/100000000000000),(-1506457/100000000000000),(6669/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((107/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(4919236417033/50000000000000),(51750794051/50000000000000),(-455954133/100000000000000),(62769/3125000000000),(1021/6250000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((107/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((107/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((107/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((107/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((107/40)+(1/40)*x)) := (SharedCertificates.h61 (107/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-35886588134831/25000000000000),(-1571217940967/100000000000000),(6278910219/100000000000000),(-3103609/12500000000000),(8929/3125000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((107/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((107/40)+(1/40)*x)) := (SharedCertificates.h61 (107/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-151861388575799/100000000000000),(-350435767651/20000000000000),(6029376743/100000000000000),(-19783773/100000000000000),(7339/2000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((107/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((107/40)+(1/40)*x)) := (SharedCertificates.h67 (107/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-351816969922543/50000000000000),(-1893669438759/25000000000000),(3923609157/12500000000000),(-131369649/100000000000000),(51539/4000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((107/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((107/40)+(1/40)*x)) := (SharedCertificates.h67 (107/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-189479983101887/25000000000000),(-4359308041251/50000000000000),(15186655669/50000000000000),(-100635537/100000000000000),(1820283/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((107/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((107/40)+(1/40)*x)) := (SharedCertificates.h72 (107/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(479235950461521/50000000000000),(9225428909343/100000000000000),(-5045505283/10000000000000),(256968949/100000000000000),(2192719/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((107/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((107/40)+(1/40)*x)) := (SharedCertificates.h72 (107/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1127338645171399/50000000000000),(25534683413497/100000000000000),(-47660917447/50000000000000),(80576049/25000000000000),(1387447/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((107/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((107/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((107/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(60322450572599/50000000000000),(11368456373/5000000000000),(-447250163/50000000000000),(3468609/100000000000000),(21089/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((107/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(114214049586359/1000000000000),(1051707417763/12500000000000),(-25816370957/50000000000000),(69997953/25000000000000),(367959/5000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((107/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(87554902713/10000000000000),(-64497943/10000000000000),(2216611/50000000000000),(-13823/50000000000000),(1/160000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((107/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(19740805080517/100000000000000),(13064154217/6250000000000),(-224832001/25000000000000),(1972709/50000000000000),(15257/20000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((107/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((107/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-230295067290669/50000000000000),(-5500656945799/100000000000000),(7555527337/50000000000000),(-56407777/100000000000000),(2819399/25000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((107/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(37383177570093/100000000000000),(-34937549131/10000000000000),(3265191507/100000000000000),(-30515809/100000000000000),(17993/6250000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((107/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-21522903485109/12500000000000),(-447131307951/100000000000000),(4913894837/50000000000000),(-112935519/100000000000000),(3986541/50000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((107/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((107/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((107/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((107/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((107/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((107/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((107/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((107/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((107/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((107/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (107/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((107/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((107/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(516669773/25000000000000),(-9657379/12500000000000),(1805117/100000000000000),(-33741/100000000000000),(623/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((107/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(110624194547207/100000000000000),(-363527991819/100000000000000),(2966444141/100000000000000),(-23285899/100000000000000),(65468249/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((107/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((107/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (107/40) (1/40))

def c134 : Certificate := ⟨(42449/1600),(207/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((107/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((107/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(453514739229/10000000000000),(-6170268561/20000000000000),(5246827/2500000000000),(-1427709/100000000000000),(9781/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((107/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(120320294784573/100000000000000),(354963981049/100000000000000),(52468269/12500000000000),(-1427721/50000000000000),(62647/12500000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((107/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((107/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (107/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((107/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (107/40) (1/40))

def c140 : Certificate := ⟨(23791380345137/100000000000000),(-4018403673/20000000000000),(-3395503/50000000000000),(93713/50000000000000),(14353/50000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((107/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(96689572389/2000000000000),(80368073459/100000000000000),(13582011/50000000000000),(-149941/20000000000000),(126487/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((107/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((107/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(233721835219/100000000000000),(242836083/3125000000000),(67216749/100000000000000),(-28827/100000000000000),(6817/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((107/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((107/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(1391031779161/50000000000000),(46061014727/50000000000000),(787484441/100000000000000),(-56487/12500000000000),(163053/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((107/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-338346254227547/50000000000000),(-11244840773559/100000000000000),(-3690099893/100000000000000),(52786953/50000000000000),(17713641/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((107/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-693184284043341/50000000000000),(-5897633680949/25000000000000),(-8502701023/50000000000000),(53518583/25000000000000),(37325327/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((107/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(448562644119331/25000000000000),(14343515607533/50000000000000),(-2424956449/25000000000000),(-11518737/4000000000000),(196611/400000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((107/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(2581472605460827/50000000000000),(87215350143939/100000000000000),(51595892037/100000000000000),(-40728331/5000000000000),(27596417/20000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((107/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(111508110302687/2000000000000),(101118011242647/100000000000000),(88251264163/50000000000000),(-813048423/100000000000000),(32449307/20000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((107/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(109902679074119/100000000000000),(84253450787/50000000000000),(121544793/100000000000000),(-1528237/100000000000000),(16663/6250000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((107/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((107/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((107/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((107/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(14404498386997277/25000000000000),(21412970064881/25000000000000),(36326843419/100000000000000),(-829873173/100000000000000),(72267027/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((107/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(86778447011/50000000000000),(-51600111/20000000000000),(137053/50000000000000),(1127/50000000000000),(223/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((107/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4838250320599/50000000000000),(161112702437/100000000000000),(15182449/25000000000000),(-1463639/100000000000000),(2439/781250000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((107/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((107/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((107/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (107/40) (1/40))

def c175 : Certificate := ⟨(1084690734011/5000000000000),(-1252902863/2500000000000),(56513603/100000000000000),(819/200000000000),(73127/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((107/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(4408247093039/100000000000000),(2672859441/4000000000000),(-75351473/100000000000000),(-546001/100000000000000),(6361/5000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((107/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((107/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(48581606083/25000000000000),(589131243/10000000000000),(38007751/100000000000000),(-148841/100000000000000),(377/3125000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((107/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((107/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(14467401963/625000000000),(69916638333/100000000000000),(445161591/100000000000000),(-453191/25000000000000),(144553/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((107/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-24682102064529/4000000000000),(-9350379172047/100000000000000),(2122761031/20000000000000),(7659237/10000000000000),(8908173/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((107/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1261510387219933/100000000000000),(-1220907974349/6250000000000),(493224721/3125000000000),(43440931/25000000000000),(7462037/20000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((107/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1641564635847007/100000000000000),(12011090943959/50000000000000),(-5052156251/12500000000000),(-6815859/4000000000000),(49280461/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((107/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(4701023673031031/100000000000000),(36159217672371/50000000000000),(-66085703119/100000000000000),(-317441991/50000000000000),(138120303/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((107/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(5043124926509881/100000000000000),(41410549363647/50000000000000),(577304543/12500000000000),(-877915743/100000000000000),(159628919/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((107/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(10901082061041/10000000000000),(436044639/312500000000),(-22539039/20000000000000),(-1240843/100000000000000),(33313/12500000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((107/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((107/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((107/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((107/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(7145494027383711/12500000000000),(71147103548719/100000000000000),(-14947335293/20000000000000),(-307093847/50000000000000),(72003187/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((107/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(174935420169/100000000000000),(-217727221/100000000000000),(249849/50000000000000),(243/25000000000000),(7/1562500000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((107/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(8822211779837/100000000000000),(133903181293/100000000000000),(-73522201/50000000000000),(-1082967/100000000000000),(152653/50000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((107/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((107/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(10232025808687/50000000000000),(129555473693/50000000000000),(-123839237/20000000000000),(388101/20000000000000),(6525703/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((107/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(3825056377079/50000000000000),(6341881171/25000000000000),(-732117/156250000000),(5104439/100000000000000),(1272761/25000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((107/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((107/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((107/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((107/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((107/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((107/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (107/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((107/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((107/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((107/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (107/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((107/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(17761756673/50000000000000),(-38756719/100000000000000),(1532927/100000000000000),(-3299/100000000000000),(71/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((107/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(206022501034399/50000000000000),(-863086961293/50000000000000),(-2144792403/25000000000000),(-630767/1000000000000),(476943/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((107/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((107/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((107/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((107/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (107/40) (1/40))

def c223 : Certificate := ⟨(34969/1600),(187/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((107/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(4269330241/2560000),(19580583/640000),(253187/1280000),(327/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((107/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((107/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(82270247479/100000000000000),(-223864619/20000000000000),(356927/3125000000000),(-51799/50000000000000),(899/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((107/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(68601338964189/50000000000000),(325163612859/50000000000000),(1075927637/100000000000000),(-2698963/100000000000000),(152823/5000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((107/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((107/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (107/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((107/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (107/40) (1/40))

def c231 : Certificate := ⟨(22872686982119/100000000000000),(-34022506771/100000000000000),(-2840323/50000000000000),(1867/800000000000),(6437/4000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((107/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(8509252071523/100000000000000),(3402250677/2500000000000),(22722583/100000000000000),(-7293/781250000000),(95429/12500000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((107/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((107/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(724073708167/100000000000000),(1447530431/6250000000000),(94535999/50000000000000),(-97023/100000000000000),(67271/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((107/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((107/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(428282899199/5000000000000),(272013490119/100000000000000),(2173319467/100000000000000),(-414847/25000000000000),(1604003/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((107/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-1190566416583779/100000000000000),(-4754450117847/25000000000000),(-1312049409/50000000000000),(133488877/100000000000000),(106960179/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((107/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-2483898877492453/100000000000000),(-5167965290213/12500000000000),(-32737471677/100000000000000),(275961537/100000000000000),(232601093/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((107/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(3064700830848791/100000000000000),(11374070055669/25000000000000),(-2543330421/5000000000000),(-183338139/50000000000000),(148068989/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((107/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(9195497794034133/100000000000000),(150936673791937/100000000000000),(20535655871/25000000000000),(-219775233/20000000000000),(851886119/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((107/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1312456356018819/12500000000000),(9680500169637/5000000000000),(226418293821/50000000000000),(-1046702907/100000000000000),(68586451/6250000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((107/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(117742577851213/100000000000000),(2307347977/781250000000),(58629291/25000000000000),(-1964031/100000000000000),(830703/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((107/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((107/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((107/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((107/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(7693287788910267/12500000000000),(145790189235099/100000000000000),(7728785751/25000000000000),(-1183659173/100000000000000),(459345757/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((107/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(10154956131/6250000000000),(-12027473/3125000000000),(415041/50000000000000),(1351/100000000000000),(613/25000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((107/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(3411951800121/20000000000000),(133869731/48828125000),(4859807/6250000000000),(-847289/50000000000000),(2059873/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((107/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((107/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((107/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (107/40) (1/40))

def c259 : Certificate := ⟨(19546213780137/100000000000000),(-74538127677/100000000000000),(160927079/100000000000000),(165929/100000000000000),(355849/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((107/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(908964369977/12500000000000),(19876834047/20000000000000),(-214569439/100000000000000),(-221239/100000000000000),(184809/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((107/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((107/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(66097298071/12500000000000),(14453867149/100000000000000),(8445797/12500000000000),(-28667/6250000000000),(54503/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((107/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((107/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(3134219050513/50000000000000),(1330416201/781250000000),(30980381/4000000000000),(-1376823/25000000000000),(650869/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((107/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-1017584271423101/100000000000000),(-6947585378123/50000000000000),(30251835989/100000000000000),(30963459/100000000000000),(51775723/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((107/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2110076016442289/100000000000000),(-2984930256097/10000000000000),(25326547453/50000000000000),(126330113/100000000000000),(27781001/12500000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((107/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(661542886544509/25000000000000),(33995267800479/100000000000000),(-1625996699/1562500000000),(430663/1000000000000),(285694341/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((107/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(3913861379996311/50000000000000),(10945529335519/10000000000000),(-204757093663/100000000000000),(-102847511/25000000000000),(817261777/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((107/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(877372008170941/10000000000000),(135830967255819/100000000000000),(-71105946839/100000000000000),(-1203474619/100000000000000),(40578467/4000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((107/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(575361041521/500000000000),(213222207619/100000000000000),(-180786251/50000000000000),(-18023/2000000000000),(793739/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((107/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((107/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((107/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((107/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(60221239115995333/100000000000000),(21269460805297/20000000000000),(-223422536921/100000000000000),(-334263161/100000000000000),(870866323/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((107/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(83027185647/50000000000000),(-293242633/100000000000000),(283479/25000000000000),(-2169/100000000000000),(2419/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((107/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(14569145720777/100000000000000),(199824970919/100000000000000),(-208451111/50000000000000),(-440003/100000000000000),(951653/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((107/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((107/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(32581330278389/25000000000000),(281416588343/20000000000000),(-2458564713/20000000000000),(-7944511/12500000000000),(17244727/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((107/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(24359873105337/50000000000000),(70687583717/100000000000000),(-2628039843/50000000000000),(12681477/50000000000000),(7497137/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((107/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((107/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((107/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((107/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((107/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((107/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (107/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((107/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(109025909358350039/10000000000000),(594745005101989/50000000000000),(-45749615777077/100000000000000),0,(140913/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((107/40)+(1/40)*x)) := (SharedCertificates.h297 (107/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(1834426341/20000000000000),(-5003471/50000000000000),(1979/500000000000),(-213/25000000000000),(1/5000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((107/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(165535838377961/25000000000000),(1464571192507/100000000000000),(10422479617/100000000000000),(3129153/6250000000000),(583379/25000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((107/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((107/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (107/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((107/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (107/40) (1/40))

def c307 : Certificate := ⟨(3486224710489627/100000000000000),(11091229182759/50000000000000),0,0,(1087/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((107/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (107/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((107/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (107/40) (1/40))

def c311 : Certificate := ⟨(1094387644755057/50000000000000),(2817541634481/100000000000000),0,0,(1087/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((107/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (107/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(571095628679/12500000000000),(-5881227621/100000000000000),(7570719/100000000000000),(-4873/50000000000000),(17/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((107/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(159277415420267/100000000000000),(202107897467/25000000000000),(-65041787/6250000000000),(334901/25000000000000),(281/10000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((107/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((107/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (107/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((107/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (107/40) (1/40))

def c316 : Certificate := ⟨(1360833298167/6250000000000),(-38325964739/100000000000000),(116798131/100000000000000),(-355941/100000000000000),(1143/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((107/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(3226667229327/25000000000000),(153303858953/100000000000000),(-467192529/100000000000000),(1423763/100000000000000),(5913/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((107/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((107/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(166582102541/10000000000000),(1582913721/4000000000000),(22884549/20000000000000),(-33279/3125000000000),(2027/25000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((107/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((107/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(1955984829591/10000000000000),(57443938601/12500000000000),(618884201/50000000000000),(-1566593/12500000000000),(98653/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((107/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-45110228089071/2500000000000),(-21373241459431/100000000000000),(8272479597/12500000000000),(-100457669/50000000000000),(858107/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((107/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-769351281667639/20000000000000),(-12112470709157/25000000000000),(115019581219/100000000000000),(-248965197/100000000000000),(559813/20000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((107/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(111814485487101/2500000000000),(46871493709853/100000000000000),(-110663854313/50000000000000),(215982659/25000000000000),(4029143/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((107/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(14129263380909861/100000000000000),(10867202328449/6250000000000),(-5851974229/1250000000000),(138981339/12500000000000),(1254391/12500000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((107/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(4299809213307587/25000000000000),(124586733156603/50000000000000),(-105153087277/50000000000000),(-875781229/100000000000000),(11639887/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((107/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(63739579430013/50000000000000),(346180560931/100000000000000),(-819962313/100000000000000),(891299/50000000000000),(9967/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((107/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((107/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((107/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((107/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(66257632392652219/100000000000000),(82018711775153/50000000000000),(-103055613773/20000000000000),(66578969/5000000000000),(464561/3125000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((107/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(30185201731/20000000000000),(-46706909/12500000000000),(2098811/100000000000000),(-87/781250000000),(89/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((107/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(259581217017/1000000000000),(311801712087/100000000000000),(-443738517/50000000000000),(2778411/100000000000000),(79649/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((107/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((107/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((107/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (107/40) (1/40))

def c344 : Certificate := ⟨(3461212164849/20000000000000),(-18159378899/25000000000000),(398380343/100000000000000),(-436983/20000000000000),(12149/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((107/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(10258585567671/100000000000000),(48425010397/50000000000000),(-531173791/100000000000000),(2913219/100000000000000),(30601/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((107/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((107/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(263096444623/25000000000000),(1987088451/10000000000000),(-15182571/100000000000000),(-215587/50000000000000),(3709/25000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((107/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((107/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((107/40)+(1/40)*x)) := (SharedCertificates.h144 (107/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(6206354775363/50000000000000),(29041899881/12500000000000),(-41277147/20000000000000),(-2453217/50000000000000),(176163/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((107/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((107/40)+(1/40)*x)) := (SharedCertificates.h148 (107/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1434928611043413/100000000000000),(-13523146894181/100000000000000),(74502242111/100000000000000),(-40942637/10000000000000),(4301791/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((107/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((107/40)+(1/40)*x)) := (SharedCertificates.h151 (107/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-1509803669173381/50000000000000),(-29895018076077/100000000000000),(150896331859/100000000000000),(-755518439/100000000000000),(532381/5000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((107/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((107/40)+(1/40)*x)) := (SharedCertificates.h154 (107/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(3639786440941359/100000000000000),(15647980830399/50000000000000),(-25242006083/12500000000000),(39407927/3125000000000),(14381797/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((107/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((107/40)+(1/40)*x)) := (SharedCertificates.h157 (107/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(5572452726289503/50000000000000),(108428178764807/100000000000000),(-567471709141/100000000000000),(1466235059/50000000000000),(593159/1562500000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((107/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((107/40)+(1/40)*x)) := (SharedCertificates.h160 (107/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6529067085316123/50000000000000),(72763301663199/50000000000000),(-582533828491/100000000000000),(2058813797/100000000000000),(8121497/12500000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((107/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((107/40)+(1/40)*x)) := (SharedCertificates.h41 (107/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(60784778456917/50000000000000),(106785463049/50000000000000),(-1077530153/100000000000000),(84301/1562500000000),(38019/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((107/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((107/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((107/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((107/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((107/40)+(1/40)*x)) := (SharedCertificates.h167 (107/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(31710506225231359/50000000000000),(103807307264771/100000000000000),(-284842665769/50000000000000),(1528701981/50000000000000),(2273221/5000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((107/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(31535289689/20000000000000),(-258084299/100000000000000),(73551/4000000000000),(-1293/10000000000000),(83/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((107/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4117920438687/20000000000000),(19576018563/10000000000000),(-52699513/5000000000000),(2868591/50000000000000),(39873/25000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((107/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((107/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(7705316499567/2500000000000),(4042511925627/100000000000000),(-22810571/4000000000000),(104156589/100000000000000),(57233/2000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((107/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(7201230373427/6250000000000),(86879983271/20000000000000),(-4272995211/100000000000000),(3154863/4000000000000),(3598547/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((107/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((107/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(18817091159179687/100000000000000),(207862520751953/25000000000000),(1499819/10240000),(13161/10240000),(562500001/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((107/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(51529/1600),(227/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((107/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(11697083/64000),(154587/64000),(681/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((107/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(3439141829804547043/100000000000000),(197412785973802763/100000000000000),(4885455106423521/100000000000000),(68009242541381/100000000000000),(146263421323/25000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((107/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(2907702123/100000000000000),(-166907213/100000000000000),(2725123/50000000000000),(-26651/20000000000000),(507/12500000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((107/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5500638400103/100000000000000),(-16369433073/100000000000000),(-79856473/50000000000000),(411697/10000000000000),(1460571/10000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((107/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((107/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((107/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel33
