import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel37
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(23/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((23/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (23/8) (1/40)

def c3 : Certificate := ⟨(503809523809523/100000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((23/8)+(1/40)*x)) := (SharedCertificates.h2 (23/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((23/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-51547619047619/12500000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((23/8)+(1/40)*x)) := (SharedCertificates.h4 (23/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(529/64),(23/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((23/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(1000621693121693/100000000000000),(4350529100529/25000000000000),(75661375661/100000000000000),0,(1/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((23/8)+(1/40)*x)) := (SharedCertificates.h8 (23/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((23/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((23/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(12167/512),(1587/2560),(69/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((23/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(2893997169777199/12500000000000),(603964626736111/100000000000000),(1312966579861/25000000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((23/8)+(1/40)*x)) := (SharedCertificates.h13 (23/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((23/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((23/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(279841/4096),(12167/5120),(1587/51200),(23/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((23/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(19086377728174603/100000000000000),(663874007936507/100000000000000),(2164806547619/25000000000000),(25099206349/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((23/8)+(1/40)*x)) := (SharedCertificates.h18 (23/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((23/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(19642160034179687/100000000000000),(213501739501953/25000000000000),(12167/81920),(529/409600),(562500001/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((23/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(63982517592818647/50000000000000),(5563697181984227/100000000000000),(9675995099103/10000000000000),(420695439091/50000000000000),(1832291671/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((23/8)+(1/40)*x)) := (SharedCertificates.h22 (23/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((23/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(282356050491333/500000000000),(2946324005126951/100000000000000),(12810104370117/20000000000000),(742614746093/100000000000000),(4860009771/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((23/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(1585078145879917/1250000000000),(3307989174010259/50000000000000),(143825616261313/100000000000000),(1667543376941/100000000000000),(852591/7812500000)⟩
theorem h27 : c27.Valid (fun x => f27 ((23/8)+(1/40)*x)) := (SharedCertificates.h26 (23/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((23/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(6494189161300659/4000000000000),(9882461767196649/100000000000000),(51560670089721/20000000000000),(1868140220641/50000000000000),(32659396989/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((23/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(19263517452667629/50000000000000),(1172561931901507/50000000000000),(61177144273121/100000000000000),(22165631983/2500000000000),(1937531687/25000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((23/8)+(1/40)*x)) := (SharedCertificates.h30 (23/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((23/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((23/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((23/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((23/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((23/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (23/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((23/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((23/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (23/8) (1/40))

def c43 : Certificate := ⟨(961/64),(31/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((23/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((23/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(31712997373/100000000000000),(-409199967/100000000000000),(3959999/100000000000000),(-6813/20000000000000),(283/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((23/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-518690104541237/50000000000000),(104346020691/100000000000000),(-682417587/100000000000000),(2239327/50000000000000),(9189631/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((23/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((23/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (23/8) (1/40))

def c52 : Certificate := ⟨(81249999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((23/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (23/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((23/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (23/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((23/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (23/8) (1/40))

def c56 : Certificate := ⟨(21621621621621/100000000000000),(-9739469199/25000000000000),(17548593/25000000000000),(-126477/100000000000000),(231/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((23/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1689189189189/12500000000000),(77915753591/50000000000000),(-280777491/100000000000000),(31619/6250000000000),(241/20000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((23/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((23/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((23/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((23/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((23/8)+(1/40)*x)) := (SharedCertificates.h61 (23/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-200146092037961/100000000000000),(-97373633677/4000000000000),(1464596103/50000000000000),(-663141/25000000000000),(33057/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((23/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((23/8)+(1/40)*x)) := (SharedCertificates.h61 (23/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-43247191676697/20000000000000),(-22050755867/781250000000),(109521681/10000000000000),(2946027/100000000000000),(48529/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((23/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((23/8)+(1/40)*x)) := (SharedCertificates.h67 (23/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-195033404280613/20000000000000),(-11626587735621/100000000000000),(16011229313/100000000000000),(-26477487/100000000000000),(13299/12500000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((23/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((23/8)+(1/40)*x)) := (SharedCertificates.h67 (23/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-134715659145307/12500000000000),(-3499745868637/25000000000000),(32191333/500000000000),(13670653/100000000000000),(127989/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((23/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((23/8)+(1/40)*x)) := (SharedCertificates.h72 (23/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(1273280368491417/100000000000000),(1598889774259/12500000000000),(-9480083497/20000000000000),(24713473/25000000000000),(108151/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((23/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((23/8)+(1/40)*x)) := (SharedCertificates.h72 (23/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(1590983833579743/50000000000000),(8030003891467/20000000000000),(-7811836313/20000000000000),(-73718471/100000000000000),(1047911/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((23/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((23/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((23/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(64426588750911/50000000000000),(176889818963/50000000000000),(-78921241/20000000000000),(273459/100000000000000),(511/10000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((23/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5850630762244993/50000000000000),(690228854397/6250000000000),(-11146599769/20000000000000),(125253039/100000000000000),(977661/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((23/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(427304354281/50000000000000),(-403290253/50000000000000),(9437/195312500000),(-351/2000000000000),(61/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((23/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(6798343196793/25000000000000),(317460431861/100000000000000),(-251950433/50000000000000),(21331/2000000000000),(21239/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((23/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((23/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((23/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (23/8) (1/40))

def c87 : Certificate := ⟨(531914893617/3125000000000),(-36215482119/50000000000000),(308216869/100000000000000),(-655781/50000000000000),(5609/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((23/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(10638297872339/100000000000000),(48287309491/50000000000000),(-205477913/50000000000000),(1748747/100000000000000),(7243/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((23/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((23/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((23/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((23/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((23/8)+(1/40)*x)) := (SharedCertificates.h61 (23/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-155726573109983/100000000000000),(-295066282677/20000000000000),(28592033/500000000000),(-21952353/100000000000000),(251953/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((23/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((23/8)+(1/40)*x)) := (SharedCertificates.h61 (23/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-41375706731643/25000000000000),(-1659387160743/100000000000000),(223075777/4000000000000),(-17955589/100000000000000),(323317/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((23/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((23/8)+(1/40)*x)) := (SharedCertificates.h67 (23/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-762287534779321/100000000000000),(-887073450283/12500000000000),(14218895571/50000000000000),(-115011473/100000000000000),(1142397/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((23/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((23/8)+(1/40)*x)) := (SharedCertificates.h67 (23/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-51610954353579/6250000000000),(-8251355738901/100000000000000),(28071367347/100000000000000),(-18270101/20000000000000),(160113/10000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((23/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((23/8)+(1/40)*x)) := (SharedCertificates.h72 (23/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(32161651364167/3125000000000),(423252093539/5000000000000),(-44739189841/100000000000000),(220478819/100000000000000),(1923241/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((23/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((23/8)+(1/40)*x)) := (SharedCertificates.h72 (23/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(1226507749324659/50000000000000),(6017395557383/25000000000000),(-87928427677/100000000000000),(58830789/20000000000000),(96973/2000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((23/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((23/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((23/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(30602082390221/25000000000000),(53424257309/25000000000000),(-204020623/25000000000000),(3075809/100000000000000),(18583/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((23/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1148554751837249/10000000000000),(7638532108817/100000000000000),(-5677850529/12500000000000),(7462587/3125000000000),(3207727/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((23/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(870659407747/100000000000000),(-2316149/400000000000),(3828357/100000000000000),(-22939/100000000000000),(533/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((23/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(10678705106241/50000000000000),(195360208601/100000000000000),(-162203757/20000000000000),(3428989/100000000000000),(8259/12500000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((23/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((23/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-503656214192989/100000000000000),(-5269239022169/100000000000000),(6922252537/50000000000000),(-9866611/20000000000000),(9960333/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((23/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(8695652173913/25000000000000),(-302457466919/100000000000000),(2630064929/100000000000000),(-2287013/10000000000000),(200617/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((23/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-175184770154083/100000000000000),(-77358240723/25000000000000),(1501240289/20000000000000),(-1030383/1250000000000),(1559691/25000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((23/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((23/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((23/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((23/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((23/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((23/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((23/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((23/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((23/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((23/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (23/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((23/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((23/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1548876517/100000000000000),(-26936983/50000000000000),(1171173/100000000000000),(-20369/100000000000000),(87/25000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((23/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(53947296483523/50000000000000),(-80049140497/25000000000000),(24693771/1000000000000),(-18446343/100000000000000),(47647911/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((23/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((23/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (23/8) (1/40))

def c134 : Certificate := ⟨(1833/64),(43/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((23/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((23/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(4301075268817/100000000000000),(-27748872703/100000000000000),(35804997/20000000000000),(-231/20000000000),(3751/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((23/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(123185483870961/100000000000000),(72233784247/20000000000000),(71609993/20000000000000),(-2310003/100000000000000),(208061/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((23/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((23/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (23/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((23/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (23/8) (1/40))

def c140 : Certificate := ⟨(945212005717/4000000000000),(-806694023/4000000000000),(-556261/20000000000000),(5937/4000000000000),(23513/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((23/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(5478799428297/100000000000000),(10083675287/12500000000000),(11125219/100000000000000),(-296851/50000000000000),(52473/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((23/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((23/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(60034486351/20000000000000),(8839429503/100000000000000),(66294581/100000000000000),(-47107/100000000000000),(3157/25000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((23/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((23/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(356917749011/10000000000000),(26155067549/25000000000000),(386971229/50000000000000),(-166371/25000000000000),(15099/10000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((23/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-766836371885657/100000000000000),(-11285105152527/100000000000000),(-35758357/2500000000000),(83696603/100000000000000),(14698277/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((23/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-315215453336401/20000000000000),(-186127525291/781250000000),(-96737231/781250000000),(172965517/100000000000000),(6230603/20000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((23/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(505746916904463/25000000000000),(14240510443943/50000000000000),(-15419411/97656250000),(-222380923/100000000000000),(10196709/25000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((23/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(1172714967295963/20000000000000),(87895222480367/100000000000000),(8504234327/25000000000000),(-164287531/25000000000000),(114964103/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((23/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(1279049281789899/20000000000000),(103794299851843/100000000000000),(15852269181/10000000000000),(-138115941/20000000000000),(137564747/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((23/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(111257771288349/100000000000000),(34035646819/20000000000000),(88545019/100000000000000),(-1234511/100000000000000),(5563/2500000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((23/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((23/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((23/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((23/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(58305130901741539/100000000000000),(86084778072853/100000000000000),(18430204461/100000000000000),(-668445213/100000000000000),(24218531/20000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((23/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(171511492133/100000000000000),(-63307159/25000000000000),(63933/20000000000000),(787/50000000000000),(73/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((23/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(10968582541571/100000000000000),(80912278587/50000000000000),(7372777/25000000000000),(-576697/50000000000000),(263903/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((23/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((23/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((23/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (23/8) (1/40))

def c175 : Certificate := ⟨(10648346930013/50000000000000),(-49142359269/100000000000000),(16169641/25000000000000),(6937/2500000000000),(29201/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((23/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1234435379991/25000000000000),(6552314569/10000000000000),(-43119043/50000000000000),(-14799/4000000000000),(104949/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((23/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((23/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(243812913179/100000000000000),(6470727139/100000000000000),(17208199/50000000000000),(-149549/100000000000000),(2729/25000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((23/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((23/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(2901677255257/100000000000000),(38345101163/50000000000000),(401538861/100000000000000),(-1811957/100000000000000),(3269/2500000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((23/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-21598141733511/3125000000000),(-9167552362423/100000000000000),(12140906473/100000000000000),(51893259/100000000000000),(14698257/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((23/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-35417358969281/2500000000000),(-37601577837/195312500000),(9667654169/50000000000000),(124573427/100000000000000),(15456823/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((23/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(228884722452763/12500000000000),(2918441749601/12500000000000),(-43639726617/100000000000000),(-101776181/100000000000000),(20310931/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((23/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(1055008496749887/20000000000000),(71151923615787/100000000000000),(-15797170983/20000000000000),(-449002313/100000000000000),(22858167/20000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((23/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(356597782612117/6250000000000),(10342330833429/12500000000000),(-1420645921/10000000000000),(-349037861/50000000000000),(66917469/50000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((23/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(110119295953107/100000000000000),(137517018519/100000000000000),(-69029887/50000000000000),(-889499/100000000000000),(110407/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((23/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((23/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((23/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((23/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(57728057580399/100000000000),(4365392602873/6250000000000),(-43558272763/50000000000000),(-106630827/25000000000000),(11965143/10000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((23/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(1353328057/781250000000),(-209589443/100000000000000),(514999/100000000000000),(17/5000000000000),(91/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((23/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(988352070191/10000000000000),(131366579973/100000000000000),(-168637149/100000000000000),(-183493/25000000000000),(50973/20000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((23/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((23/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(11249145959811/50000000000000),(15598104147/6250000000000),(-287000967/50000000000000),(1802719/100000000000000),(5344127/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((23/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7825492841607/100000000000000),(1875907663/10000000000000),(-362775253/100000000000000),(4727/125000000000),(3873709/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((23/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((23/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((23/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((23/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((23/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((23/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (23/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((23/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((23/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((23/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (23/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((23/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(8827537503/25000000000000),(-2945581/20000000000000),(1478933/100000000000000),(-77/6250000000000),(33/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((23/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(397652978455453/100000000000000),(-1876196915093/100000000000000),(-10217344303/100000000000000),(-74004079/100000000000000),(1843227/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((23/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((23/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((23/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((23/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (23/8) (1/40))

def c223 : Certificate := ⟨(1521/64),(39/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((23/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(7886385/4096),(34671/1024),(10763/51200),(67/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((23/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((23/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(4624812117/6250000000000),(-954799921/100000000000000),(9239999/100000000000000),(-19871/25000000000000),(327/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((23/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(71236423647123/50000000000000),(667060381633/100000000000000),(1017843963/100000000000000),(-433241/20000000000000),(102851/4000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((23/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((23/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (23/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((23/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (23/8) (1/40))

def c231 : Certificate := ⟨(11300128427259/50000000000000),(-34071550503/100000000000000),(-623211/100000000000000),(189959/100000000000000),(132187/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((23/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(4799486290963/50000000000000),(136286202007/100000000000000),(2492839/100000000000000),(-4749/625000000000),(320511/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((23/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((23/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(184280549257/20000000000000),(26164150327/100000000000000),(93108931/50000000000000),(-139079/100000000000000),(126883/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((23/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((23/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(10879942561449/100000000000000),(12257413403/4000000000000),(2127502149/100000000000000),(-2137129/100000000000000),(1511507/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((23/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-671405899383119/50000000000000),(-1189739111043/6250000000000),(273121187/100000000000000),(54498459/50000000000000),(89827671/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((23/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-2816608459329719/100000000000000),(-653397616557/1562500000000),(-26648456201/100000000000000),(233318699/100000000000000),(39450813/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((23/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(3425238970290241/100000000000000),(44617493761953/100000000000000),(-58659859423/100000000000000),(-57220219/20000000000000),(124422549/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((23/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(650481810040369/6250000000000),(76025730601287/50000000000000),(57879610499/100000000000000),(-465077077/50000000000000),(180068147/25000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((23/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(12076987470100411/100000000000000),(50164952691667/25000000000000),(107174598707/25000000000000),(-484610857/50000000000000),(476769791/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((23/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(120119347910137/100000000000000),(298736554341/100000000000000),(9560177/5000000000000),(-1658759/100000000000000),(1408927/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((23/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((23/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((23/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((23/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(62714021017125879/100000000000000),(146069747352939/100000000000000),(4745553533/100000000000000),(-100440311/10000000000000),(391999883/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((23/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(79726987983/50000000000000),(-185695333/50000000000000),(170591/20000000000000),(119/20000000000000),(503/25000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((23/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(1925723669799/10000000000000),(55021448447/20000000000000),(646189/1562500000000),(-1354213/100000000000000),(3559/200000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((23/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((23/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((23/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (23/8) (1/40))

def c259 : Certificate := ⟨(4740068468347/25000000000000),(-17985214571/25000000000000),(163192761/100000000000000),(15463/50000000000000),(140691/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((23/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(4026484084407/50000000000000),(95921144377/100000000000000),(-217590349/100000000000000),(-8247/20000000000000),(614197/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((23/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((23/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(648502963279/100000000000000),(15448998447/100000000000000),(3560231/6250000000000),(-53009/12500000000000),(201/200000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((23/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((23/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(3838794042467/50000000000000),(181655672581/100000000000000),(323787131/50000000000000),(-2531039/50000000000000),(1199243/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((23/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-281699317477337/25000000000000),(-13406967108939/100000000000000),(15336169159/50000000000000),(2793991/50000000000000),(10755703/12500000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((23/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-469114342548157/20000000000000),(-29018416055353/100000000000000),(13246754299/25000000000000),(71053957/100000000000000),(93023139/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((23/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(2911504601589669/100000000000000),(32342897548069/100000000000000),(-51118157911/50000000000000),(1047807/1000000000000),(237434433/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((23/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(869007911605427/10000000000000),(106114513372701/100000000000000),(-26501799999/12500000000000),(-204500621/100000000000000),(136529421/20000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((23/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(4927617593687953/50000000000000),(33619796058853/25000000000000),(-96861806539/100000000000000),(-237980839/25000000000000),(864664547/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((23/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(116754439300907/100000000000000),(207291287201/100000000000000),(-189108501/50000000000000),(-253271/50000000000000),(664447/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((23/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((23/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((23/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((23/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(61057576493408933/100000000000000),(102722696059351/100000000000000),(-228828912841/100000000000000),(-15965731/12500000000000),(146483347/20000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((23/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(20472479777/12500000000000),(-27554167/10000000000000),(8619/800000000000),(-2503/100000000000000),(991/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((23/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(1614088824569/10000000000000),(193094510757/100000000000000),(-21150423/5000000000000),(-22499/25000000000000),(1618333/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((23/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((23/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(70380849077963/50000000000000),(1197679687759/100000000000000),(-6959393571/50000000000000),(-9077029/12500000000000),(14517619/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((23/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(4896059066293/10000000000000),(-1832005483/20000000000000),(-595208107/12500000000000),(16147961/100000000000000),(362523/6250000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((23/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((23/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((23/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((23/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((23/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((23/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (23/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((23/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1096847038255399347/100000000000000),(11437403944269/2500000000000),(-45749615777077/100000000000000),0,(14167/10000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((23/8)+(1/40)*x)) := (SharedCertificates.h297 (23/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(911704153/10000000000000),(-3802729/100000000000000),(190929/50000000000000),(-159/50000000000000),(9/50000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((23/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(67455423288957/10000000000000),(410442141241/25000000000000),(11780963823/100000000000000),(31777919/50000000000000),(2059563/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((23/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((23/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (23/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((23/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (23/8) (1/40))

def c307 : Certificate := ⟨(3663684377413777/100000000000000),(11091229182759/50000000000000),0,0,(1097/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((23/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (23/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((23/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (23/8) (1/40))

def c311 : Certificate := ⟨(552828905646491/25000000000000),(2817541634481/100000000000000),0,0,(1097/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((23/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (23/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4522194795651/100000000000000),(-576194189/10000000000000),(3670781/50000000000000),(-1871/20000000000000),(1/6250000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((23/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(41419736061121/25000000000000),(792034612893/100000000000000),(-1009168701/100000000000000),(1285801/100000000000000),(679/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((23/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((23/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (23/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((23/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (23/8) (1/40))

def c316 : Certificate := ⟨(21474022228391/100000000000000),(-18261689833/50000000000000),(108655743/100000000000000),(-161623/50000000000000),(1017/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((23/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(14103911086433/100000000000000),(73046759331/50000000000000),(-848873/195312500000),(646491/50000000000000),(5393/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((23/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((23/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(99460153967/5000000000000),(824195999/2000000000000),(18167097/20000000000000),(-90519/10000000000000),(7217/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((23/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((23/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(11654663042401/50000000000000),(29817563673/6250000000000),(961284481/100000000000000),(-10565581/100000000000000),(8719/10000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((23/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1971260025474773/100000000000000),(-2035175211533/10000000000000),(15394618027/25000000000000),(-36575077/20000000000000),(779721/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((23/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-4227119865476599/100000000000000),(-46656461381431/100000000000000),(109214364447/100000000000000),(-3670313/1562500000000),(2528107/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((23/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(4833816540932939/100000000000000),(43490070706021/100000000000000),(-100858190431/50000000000000),(96543361/12500000000000),(3634667/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((23/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(7745431913884561/50000000000000),(83296944084609/50000000000000),(-221138363273/50000000000000),(522675099/50000000000000),(9017001/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((23/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(19178741962332587/100000000000000),(24565299839499/10000000000000),(-45799743577/20000000000000),(-687296107/100000000000000),(21148897/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((23/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(65098512626103/50000000000000),(166698418637/50000000000000),(-778410467/100000000000000),(840387/50000000000000),(18003/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((23/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((23/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((23/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((23/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(263818847805537/390625000000),(15604328932161/10000000000000),(-484320022949/100000000000000),(31219061/2500000000000),(13266431/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((23/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(148065615193/100000000000000),(-342100357/100000000000000),(926103/50000000000000),(-9471/100000000000000),(73/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((23/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(5679424454561/20000000000000),(4658079353/1562500000000),(-25756823/3125000000000),(2499337/100000000000000),(35367/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((23/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((23/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((23/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (23/8) (1/40))

def c344 : Certificate := ⟨(669975415367/4000000000000),(-1041557361/1562500000000),(87557063/25000000000000),(-1840089/100000000000000),(9813/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((23/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(5500409743883/50000000000000),(88879561471/100000000000000),(-93394201/20000000000000),(49069/2000000000000),(2597/10000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((23/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((23/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(151272536753/12500000000000),(19554960237/100000000000000),(-23745511/100000000000000),(-58057/20000000000000),(1541/12500000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((23/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((23/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((23/8)+(1/40)*x)) := (SharedCertificates.h144 (23/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(14255904029043/100000000000000),(114102952607/50000000000000),(-12127203/4000000000000),(-1627047/50000000000000),(29311/20000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((23/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((23/8)+(1/40)*x)) := (SharedCertificates.h148 (23/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-48079576938083/3125000000000),(-12405363501263/100000000000000),(16369711469/25000000000000),(-344826337/100000000000000),(57071/1562500000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((23/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((23/8)+(1/40)*x)) := (SharedCertificates.h151 (23/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-3249482175596563/100000000000000),(-1104736888237/4000000000000),(67056912117/50000000000000),(-64652043/10000000000000),(8999307/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((23/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((23/8)+(1/40)*x)) := (SharedCertificates.h154 (23/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(19389229171827/500000000000),(28292252886343/100000000000000),(-174403210183/100000000000000),(520950543/50000000000000),(2408927/20000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((23/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((23/8)+(1/40)*x)) := (SharedCertificates.h157 (23/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(1197745528240669/10000000000000),(12485316448213/12500000000000),(-502467722953/100000000000000),(124937787/5000000000000),(16031249/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((23/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((23/8)+(1/40)*x)) := (SharedCertificates.h160 (23/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(7093048465922603/50000000000000),(68295176502217/50000000000000),(-133795716029/25000000000000),(1887584329/100000000000000),(1368427/2500000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((23/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((23/8)+(1/40)*x)) := (SharedCertificates.h41 (23/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(30802954817389/25000000000000),(197314083179/100000000000000),(-957687521/100000000000000),(923323/20000000000000),(16067/25000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((23/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((23/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((23/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((23/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((23/8)+(1/40)*x)) := (SharedCertificates.h167 (23/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(802706416151921/1250000000000),(9524810196749/10000000000000),(-251036657091/50000000000000),(64813479/2500000000000),(192341/500000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((23/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(3893079633/2500000000000),(-23097389/10000000000000),(1560101/100000000000000),(-10407/100000000000000),(133/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((23/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(5522760503713/25000000000000),(35987333723/20000000000000),(-185514883/20000000000000),(4830139/100000000000000),(131427/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((23/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((23/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(34057004931063/10000000000000),(2026815298787/50000000000000),(1979736361/100000000000000),(54544211/50000000000000),(2634789/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((23/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(23691829517261/20000000000000),(379878924491/100000000000000),(-2614691047/100000000000000),(30340121/50000000000000),(2823257/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((23/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((23/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(26474215698242187/100000000000000),(272910919189453/25000000000000),(73531/409600),(3013/2048000),(601562501/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((23/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(2209/64),(47/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((23/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(103823/512),(6627/2560),(141/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((23/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(5368422844606637853/100000000000000),(289895794801711933/100000000000000),(6757811846733091/100000000000000),(44371551322937/50000000000000),(721103271249/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((23/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(465686119/25000000000000),(-12573567/12500000000000),(3086961/100000000000000),(-17717/25000000000000),(1011/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((23/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(134033648139/2500000000000),(-9121774007/50000000000000),(-80622007/100000000000000),(2591861/100000000000000),(11027421/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((23/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((23/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((23/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel37

namespace Hf4Quad.Panel38
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(117/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((117/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (117/40) (1/40)

def c3 : Certificate := ⟨(128142857142857/25000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((117/40)+(1/40)*x)) := (SharedCertificates.h2 (117/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((117/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-421142857142857/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((117/40)+(1/40)*x)) := (SharedCertificates.h4 (117/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(13689/1600),(117/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((117/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(1035728571428571/100000000000000),(17704761904761/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((117/40)+(1/40)*x)) := (SharedCertificates.h8 (117/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((117/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((117/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1601613/64000),(41067/64000),(351/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((117/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(312077259/1280000),(8001981/1280000),(68393/1280000),(608912037/4000000000000),(1/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((117/40)+(1/40)*x)) := (SharedCertificates.h13 (117/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((117/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((117/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(187388721/2560000),(1601613/640000),(41067/1280000),(117/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((117/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(20449165982142857/100000000000000),(139823357142857/20000000000000),(1792607142857/20000000000000),(51071428571/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((117/40)+(1/40)*x)) := (SharedCertificates.h18 (117/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((117/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(5352656337158203/25000000000000),(228745997314453/25000000000000),(1601613/10240000),(13689/10240000),(286132813/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((117/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(34871564803930663/25000000000000),(372559453033447/6250000000000),(50948301269531/50000000000000),(217727783203/25000000000000),(1864102291/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((117/40)+(1/40)*x)) := (SharedCertificates.h22 (117/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((117/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(2505043165790039/4000000000000),(80289845057373/2500000000000),(13724759838867/20000000000000),(97754699707/12500000000000),(2515112307/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((117/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(140627026396996369/100000000000000),(7211642379333143/100000000000000),(154094922635321/100000000000000),(1756067494419/100000000000000),(282384567/2500000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((117/40)+(1/40)*x)) := (SharedCertificates.h26 (117/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((117/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(183181281498396601/100000000000000),(2191912770066283/20000000000000),(140507228850401/50000000000000),(2001527476501/50000000000000),(6878020511/20000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((117/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(43469208863508399/100000000000000),(130036094890837/5000000000000),(13337035373419/20000000000000),(474965647201/50000000000000),(8160825927/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((117/40)+(1/40)*x)) := (SharedCertificates.h30 (117/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((117/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((117/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((117/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((117/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((117/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (117/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((117/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((117/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (117/40) (1/40))

def c43 : Certificate := ⟨(24649/1600),(157/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((117/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((117/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(7727542313/25000000000000),(-196880059/50000000000000),(3762039/100000000000000),(-639/2000000000000),(261/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((117/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-518587105814583/50000000000000),(101668867133/100000000000000),(-656338909/100000000000000),(106437/2500000000000),(8709957/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((117/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((117/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (117/40) (1/40))

def c52 : Certificate := ⟨(32833333333333/20000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((117/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (117/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((117/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (117/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((117/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (117/40) (1/40))

def c56 : Certificate := ⟨(10771992818671/50000000000000),(-19339304881/50000000000000),(69440951/100000000000000),(-12467/10000000000000),(227/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((117/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(13824057450627/100000000000000),(154714439047/100000000000000),(-55552761/20000000000000),(249339/50000000000000),(1189/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((117/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((117/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((117/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((117/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((117/40)+(1/40)*x)) := (SharedCertificates.h61 (117/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-205003078172673/100000000000000),(-1211327950959/50000000000000),(1456639273/50000000000000),(-1325927/50000000000000),(8137/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((117/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((117/40)+(1/40)*x)) := (SharedCertificates.h61 (117/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-221876547610923/100000000000000),(-563616170559/20000000000000),(1112652431/100000000000000),(716533/25000000000000),(11991/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((117/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((117/40)+(1/40)*x)) := (SharedCertificates.h67 (117/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-249589090738773/25000000000000),(-11562858905399/100000000000000),(15853594819/100000000000000),(-6517163/25000000000000),(2633/2500000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((117/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((117/40)+(1/40)*x)) := (SharedCertificates.h67 (117/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-1105697378720793/100000000000000),(-1746633554743/12500000000000),(6518736733/100000000000000),(1644431/12500000000000),(15759/6250000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((117/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((117/40)+(1/40)*x)) := (SharedCertificates.h72 (117/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(259734758290279/20000000000000),(3150674398603/25000000000000),(-9362234591/20000000000000),(9756349/10000000000000),(214553/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((117/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((117/40)+(1/40)*x)) := (SharedCertificates.h72 (117/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(3262110886684623/100000000000000),(39992912254419/100000000000000),(-7898182327/20000000000000),(-35104753/50000000000000),(1029503/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((117/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((117/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((117/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(32389790136309/25000000000000),(35220450397/10000000000000),(-39295849/10000000000000),(275749/100000000000000),(503/10000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((117/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11723126914685813/100000000000000),(5411113182611/50000000000000),(-54986237371/100000000000000),(61834837/50000000000000),(192451/20000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((117/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(853014735127/100000000000000),(-98432767/12500000000000),(4727933/100000000000000),(-17057/100000000000000),(119/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((117/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(27826286539601/100000000000000),(315457546469/100000000000000),(-1554881/312500000000),(523249/50000000000000),(10431/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((117/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((117/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((117/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (117/40) (1/40))

def c87 : Certificate := ⟨(16877637130801/100000000000000),(-3560682939/5000000000000),(75119893/25000000000000),(-1267847/100000000000000),(21/390625000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((117/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1082981715893/10000000000000),(94951545039/100000000000000),(-50079929/12500000000000),(1690461/100000000000000),(14063/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((117/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((117/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((117/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((117/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((117/40)+(1/40)*x)) := (SharedCertificates.h61 (117/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-39663634151693/25000000000000),(-726359287577/50000000000000),(5588666509/100000000000000),(-21298381/100000000000000),(48859/20000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((117/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((117/40)+(1/40)*x)) := (SharedCertificates.h61 (117/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-84399718226941/50000000000000),(-409323332463/25000000000000),(2735224157/50000000000000),(-3505667/20000000000000),(313443/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((117/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((117/40)+(1/40)*x)) := (SharedCertificates.h67 (117/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-19409196786459/2500000000000),(-6984201699639/100000000000000),(1387942079/5000000000000),(-6958133/6250000000000),(1109027/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((117/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((117/40)+(1/40)*x)) := (SharedCertificates.h67 (117/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-421083211042359/50000000000000),(-2035039428987/25000000000000),(6882455109/25000000000000),(-89174401/100000000000000),(1551647/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((117/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((117/40)+(1/40)*x)) := (SharedCertificates.h72 (117/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(261481429500493/25000000000000),(207217450061/2500000000000),(-43440865893/100000000000000),(53089289/25000000000000),(7449/400000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((117/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((117/40)+(1/40)*x)) := (SharedCertificates.h72 (117/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1250402644565489/50000000000000),(5930342848409/25000000000000),(-17236740299/20000000000000),(143721697/50000000000000),(1172857/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((117/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((117/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((117/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(61416241857409/50000000000000),(26308655939/12500000000000),(-797897941/100000000000000),(2986243/100000000000000),(3603/10000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((117/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11500644783256727/100000000000000),(1864917383009/25000000000000),(-44017626467/100000000000000),(57415111/25000000000000),(6203571/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((117/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(869516465247/100000000000000),(-281997471/50000000000000),(461727/12500000000000),(-21919/100000000000000),(511/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((117/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(21744913752761/100000000000000),(19215681471/10000000000000),(-12356151/1562500000000),(3313511/100000000000000),(15939/25000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((117/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((117/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-514139705827421/100000000000000),(-2607223385457/50000000000000),(6776611283/50000000000000),(-47751933/100000000000000),(4818111/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((117/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(17094017094017/50000000000000),(-292205420411/100000000000000),(99899289/4000000000000),(-10673001/50000000000000),(184019/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((117/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-175774258402537/100000000000000),(-56074551169/20000000000000),(1757482177/25000000000000),(-19102577/25000000000000),(5873769/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((117/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((117/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((117/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((117/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((117/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((117/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((117/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((117/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((117/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((117/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (117/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((117/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((117/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1445655157/100000000000000),(-12356027/25000000000000),(105607/10000000000000),(-18053/100000000000000),(303/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((117/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(6703995773299/6250000000000),(-310535555001/100000000000000),(1181039387/50000000000000),(-17412033/100000000000000),(690397/1562500000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((117/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((117/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (117/40) (1/40))

def c134 : Certificate := ⟨(46689/1600),(217/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((117/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((117/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(4246284501061/100000000000000),(-1690399881/6250000000000),(172270051/100000000000000),(-548631/50000000000000),(1759/25000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((117/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(123909235668773/100000000000000),(45321733809/12500000000000),(172270043/50000000000000),(-2194539/100000000000000),(9947/2500000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((117/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((117/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (117/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((117/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (117/40) (1/40))

def c140 : Certificate := ⟨(23589955487107/100000000000000),(-4035345657/20000000000000),(-957907/50000000000000),(219/156250000000),(11203/50000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((117/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(5640178051571/100000000000000),(5044182071/6250000000000),(7663251/100000000000000),(-560643/100000000000000),(4013/4000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((117/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((117/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(159058042267/50000000000000),(9104027201/100000000000000),(132001/200000000000),(-50873/100000000000000),(2477/20000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((117/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((117/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3781508387251/100000000000000),(107707876379/100000000000000),(769816993/100000000000000),(-7091/1000000000000),(148077/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((117/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-98676455426733/12500000000000),(-2822460246087/25000000000000),(-942218603/100000000000000),(39529187/50000000000000),(1405141/10000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((117/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-324754815337651/20000000000000),(-372997071573/1562500000000),(-11371029839/100000000000000),(164239249/100000000000000),(14912607/50000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((117/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(519971200193591/25000000000000),(1136610035603/4000000000000),(-17081631621/100000000000000),(-104243579/50000000000000),(38991899/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((117/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3019748080090393/50000000000000),(8802354035629/10000000000000),(15087718879/50000000000000),(-155925863/25000000000000),(110016069/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((117/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(660346362785353/10000000000000),(1305252617991/1250000000000),(154458118393/100000000000000),(-664552887/100000000000000),(132213541/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((117/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(27899618046919/25000000000000),(170517853473/100000000000000),(40663501/50000000000000),(-1172159/100000000000000),(42607/20000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((117/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((117/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((117/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((117/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(14619342225285273/25000000000000),(86150617078753/100000000000000),(1815453189/12500000000000),(-317054223/50000000000000),(29010191/25000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((117/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(17100632583/10000000000000),(-125965829/50000000000000),(328681/100000000000000),(179/12500000000000),(347/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((117/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(1411542565939/12500000000000),(161928948183/100000000000000),(11384959/50000000000000),(-543893/50000000000000),(31673/12500000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((117/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((117/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((117/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (117/40) (1/40))

def c175 : Certificate := ⟨(21198670019749/100000000000000),(-12220106627/25000000000000),(16565129/25000000000000),(10007/4000000000000),(55299/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((117/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(5068439973667/100000000000000),(65173902009/100000000000000),(-22086839/25000000000000),(-1303/390625000000),(100173/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((117/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((117/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(128445418833/50000000000000),(6606600203/100000000000000),(33520709/100000000000000),(-148973/100000000000000),(5323/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((117/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((117/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1528324668091/50000000000000),(78274647739/100000000000000),(97673227/25000000000000),(-1802881/100000000000000),(127513/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((117/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-709426671876571/100000000000000),(-4559193420041/50000000000000),(194324157/1562500000000),(23391711/50000000000000),(14029567/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((117/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-181890007206001/12500000000000),(-19173213570031/100000000000000),(20051559891/100000000000000),(3571813/3125000000000),(29538481/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((117/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1877597503195117/100000000000000),(72411909163/312500000000),(-4420780211/10000000000000),(-5485583/6250000000000),(7753103/20000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((117/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(338564179671679/6250000000000),(70830749994213/100000000000000),(-40781102057/50000000000000),(-410241633/100000000000000),(109171527/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((117/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(2935489741679129/50000000000000),(82673600776457/100000000000000),(-9138929681/50000000000000),(-65943977/10000000000000),(32062509/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((117/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(22078754157/20000000000),(136954404221/100000000000000),(-143174003/100000000000000),(-816109/100000000000000),(13187/6250000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((117/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((117/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((117/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((117/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(7233424793142161/12500000000000),(17373214054927/25000000000000),(-1399330121/1562500000000),(-387474381/100000000000000),(11440751/10000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((117/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(1382470999/800000000000),(-12970367/6250000000000),(516661/100000000000000),(43/20000000000000),(69/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((117/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(10145573589333/100000000000000),(127620623/97656250000),(-172821813/100000000000000),(-1059/160000000000),(60973/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((117/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((117/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(5748787425107/25000000000000),(49459058441/20000000000000),(-56323689/10000000000000),(1768169/100000000000000),(5092911/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((117/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7861589641171/100000000000000),(4338081297/25000000000000),(-340870093/100000000000000),(3517921/100000000000000),(3627313/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((117/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((117/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((117/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((117/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((117/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((117/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (117/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((117/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((117/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((117/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (117/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((117/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(17643300541/50000000000000),(-13789/156250000000),(1473033/100000000000000),(-737/100000000000000),(1/1562500000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((117/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(393859116920729/100000000000000),(-1917967089791/100000000000000),(-266776001/2500000000000),(-77284951/100000000000000),(1831083/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((117/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((117/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((117/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((117/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (117/40) (1/40))

def c223 : Certificate := ⟨(38809/1600),(197/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((117/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(5104508961/2560000),(22211553/640000),(273107/1280000),(337/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((117/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((117/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(14424745651/20000000000000),(-918773609/100000000000000),(8778091/100000000000000),(-74549/100000000000000),(19/3125000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((117/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(143811022335303/100000000000000),(167776555713/25000000000000),(1005187277/100000000000000),(-1027369/50000000000000),(2471533/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((117/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((117/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (117/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((117/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (117/40) (1/40))

def c231 : Certificate := ⟨(11266056380687/50000000000000),(-8517950393/25000000000000),(488507/100000000000000),(45187/25000000000000),(25259/20000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((117/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(9871548954501/100000000000000),(34071801571/25000000000000),(-195403/10000000000000),(-180749/25000000000000),(615833/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((117/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((117/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(974474787611/100000000000000),(13453658287/50000000000000),(185356239/100000000000000),(-37017/25000000000000),(25047/20000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((117/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((117/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(2300261187983/20000000000000),(39364911513/12500000000000),(2114375427/100000000000000),(-89507/4000000000000),(1491577/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((117/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-11047051972671/800000000000),(-9516723329561/50000000000000),(911255771/100000000000000),(51895431/50000000000000),(21575601/25000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((117/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-725087025049801/25000000000000),(-41921278577991/100000000000000),(-12638043207/50000000000000),(7008819/3125000000000),(189970449/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((117/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(175711853246039/5000000000000),(2773718217743/6250000000000),(-12064821707/20000000000000),(-268872849/100000000000000),(239114097/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((117/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(10712036034466923/100000000000000),(152271965343767/100000000000000),(26204122227/50000000000000),(-44708837/5000000000000),(693156883/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((117/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(12480014164558429/100000000000000),(101181519549501/50000000000000),(422931061761/100000000000000),(-953678589/100000000000000),(461909637/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((117/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(120717572696613/100000000000000),(149740864571/50000000000000),(181448179/100000000000000),(-79703/5000000000000),(1356901/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((117/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((117/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((117/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((117/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(12601234307605263/20000000000000),(73038417140863/50000000000000),(-290948537/25000000000000),(-482961113/50000000000000),(378116839/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((117/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(1587146109/1000000000000),(-367972333/100000000000000),(428029/50000000000000),(441/100000000000000),(1923/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((117/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(19807605921543/100000000000000),(275256710831/100000000000000),(2090597/6250000000000),(-256503/20000000000000),(344313/20000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((117/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((117/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((117/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (117/40) (1/40))

def c259 : Certificate := ⟨(1176065319987/6250000000000),(-35643913203/50000000000000),(163296479/100000000000000),(2067/50000000000000),(133159/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((117/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(2060984960069/25000000000000),(47525217603/50000000000000),(-217728639/100000000000000),(-2757/50000000000000),(294221/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((117/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((117/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(6796254409/1000000000000),(979487587/6250000000000),(6805877/12500000000000),(-207407/50000000000000),(9861/10000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((117/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((117/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(321737978633/4000000000000),(46046423767/25000000000000),(617554281/100000000000000),(-61807/1250000000000),(73529/6250000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((117/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-230697696100719/20000000000000),(-6642115718611/50000000000000),(1227619067/4000000000000),(137463/25000000000000),(20609953/25000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((117/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2403396051674511/100000000000000),(-14402830863189/50000000000000),(6672359791/12500000000000),(2987393/5000000000000),(89285061/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((117/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(743945578470661/25000000000000),(31935257724153/100000000000000),(-101572028721/100000000000000),(58195121/50000000000000),(22752671/10000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((117/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(4450729268011929/50000000000000),(26316043610261/25000000000000),(-213113136773/100000000000000),(-162435501/100000000000000),(654867569/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((117/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(10123798605523639/100000000000000),(13408053755121/10000000000000),(-25601711431/25000000000000),(-22426599/2500000000000),(52105949/6250000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((117/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(29291876280363/25000000000000),(51443167951/25000000000000),(-190505131/50000000000000),(-212921/50000000000000),(637747/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((117/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((117/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((117/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((117/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(30631052817090621/50000000000000),(50903009463611/50000000000000),(-11473404947/5000000000000),(-1344367/1562500000000),(175945347/25000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((117/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(40808261063/25000000000000),(-27126241/10000000000000),(212441/20000000000000),(-319/12500000000000),(1891/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((117/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(16525384657737/100000000000000),(191401683113/100000000000000),(-84667283/20000000000000),(-20663/100000000000000),(1559201/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((117/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((117/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(143100795846443/100000000000000),(71320114211/6250000000000),(-7181533673/50000000000000),(-37766011/50000000000000),(13953213/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((117/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(4892334900733/10000000000000),(-5604232329/20000000000000),(-1167738317/25000000000000),(14099763/100000000000000),(5459701/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((117/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((117/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((117/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((117/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((117/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((117/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (117/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((117/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(219515806421566513/20000000000000),(34312211832807/12500000000000),(-45749615777077/100000000000000),0,(7087/5000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((117/40)+(1/40)*x)) := (SharedCertificates.h297 (117/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4555480611/50000000000000),(-455719/20000000000000),(76067/20000000000000),(-191/100000000000000),(19/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((117/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(677885410258309/100000000000000),(422417644931/25000000000000),(12173731581/100000000000000),(67317419/100000000000000),(105529/5000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((117/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((117/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (117/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((117/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (117/40) (1/40))

def c307 : Certificate := ⟨(1854024647072407/50000000000000),(11091229182759/50000000000000),0,0,(11/1000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((117/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (117/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((117/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (117/40) (1/40))

def c311 : Certificate := ⟨(2216950705854927/100000000000000),(2817541634481/100000000000000),0,0,(1099/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((117/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (117/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4510700203477/100000000000000),(-716585939/12500000000000),(7285721/100000000000000),(-463/5000000000000),(17/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((117/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(167258987056017/100000000000000),(157602663161/20000000000000),(-200298579/20000000000000),(636393/50000000000000),(2741/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((117/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((117/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (117/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((117/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (117/40) (1/40))

def c316 : Certificate := ⟨(2675175940169/12500000000000),(-3609260511/10000000000000),(21347823/20000000000000),(-157833/50000000000000),(989/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((117/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(14394369914591/100000000000000),(72185210219/50000000000000),(-426956463/100000000000000),(1262663/100000000000000),(1321/25000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((117/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((117/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(103598942619/5000000000000),(4156242473/10000000000000),(85512797/100000000000000),(-869293/100000000000000),(3509/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((117/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((117/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(3033406203429/12500000000000),(120200287319/25000000000000),(899220707/100000000000000),(-5062793/50000000000000),(84643/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((117/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-2011718670363271/100000000000000),(-1256725989689/6250000000000),(7561733253/12500000000000),(-44669631/25000000000000),(381627/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((117/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-4319997803138461/100000000000000),(-11555602257343/25000000000000),(2156304677/2000000000000),(-231480501/100000000000000),(2469519/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((117/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(245999797651579/5000000000000),(42692388338203/100000000000000),(-197145891101/100000000000000),(15025219/2000000000000),(3548069/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((117/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(7911145413791411/50000000000000),(82418630302799/50000000000000),(-436053255149/100000000000000),(205832027/20000000000000),(1759479/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((117/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2458640818961237/12500000000000),(48945785427721/20000000000000),(-58248654377/25000000000000),(-80623463/12500000000000),(20673529/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((117/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(65430359340781/50000000000000),(165151632803/50000000000000),(-768400129/100000000000000),(1656033/100000000000000),(8793/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((117/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((117/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((117/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((117/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(33923892143208199/50000000000000),(154120913465849/100000000000000),(-238444053807/50000000000000),(1228569167/100000000000000),(807349/6250000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((117/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(73694374143/50000000000000),(-33480369/10000000000000),(898247/50000000000000),(-569/6250000000000),(71/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((117/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(1159603176933/4000000000000),(294849940917/100000000000000),(-809414651/100000000000000),(1217649/50000000000000),(68997/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((117/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((117/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((117/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (117/40) (1/40))

def c344 : Certificate := ⟨(8308726193663/50000000000000),(-1020008341/1562500000000),(339415737/100000000000000),(-1764737/100000000000000),(9319/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((117/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(11176730150231/100000000000000),(21760177941/25000000000000),(-226277159/50000000000000),(2352981/100000000000000),(39/156250000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((117/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((117/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(124919296851/10000000000000),(19456610949/100000000000000),(-5080139/20000000000000),(-261841/100000000000000),(11791/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((117/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((117/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((117/40)+(1/40)*x)) := (SharedCertificates.h144 (117/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(14711077767827/100000000000000),(226955492681/100000000000000),(-160847099/50000000000000),(-2922027/100000000000000),(35051/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((117/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((117/40)+(1/40)*x)) := (SharedCertificates.h148 (117/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-39077450089201/2500000000000),(-2429505763437/20000000000000),(31726308843/50000000000000),(-330704881/100000000000000),(3510839/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((117/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((117/40)+(1/40)*x)) := (SharedCertificates.h151 (117/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-413023460988391/12500000000000),(-27089627437613/100000000000000),(130307708857/100000000000000),(-124474459/20000000000000),(8641299/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((117/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((117/40)+(1/40)*x)) := (SharedCertificates.h154 (117/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1966870483152199/50000000000000),(13803475495081/50000000000000),(-84147515963/50000000000000),(49730297/5000000000000),(2884947/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((117/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((117/40)+(1/40)*x)) := (SharedCertificates.h157 (117/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(12175230270355481/100000000000000),(979022579031/1000000000000),(-487764943439/100000000000000),(2402933007/100000000000000),(15391037/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((117/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((117/40)+(1/40)*x)) := (SharedCertificates.h160 (117/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(7228575961358147/50000000000000),(1050563311549/781250000000),(-261991896649/50000000000000),(1845500487/100000000000000),(26259821/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((117/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((117/40)+(1/40)*x)) := (SharedCertificates.h41 (117/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(30900663317243/25000000000000),(193538034477/100000000000000),(-930509331/100000000000000),(4444121/100000000000000),(61711/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((117/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((117/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((117/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((117/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((117/40)+(1/40)*x)) := (SharedCertificates.h167 (117/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(16101255433837261/25000000000000),(11658813071367/12500000000000),(-486827786751/100000000000000),(2490138219/100000000000000),(295559/800000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((117/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(155267395779/100000000000000),(-224856199/100000000000000),(374819/25000000000000),(-79/800000000000),(127/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((117/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4489448658843/20000000000000),(176283531443/100000000000000),(-899192243/100000000000000),(2316067/50000000000000),(31391/25000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((117/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((117/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(174343053064843/50000000000000),(4062866380927/100000000000000),(132002421/5000000000000),(3469377/3125000000000),(529337/20000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((117/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(119208925172541/100000000000000),(185067222497/50000000000000),(-565240403/25000000000000),(11456007/20000000000000),(2689747/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((117/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((117/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1795656078918457/6250000000000),(291309005126953/25000000000000),(1930149/10240000),(15561/10240000),(305664063/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((117/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(56169/1600),(237/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((117/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(13312053/64000),(168507/64000),(711/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((117/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(1195193444616734113/20000000000000),(318015211949282487/100000000000000),(7307784041631041/100000000000000),(47315301284729/50000000000000),(379236659553/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((117/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(334673857/20000000000000),(-178099/200000000000),(269253/10000000000000),(-7611/12500000000000),(171/10000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((117/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2662278266171/50000000000000),(-1853604683/10000000000000),(-16478011/25000000000000),(1807/78125000000),(2060257/20000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((117/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((117/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((117/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel38

namespace Hf4Quad.Panel39
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(119/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((119/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (119/40) (1/40)

def c3 : Certificate := ⟨(521333333333333/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((119/40)+(1/40)*x)) := (SharedCertificates.h2 (119/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((119/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-214952380952381/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((119/40)+(1/40)*x)) := (SharedCertificates.h4 (119/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(14161/1600),(119/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((119/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(53572037037037/5000000000000),(18007407407407/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((119/40)+(1/40)*x)) := (SharedCertificates.h8 (119/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((119/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((119/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1685159/64000),(42483/64000),(357/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((119/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(25652839985532407/100000000000000),(646710251736111/100000000000000),(1086907986111/20000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((119/40)+(1/40)*x)) := (SharedCertificates.h13 (119/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((119/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((119/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(200533921/2560000),(1685159/640000),(42483/1280000),(119/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((119/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(2735457751736111/12500000000000),(735585277777777/100000000000000),(9272083333333/100000000000000),(12986111111/25000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((119/40)+(1/40)*x)) := (SharedCertificates.h18 (119/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((119/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(23304234959960937/100000000000000),(244792384033203/25000000000000),(1685159/10240000),(14161/10240000),(582031251/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((119/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(30364555033015769/20000000000000),(6379108200213393/100000000000000),(53605951262297/50000000000000),(900940357349/100000000000000),(3791825819/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((119/40)+(1/40)*x)) := (SharedCertificates.h22 (119/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((119/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(69330099005883787/100000000000000),(3495635243994139/100000000000000),(1835942880249/2500000000000),(102853942871/12500000000000),(2601684573/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((119/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(19460115091334047/12500000000000),(1962364547025281/25000000000000),(32980916756727/20000000000000),(1847670406537/100000000000000),(5842089593/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((119/40)+(1/40)*x)) := (SharedCertificates.h26 (119/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((119/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(103128522271252133/50000000000000),(6066383663014829/50000000000000),(76467020962371/25000000000000),(2141933360289/50000000000000),(18090448007/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((119/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(6118140507758807/12500000000000),(359890618103459/12500000000000),(72582981802377/100000000000000),(1016568372581/100000000000000),(8585784057/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((119/40)+(1/40)*x)) := (SharedCertificates.h30 (119/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((119/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((119/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((119/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((119/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((119/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (119/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((119/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((119/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (119/40) (1/40))

def c43 : Certificate := ⟨(25281/1600),(159/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((119/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((119/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(30137445587/100000000000000),(-189543683/50000000000000),(715259/20000000000000),(-2999/10000000000000),(121/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((119/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-518486732917891/50000000000000),(99093441767/100000000000000),(-315771341/50000000000000),(4028379/100000000000000),(8279021/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((119/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((119/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (119/40) (1/40))

def c52 : Certificate := ⟨(165833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((119/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (119/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((119/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (119/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((119/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (119/40) (1/40))

def c56 : Certificate := ⟨(4293381037567/20000000000000),(-19201167431/50000000000000),(68698273/100000000000000),(-24579/20000000000000),(111/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((119/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(14132379248657/100000000000000),(153609339447/100000000000000),(-54958619/20000000000000),(491579/100000000000000),(1177/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((119/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((119/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((119/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((119/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((119/40)+(1/40)*x)) := (SharedCertificates.h61 (119/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-209836758074871/100000000000000),(-2411034605203/100000000000000),(362171401/12500000000000),(-1325237/50000000000000),(32107/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((119/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((119/40)+(1/40)*x)) := (SharedCertificates.h61 (119/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-113754117967713/50000000000000),(-1406798082239/50000000000000),(35300419/3125000000000),(1393897/50000000000000),(47473/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((119/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((119/40)+(1/40)*x)) := (SharedCertificates.h67 (119/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-510709437065157/50000000000000),(-2874938935047/25000000000000),(784919417/5000000000000),(-6417043/25000000000000),(5227/5000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((119/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((119/40)+(1/40)*x)) := (SharedCertificates.h67 (119/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-1133617336415449/100000000000000),(-6973418820351/50000000000000),(1649040533/25000000000000),(12655591/100000000000000),(24873/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((119/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((119/40)+(1/40)*x)) := (SharedCertificates.h72 (119/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(1323692719898229/100000000000000),(1552077318879/12500000000000),(-46229623337/100000000000000),(48144487/50000000000000),(213191/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((119/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((119/40)+(1/40)*x)) := (SharedCertificates.h72 (119/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(3341938192743731/100000000000000),(39834119817539/100000000000000),(-9975475563/25000000000000),(-66804633/100000000000000),(1012489/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((119/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((119/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((119/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(16282749991199/12500000000000),(175317993859/50000000000000),(-12228047/3125000000000),(55577/20000000000000),(4961/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((119/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5872276204339479/50000000000000),(10603759163457/100000000000000),(-27124466257/50000000000000),(122100887/100000000000000),(948499/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((119/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(425729293549/50000000000000),(-384376581/50000000000000),(4627029/100000000000000),(-16581/100000000000000),(29/25000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((119/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(3556902464703/12500000000000),(78369944563/25000000000000),(-24567089/5000000000000),(513471/50000000000000),(4099/20000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((119/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((119/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((119/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (119/40) (1/40))

def c87 : Certificate := ⟨(418410041841/2500000000000),(-35013392623/50000000000000),(292999101/100000000000000),(-612969/50000000000000),(2577/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((119/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(2754532775453/25000000000000),(93369046993/100000000000000),(-390665469/100000000000000),(1634583/100000000000000),(2731/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((119/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((119/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((119/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((119/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((119/40)+(1/40)*x)) := (SharedCertificates.h61 (119/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-40384447050993/25000000000000),(-1430616945977/100000000000000),(682847279/12500000000000),(-20668241/100000000000000),(236929/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((119/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((119/40)+(1/40)*x)) := (SharedCertificates.h61 (119/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-3441045614173/2000000000000),(-323124040391/20000000000000),(2683265791/50000000000000),(-3422483/20000000000000),(303949/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((119/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((119/40)+(1/40)*x)) := (SharedCertificates.h67 (119/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-790226122978977/100000000000000),(-6874488016297/100000000000000),(27101533979/100000000000000),(-107796267/100000000000000),(1076849/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((119/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((119/40)+(1/40)*x)) := (SharedCertificates.h67 (119/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-85833732735743/10000000000000),(-50194374949/625000000000),(27001162017/100000000000000),(-10881769/12500000000000),(1504119/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((119/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((119/40)+(1/40)*x)) := (SharedCertificates.h72 (119/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(1062331033666229/100000000000000),(8117451425707/100000000000000),(-8438036959/20000000000000),(2045947/1000000000000),(1803631/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((119/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((119/40)+(1/40)*x)) := (SharedCertificates.h72 (119/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(2547905583429679/100000000000000),(292250743413/1250000000000),(-42239417597/50000000000000),(280867513/100000000000000),(2270399/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((119/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((119/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((119/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(123250254333391/100000000000000),(103656570999/50000000000000),(-12191269/1562500000000),(579969/20000000000000),(17469/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((119/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11515389871400231/100000000000000),(7286319635053/100000000000000),(-42666050359/100000000000000),(220931887/100000000000000),(6000543/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((119/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(173680615449/20000000000000),(-274739391/50000000000000),(3565229/100000000000000),(-20953/100000000000000),(123/25000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((119/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(110630452459/500000000000),(189032955359/100000000000000),(-385623301/50000000000000),(640589/20000000000000),(7699/12500000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((119/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((119/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-524514765543813/100000000000000),(-1032160189763/20000000000000),(829451319/6250000000000),(-11562481/25000000000000),(9342481/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((119/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(33613445378151/100000000000000),(-70616481887/25000000000000),(296707907/12500000000000),(-19946751/100000000000000),(169043/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((119/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-176307484216407/100000000000000),(-126573755193/50000000000000),(6588204663/100000000000000),(-70909253/100000000000000),(5541169/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((119/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((119/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((119/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((119/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((119/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((119/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((119/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((119/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((119/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((119/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (119/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((119/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((119/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1350891009/100000000000000),(-22704051/50000000000000),(953951/100000000000000),(-16033/100000000000000),(53/20000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((119/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(2133043455091/2000000000000),(-150645848019/50000000000000),(2260725973/100000000000000),(-2054683/12500000000000),(41074467/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((119/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((119/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (119/40) (1/40))

def c134 : Certificate := ⟨(47561/1600),(219/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((119/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((119/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(20964360587/500000000000),(-2637026489/10000000000000),(82925361/50000000000000),(-1043087/100000000000000),(1321/20000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((119/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(31158936058697/25000000000000),(363926136867/100000000000000),(331701427/100000000000000),(-1043097/50000000000000),(380693/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((119/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((119/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (119/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((119/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (119/40) (1/40))

def c140 : Certificate := ⟨(23549595472751/100000000000000),(-10091370571/50000000000000),(-1098371/100000000000000),(132403/100000000000000),(5341/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((119/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(2900809054497/50000000000000),(20182741141/25000000000000),(2196741/50000000000000),(-33101/6250000000000),(95971/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((119/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((119/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(168293863413/50000000000000),(9367404519/100000000000000),(1026323/1562500000000),(-54359/100000000000000),(12147/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((119/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((119/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3999997652887/100000000000000),(110778471117/100000000000000),(191360037/25000000000000),(-149863/20000000000000),(145223/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((119/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-811994470670971/100000000000000),(-176448107163/1562500000000),(-481071299/100000000000000),(74704397/100000000000000),(2688383/20000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((119/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-835780944386399/50000000000000),(-23915359147941/100000000000000),(-10410448279/100000000000000),(156042481/100000000000000),(7143201/25000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((119/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(427329066944121/20000000000000),(28344475513891/100000000000000),(-18293023773/100000000000000),(-39090297/20000000000000),(18650289/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((119/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3107829508553913/50000000000000),(688569417223/781250000000),(26528506331/100000000000000),(-59227499/10000000000000),(26337571/25000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((119/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(212903644146981/3125000000000),(105030166757907/100000000000000),(75272502261/50000000000000),(-640080121/100000000000000),(12715127/10000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((119/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(55969911972407/50000000000000),(170829333647/100000000000000),(18617909/25000000000000),(-1113591/100000000000000),(204089/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((119/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((119/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((119/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((119/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(29324861611373127/50000000000000),(86201233454917/100000000000000),(10816832259/100000000000000),(-601830233/100000000000000),(2225461/2000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((119/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(10656486777/6250000000000),(-250600277/100000000000000),(84219/25000000000000),(13/1000000000000),(83/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((119/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2904070231843/25000000000000),(32401445083/20000000000000),(1026883/6250000000000),(-513119/50000000000000),(243563/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((119/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((119/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((119/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (119/40) (1/40))

def c175 : Certificate := ⟨(10550588079163/50000000000000),(-4861248569/10000000000000),(67684537/100000000000000),(112407/50000000000000),(13099/25000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((119/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(5198431788897/100000000000000),(12963329517/20000000000000),(-1804921/2000000000000),(-149877/50000000000000),(3827/4000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((119/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((119/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(135118465319/50000000000000),(269555937/4000000000000),(32629219/100000000000000),(-74077/50000000000000),(519/5000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((119/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((119/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(40184337533/1250000000000),(39907914993/50000000000000),(11872191/3125000000000),(-22387/1250000000000),(62159/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((119/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-727613334015463/100000000000000),(-4534048899593/50000000000000),(12703029131/100000000000000),(10509259/25000000000000),(13399789/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((119/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-746692691873437/50000000000000),(-4772918693233/25000000000000),(5177064401/25000000000000),(52357357/50000000000000),(28242153/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((119/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(961881809102953/50000000000000),(11496989644263/50000000000000),(-1117377171/2500000000000),(-18708351/25000000000000),(4627177/12500000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((119/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(55583589178139/1000000000000),(35249862688949/50000000000000),(-41956995129/50000000000000),(-374119437/100000000000000),(104347003/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((119/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1509062093047777/25000000000000),(82592724057047/100000000000000),(-22124057233/100000000000000),(-6229881/1000000000000),(30742841/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((119/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(6916693781777/6250000000000),(27274438719/20000000000000),(-147862881/100000000000000),(-373831/50000000000000),(20173/10000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((119/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((119/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((119/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((119/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(29003011401800091/50000000000000),(69130126107513/100000000000000),(-91771579961/100000000000000),(-87779317/25000000000000),(109458499/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((119/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(34479178253/20000000000000),(-205457109/100000000000000),(258803/50000000000000),(101/100000000000000),(33/10000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((119/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(10406244180207/100000000000000),(1624807017/1250000000000),(-35317921/20000000000000),(-594949/100000000000000),(233697/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((119/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((119/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(23487501522649/100000000000000),(245063545453/100000000000000),(-69086453/12500000000000),(346941/20000000000000),(9722837/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((119/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(246717452969/3125000000000),(8015055979/50000000000000),(-320485521/100000000000000),(3276249/100000000000000),(3403051/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((119/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((119/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((119/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((119/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((119/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((119/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (119/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((119/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((119/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((119/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (119/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((119/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(35274838391/100000000000000),(-2939693/100000000000000),(1470091/100000000000000),(-123/50000000000000),(1/1562500000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((119/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(389979873493/100000000000),(-490398102151/25000000000000),(-5572578961/50000000000000),(-20204653/25000000000000),(1846349/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((119/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((119/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((119/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((119/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (119/40) (1/40))

def c223 : Certificate := ⟨(39601/1600),(199/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((119/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(5284397041/2560000),(22761819/640000),(277163/1280000),(339/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((119/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((119/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(70320706371/100000000000000),(-221134297/25000000000000),(834469/10000000000000),(-69977/100000000000000),(563/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((119/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(72578619661707/50000000000000),(67510275881/10000000000000),(248295853/25000000000000),(-1950017/100000000000000),(592817/25000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((119/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((119/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (119/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((119/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (119/40) (1/40))

def c231 : Certificate := ⟨(22463972539677/100000000000000),(-17033857361/50000000000000),(1546337/100000000000000),(86033/50000000000000),(120443/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((119/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(10144109841287/100000000000000),(34067714721/25000000000000),(-123707/2000000000000),(-688267/100000000000000),(295269/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((119/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((119/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(12862870559/1250000000000),(27646931213/100000000000000),(46110643/25000000000000),(-31299/20000000000000),(61649/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((119/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((119/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(303489598543/2500000000000),(64669913869/20000000000000),(1050334313/50000000000000),(-291411/12500000000000),(293643/20000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((119/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-1418943925050857/100000000000000),(-4757144148243/25000000000000),(379730873/25000000000000),(98879937/100000000000000),(2069051/2500000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((119/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-2984289985903789/100000000000000),(-21009863636047/50000000000000),(-11978329421/50000000000000),(107879103/50000000000000),(182616321/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((119/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1801376317371443/50000000000000),(44135035785469/100000000000000),(-61887604011/100000000000000),(-1578769/625000000000),(9173623/4000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((119/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(11016782517929529/100000000000000),(152471010295599/100000000000000),(11786946361/25000000000000),(-430082957/50000000000000),(133164647/20000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((119/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(128864243725403/1000000000000),(204043383666341/100000000000000),(417255086229/100000000000000),(-187841361/20000000000000),(893330781/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((119/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(60658624663647/50000000000000),(300188648981/100000000000000),(2688623/1562500000000),(-1533029/100000000000000),(652187/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((119/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((119/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((119/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((119/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(1582457822550307/2500000000000),(73030369908701/50000000000000),(-1711853441/25000000000000),(-46472987/5000000000000),(14562001/2000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((119/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(1579820937/1000000000000),(-364543389/100000000000000),(858273/100000000000000),(299/100000000000000),(917/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((119/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(10179121513403/50000000000000),(275375401443/100000000000000),(6490589/25000000000000),(-48603/4000000000000),(831139/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((119/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((119/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((119/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (119/40) (1/40))

def c259 : Certificate := ⟨(18675122633751/100000000000000),(-35317346523/50000000000000),(163245899/100000000000000),(-20381/100000000000000),(125801/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((119/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(8433169821663/100000000000000),(94179590727/100000000000000),(-544153/250000000000),(27173/100000000000000),(562701/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((119/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((119/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(71118353241/10000000000000),(7942324823/50000000000000),(2079459/4000000000000),(-202701/50000000000000),(96497/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((119/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((119/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1051781469857/12500000000000),(186597057311/100000000000000),(588245229/100000000000000),(-2412803/50000000000000),(1151039/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((119/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-589967093446387/50000000000000),(-6580741073593/50000000000000),(15339798751/50000000000000),(-1015257/25000000000000),(7883579/10000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((119/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2460793403830167/100000000000000),(-1786967045759/6250000000000),(6713153431/12500000000000),(24634911/50000000000000),(42766747/25000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((119/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(121569899785399/4000000000000),(15765204911757/50000000000000),(-25210412129/25000000000000),(126759847/100000000000000),(217620373/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((119/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(1822226643053871/20000000000000),(104409934120861/100000000000000),(-26746057389/12500000000000),(-123554343/100000000000000),(627021389/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((119/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1298942873273671/12500000000000),(33415090079753/25000000000000),(-107630013557/100000000000000),(-422452489/50000000000000),(160449121/20000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((119/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(14697190396967/12500000000000),(2042438311/1000000000000),(-15333437/4000000000000),(-21941/6250000000000),(1221899/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((119/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((119/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((119/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((119/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(61464799192729363/100000000000000),(12610909200291/12500000000000),(-22986646611/10000000000000),(-9527027/20000000000000),(674964297/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((119/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(162694747747/100000000000000),(-133522193/50000000000000),(1046769/100000000000000),(-2591/100000000000000),(901/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((119/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(16906494648401/100000000000000),(37941670779/20000000000000),(-423265417/100000000000000),(21337/50000000000000),(149937/10000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((119/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((119/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(14532497684327/10000000000000),(54137538769/5000000000000),(-14825663477/100000000000000),(-3149193/4000000000000),(13397849/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((119/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(48848731712023/100000000000000),(-5817962917/12500000000000),(-4592292739/100000000000000),(12126887/100000000000000),(5135767/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((119/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((119/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((119/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((119/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((119/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((119/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (119/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((119/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1097945029034049173/100000000000000),(11437403944269/12500000000000),(-45749615777077/100000000000000),0,(35441/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((119/40)+(1/40)*x)) := (SharedCertificates.h297 (119/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(2276981027/25000000000000),(-379513/50000000000000),(15183/4000000000000),(-1/1562500000000),(19/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((119/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(340656996779757/50000000000000),(1739190200909/100000000000000),(12590014949/100000000000000),(71364531/100000000000000),(130637/6250000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((119/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((119/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (119/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((119/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (119/40) (1/40))

def c307 : Certificate := ⟨(938103552718963/25000000000000),(11091229182759/50000000000000),0,0,(551/50000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((119/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (119/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((119/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (119/40) (1/40))

def c311 : Certificate := ⟨(2222585789123889/100000000000000),(2817541634481/100000000000000),0,0,(551/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((119/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (119/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2249631948727/50000000000000),(-5703655363/100000000000000),(1446089/20000000000000),(-4583/50000000000000),(1/6250000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((119/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(16883101787287/10000000000000),(392011283213/50000000000000),(-993894731/100000000000000),(157493/12500000000000),(269/10000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((119/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((119/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (119/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((119/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (119/40) (1/40))

def c316 : Certificate := ⟨(213296467571/1000000000000),(-17834703501/50000000000000),(104867301/100000000000000),(-77077/25000000000000),(961/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((119/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(14681412971599/100000000000000),(28535525601/20000000000000),(-83893841/20000000000000),(1233229/100000000000000),(129/2500000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((119/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((119/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1077719434213/50000000000000),(4189418357/10000000000000),(40200521/50000000000000),(-834867/100000000000000),(3411/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((119/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((119/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(3154046082233/12500000000000),(60534778567/12500000000000),(167948007/20000000000000),(-9704389/100000000000000),(41071/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((119/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-2051693347778683/100000000000000),(-19867768088947/100000000000000),(2377363563/4000000000000),(-87299453/50000000000000),(2979/400000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((119/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-2206006602672967/50000000000000),(-1831756493013/4000000000000),(106436502991/100000000000000),(-228101467/100000000000000),(2407007/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((119/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(156393691094603/3125000000000),(41912737608937/100000000000000),(-12043743283/6250000000000),(365423429/50000000000000),(3457071/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((119/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(8075114668507483/50000000000000),(10194083336439/6250000000000),(-429926380343/100000000000000),(1013156587/100000000000000),(856431/10000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((119/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(10078823674916977/50000000000000),(243789372821421/100000000000000),(-47348407113/20000000000000),(-18889073/3125000000000),(1261299/6250000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((119/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(16439783101453/12500000000000),(16362471979/5000000000000),(-94817171/12500000000000),(1631591/100000000000000),(8571/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((119/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((119/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((119/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((119/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(4259633021841963/6250000000000),(38057005958553/25000000000000),(-469576697211/100000000000000),(1208599577/100000000000000),(12558533/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((119/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(36681563693/25000000000000),(-32772553/10000000000000),(348587/20000000000000),(-8753/100000000000000),(33/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((119/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(14788280503279/50000000000000),(14582062983/5000000000000),(-397494023/50000000000000),(593417/25000000000000),(66639/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((119/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((119/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((119/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (119/40) (1/40))

def c344 : Certificate := ⟨(8244117505003/50000000000000),(-12788751579/20000000000000),(82260941/25000000000000),(-423301/25000000000000),(177/2000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((119/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(5674509993329/50000000000000),(42629171929/50000000000000),(-438725019/100000000000000),(2257603/100000000000000),(23981/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((119/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((119/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(51520101863/4000000000000),(19351972969/100000000000000),(-26892129/100000000000000),(-58917/25000000000000),(11281/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((119/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((119/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((119/40)+(1/40)*x)) := (SharedCertificates.h144 (119/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(15163679226021/100000000000000),(225634897787/100000000000000),(-338298327/100000000000000),(-2617021/100000000000000),(134169/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((119/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((119/40)+(1/40)*x)) := (SharedCertificates.h148 (119/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1587141869146047/100000000000000),(-5948816244349/50000000000000),(61508954837/100000000000000),(-63459487/20000000000000),(3373453/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((119/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((119/40)+(1/40)*x)) := (SharedCertificates.h151 (119/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-3357850644210243/100000000000000),(-26575771841633/100000000000000),(63321566473/50000000000000),(-299665473/50000000000000),(2073919/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((119/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((119/40)+(1/40)*x)) := (SharedCertificates.h154 (119/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(797657910825957/20000000000000),(5389104975787/20000000000000),(-162462709909/100000000000000),(949920427/100000000000000),(1381813/12500000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((119/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((119/40)+(1/40)*x)) := (SharedCertificates.h157 (119/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(6184551382307441/50000000000000),(11997457959629/12500000000000),(-473623511217/100000000000000),(1155799889/50000000000000),(7386467/25000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((119/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((119/40)+(1/40)*x)) := (SharedCertificates.h160 (119/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(368100371896093/2500000000000),(8274884238311/6250000000000),(-4104287019/800000000000),(901940371/50000000000000),(50388683/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((119/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((119/40)+(1/40)*x)) := (SharedCertificates.h41 (119/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(123986042519891/100000000000000),(37973732137/20000000000000),(-904342167/100000000000000),(2139769/50000000000000),(59243/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((119/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((119/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((119/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((119/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((119/40)+(1/40)*x)) := (SharedCertificates.h167 (119/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(64589635156650841/100000000000000),(4567634019739/5000000000000),(-472181799681/100000000000000),(2392647383/100000000000000),(35475319/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((119/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(154823602513/100000000000000),(-109487777/50000000000000),(288309/20000000000000),(-3/32000000000),(3/2500000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((119/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(22796250265331/100000000000000),(172741588959/100000000000000),(-174393381/20000000000000),(2222229/50000000000000),(119787/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((119/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((119/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(178411646007947/50000000000000),(254673008307/6250000000000),(1656524209/50000000000000),(11330281/10000000000000),(26183/1000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((119/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(59970301179141/50000000000000),(180882869571/50000000000000),(-1926418511/100000000000000),(10854673/20000000000000),(1276939/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((119/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((119/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(31137591249023437/100000000000000),(310618907470703/25000000000000),(2025023/10240000),(3213/2048000),(621093751/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((119/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(57121/1600),(239/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((119/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(13651919/64000),(171363/64000),(717/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((119/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(6641998024793387359/100000000000000),(174203185217504157/50000000000000),(7893985963187681/100000000000000),(100821554436401/100000000000000),(159450796049/20000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((119/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(752785529/50000000000000),(-78974813/100000000000000),(2353263/100000000000000),(-26217/50000000000000),(363/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((119/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5287238793833/100000000000000),(-18772949537/100000000000000),(-52792809/100000000000000),(1030183/50000000000000),(1927971/20000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((119/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((119/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((119/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel39
