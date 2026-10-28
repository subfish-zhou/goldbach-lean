import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel0
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(41/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((41/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (41/40) (1/40)

def c3 : Certificate := ⟨(179619047619047/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((41/40)+(1/40)*x)) := (SharedCertificates.h2 (41/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((41/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-22047619047619/25000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((41/40)+(1/40)*x)) := (SharedCertificates.h4 (41/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(1681/1600),(41/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((41/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(31796693121693/25000000000000),(775529100529/12500000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((41/40)+(1/40)*x)) := (SharedCertificates.h8 (41/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((41/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((41/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(68921/64000),(5043/64000),(123/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((41/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(52458533130787/5000000000000),(19192146267361/25000000000000),(58512641059/3125000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((41/40)+(1/40)*x)) := (SharedCertificates.h13 (41/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((41/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((41/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(2825761/2560000),(68921/640000),(5043/1280000),(41/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((41/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(6167335515873/2000000000000),(30084563492063/100000000000000),(68790922619/6250000000000),(4474206349/25000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((41/40)+(1/40)*x)) := (SharedCertificates.h18 (41/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((41/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(56570410644531/50000000000000),(3449415283203/25000000000000),(68921/10240000),(1681/10240000),(50292969/25000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((41/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(92136437336787/12500000000000),(44944603578919/50000000000000),(4384839373553/100000000000000),(106947301793/100000000000000),(16382469/1250000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((41/40)+(1/40)*x)) := (SharedCertificates.h22 (41/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((41/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(14496167727661/12500000000000),(8485561596679/50000000000000),(808456707/78125000000),(33652832031/100000000000000),(621630863/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((41/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(130204731928451/50000000000000),(9527175506959/25000000000000),(1161850671579/50000000000000),(37783761677/50000000000000),(1116699/80000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((41/40)+(1/40)*x)) := (SharedCertificates.h26 (41/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((41/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(5943428768341/5000000000000),(5073658704681/25000000000000),(1484973279417/100000000000000),(12072953491/20000000000000),(1494033209/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((41/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(3525962701853/12500000000000),(4815949056189/100000000000000),(176193258153/50000000000000),(7162327567/50000000000000),(177268227/50000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((41/40)+(1/40)*x)) := (SharedCertificates.h30 (41/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((41/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((41/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((41/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((41/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((41/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (41/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((41/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((41/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (41/40) (1/40))

def c43 : Certificate := ⟨(6561/1600),(81/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((41/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((41/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(290315791/250000000000),(-573463291/20000000000000),(13274613/25000000000000),(-874049/100000000000000),(3493/25000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((41/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-263085349212101/25000000000000),(391675433813/100000000000000),(-2479693787/50000000000000),(62760443/100000000000000),(252323403/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((41/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((41/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (41/40) (1/40))

def c52 : Certificate := ⟨(25208333333333/25000000000000),(833333333333/100000000000000),0,0,(1/25000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((41/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (41/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((41/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (41/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((41/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (41/40) (1/40))

def c56 : Certificate := ⟨(997920997921/4000000000000),(-25933497867/50000000000000),(107831591/100000000000000),(-224183/100000000000000),(47/10000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((41/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(207900207899/100000000000000),(41493596587/20000000000000),(-13478949/3125000000000),(112091/12500000000000),(47/2500000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((41/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((41/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((41/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((41/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((41/40)+(1/40)*x)) := (SharedCertificates.h61 (41/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-2913196260373/100000000000000),(-581945535501/20000000000000),(433344007/12500000000000),(-367639/20000000000000),(59951/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((41/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((41/40)+(1/40)*x)) := (SharedCertificates.h61 (41/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-729164862917/25000000000000),(-1458322520251/50000000000000),(10794299/50000000000000),(3579343/50000000000000),(3579/5000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((41/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((41/40)+(1/40)*x)) := (SharedCertificates.h67 (41/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-7279539146997/50000000000000),(-14534873651087/100000000000000),(24154366329/100000000000000),(-391853/781250000000),(35859/25000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((41/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((41/40)+(1/40)*x)) := (SharedCertificates.h67 (41/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-3645820726743/25000000000000),(-14583182264059/100000000000000),(30130139/20000000000000),(49799527/100000000000000),(471761/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((41/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((41/40)+(1/40)*x)) := (SharedCertificates.h72 (41/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(2724900394239/12500000000000),(5430891024759/25000000000000),(-4717592999/6250000000000),(157342863/100000000000000),(113841/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((41/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((41/40)+(1/40)*x)) := (SharedCertificates.h72 (41/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(2734355302259/6250000000000),(21874527910179/50000000000000),(-58847533/6250000000000),(-31124069/10000000000000),(2094667/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((41/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((41/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((41/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(50208116320381/50000000000000),(83159723721/20000000000000),(-217008277/50000000000000),(233/3125000000000),(9367/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((41/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5260892021927719/50000000000000),(5423319300351/25000000000000),(-45288681409/50000000000000),(189091821/100000000000000),(886341/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((41/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(475204583097/50000000000000),(-1959505101/100000000000000),(12221657/100000000000000),(-59147/100000000000000),(427/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((41/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(415801014863/100000000000000),(414937759333/100000000000000),(-430433361/50000000000000),(595343/25000000000000),(629/1562500000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((41/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((41/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((41/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (41/40) (1/40))

def c87 : Certificate := ⟨(12422360248447/50000000000000),(-154315034143/100000000000000),(119809809/12500000000000),(-5953283/100000000000000),(9303/25000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((41/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(207039337473/100000000000000),(25719172357/12500000000000),(-638985649/50000000000000),(7937709/100000000000000),(10047/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((41/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((41/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((41/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((41/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((41/40)+(1/40)*x)) := (SharedCertificates.h61 (41/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-1450561320929/50000000000000),(-2885659189173/100000000000000),(15383281837/100000000000000),(-79771507/100000000000000),(500493/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((41/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((41/40)+(1/40)*x)) := (SharedCertificates.h61 (41/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-2904557189719/100000000000000),(-361561363939/12500000000000),(12023181847/100000000000000),(-42993849/100000000000000),(65119/5000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((41/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((41/40)+(1/40)*x)) := (SharedCertificates.h67 (41/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-14498767199073/100000000000000),(-14414701338499/100000000000000),(83568605199/100000000000000),(-494255893/100000000000000),(3997983/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((41/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((41/40)+(1/40)*x)) := (SharedCertificates.h67 (41/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-14522771774661/100000000000000),(-578496493019/4000000000000),(60157565773/100000000000000),(-20165283/10000000000000),(1697423/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((41/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((41/40)+(1/40)*x)) := (SharedCertificates.h72 (41/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(108545312921/500000000000),(5386070200897/25000000000000),(-81816870817/50000000000000),(1140490871/100000000000000),(7641849/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((41/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((41/40)+(1/40)*x)) := (SharedCertificates.h72 (41/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(43568153468021/100000000000000),(1355836065369/3125000000000),(-9047512239/5000000000000),(451064469/100000000000000),(5751849/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((41/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((41/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((41/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(50207253663909/50000000000000),(25772421161/6250000000000),(-1068944937/50000000000000),(2662337/25000000000000),(18761/12500000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((41/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(10521694028697569/100000000000000),(1075718448457/5000000000000),(-22294611359/12500000000000),(1294156001/100000000000000),(29716151/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((41/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(950417297131/100000000000000),(-1943377973/100000000000000),(100423/500000000000),(-2983/1562500000000),(919/25000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((41/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(2070396333/500000000000),(205754260827/50000000000000),(-2554200559/100000000000000),(16434421/100000000000000),(3507/1000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((41/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((41/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-4366586873059/50000000000000),(-2173446475087/25000000000000),(9783499201/25000000000000),(-251848197/100000000000000),(1107/12207031250)⟩
theorem h113 : c113.Valid (fun x => f113 ((41/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(24390243902439/25000000000000),(-1189767995241/50000000000000),(29018731591/50000000000000),(-1415547883/100000000000000),(35388699/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((41/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-1065021188551/12500000000000),(-8273933329403/100000000000000),(239982761013/100000000000000),(-381183977/6250000000000),(670893/400000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((41/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((41/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((41/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((41/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((41/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((41/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((41/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((41/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((41/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((41/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (41/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((41/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((41/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(958677931/1000000000000),(-374118217/4000000000000),(7128777/1250000000000),(-13909809/50000000000000),(737981/50000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((41/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(2011040565699/1250000000000),(-1621096323479/100000000000000),(34061752619/100000000000000),(-304492159/25000000000000),(4784021579/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((41/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((41/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (41/40) (1/40))

def c134 : Certificate := ⟨(19481/1600),(141/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((41/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((41/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(8230452674897/100000000000000),(-101610526851/100000000000000),(313612737/25000000000000),(-15487049/100000000000000),(19359/10000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((41/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(3131590792181/3125000000000),(1334035081/625000000000),(4900199/195312500000),(-30974101/100000000000000),(2173281/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((41/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((41/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (41/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((41/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (41/40) (1/40))

def c140 : Certificate := ⟨(12493412681071/50000000000000),(-3331573543/25000000000000),(-149533793/100000000000000),(1048567/50000000000000),(272907/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((41/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(52698551431/100000000000000),(26652588343/50000000000000),(4672931/781250000000),(-8388539/100000000000000),(1092773/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((41/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((41/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(27771373/100000000000000),(56182111/100000000000000),(5808967/20000000000000),(19651/3125000000000),(39/500000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((41/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((41/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(66645441/20000000000000),(67409651/10000000000000),(348447179/100000000000000),(939211/12500000000000),(94617/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((41/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-1475559404947/20000000000000),(-3731362101587/50000000000000),(-20934594643/25000000000000),(293647291/25000000000000),(7649719/5000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((41/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-368987059821/2500000000000),(-3733328741843/25000000000000),(-85772061737/50000000000000),(565188683/25000000000000),(307068063/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((41/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(4056232853503/20000000000000),(10253377907637/50000000000000),(55535781707/25000000000000),(-851980333/25000000000000),(211254299/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((41/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(13836041720583/25000000000000),(27996026597003/50000000000000),(127842292761/20000000000000),(-267824727/3125000000000),(1150557683/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((41/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(55391810151047/100000000000000),(56088452134083/100000000000000),(137814205677/20000000000000),(-1495000421/20000000000000),(9307261/800000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((41/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(20021084974847/20000000000000),(106666535483/100000000000000),(1225315171/100000000000000),(-8074123/50000000000000),(1096673/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((41/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((41/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((41/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((41/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(5255533930176833/10000000000000),(11196441155003/20000000000000),(317056355971/50000000000000),(-8686094547/100000000000000),(288572703/25000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((41/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(190275624377/100000000000000),(-202682531/100000000000000),(-415979/20000000000000),(9027/25000000000000),(2119/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((41/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(52698556309/50000000000000),(53305191489/50000000000000),(239260123/20000000000000),(-8383157/50000000000000),(2242299/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((41/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((41/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((41/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (41/40) (1/40))

def c175 : Certificate := ⟨(12480258849813/50000000000000),(-4986842799/12500000000000),(-202585049/50000000000000),(7186407/100000000000000),(41421/5000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((41/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(13160766791/25000000000000),(10638597971/20000000000000),(135056699/25000000000000),(-4790939/50000000000000),(221611/20000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((41/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((41/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(1108517/4000000000000),(28002421/50000000000000),(1154549/4000000000000),(564637/100000000000000),(487/5000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((41/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((41/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(166262961/50000000000000),(83996207/12500000000000),(346274429/100000000000000),(3371871/50000000000000),(117787/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((41/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-7370029227909/100000000000000),(-297880721963/4000000000000),(-37815604957/50000000000000),(670827131/50000000000000),(155133233/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((41/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-14743938615357/100000000000000),(-14901877837013/100000000000000),(-155304423897/100000000000000),(1301938513/50000000000000),(311618751/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((41/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(2532477399579/12500000000000),(5115903386711/25000000000000),(99949577187/50000000000000),(-3849354527/100000000000000),(2680871/625000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((41/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(27642942956213/50000000000000),(55874188825143/100000000000000),(18073063303/3125000000000),(-9848057329/100000000000000),(583668189/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((41/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(27666714447153/50000000000000),(2798514177631/5000000000000),(627886687077/100000000000000),(-8862970137/100000000000000),(591786499/50000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((41/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(100105313847253/100000000000000),(13305248069/12500000000000),(1109317317/100000000000000),(-18599119/100000000000000),(44517/2000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((41/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((41/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((41/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((41/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(26277640515521501/50000000000000),(6983046561709/12500000000000),(573271068009/100000000000000),(-9952457303/100000000000000),(1171933501/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((41/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(38055167069/20000000000000),(-101128183/50000000000000),(-1860531/100000000000000),(5027/12500000000000),(1079/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((41/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(105286144053/100000000000000),(13298251149/12500000000000),(1080483681/100000000000000),(-19153123/100000000000000),(2288477/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((41/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((41/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(338954060543/100000000000000),(339260129473/100000000000000),(281850189/100000000000000),(-988519/4000000000000),(14510461/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((41/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(165343444167/50000000000000),(161459979153/50000000000000),(-30404483/400000000000),(161282969/100000000000000),(33330483/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((41/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((41/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((41/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((41/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((41/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((41/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (41/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((41/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((41/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((41/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (41/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((41/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(47669398421/100000000000000),(-84821949/20000000000000),(6457499/100000000000000),(-40667/50000000000000),(221/20000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((41/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(503768712844427/100000000000000),(-31979770633/2500000000000),(1253028313/50000000000000),(-47168109/50000000000000),(5581451/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((41/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((41/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((41/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((41/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (41/40) (1/40))

def c223 : Certificate := ⟨(14641/1600),(121/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((41/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(948751441/2560000),(6855981/640000),(136763/1280000),(261/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((41/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((41/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(135480702467/50000000000000),(-6690405061/100000000000000),(12389639/10000000000000),(-2039447/100000000000000),(8149/25000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((41/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(50209965505179/50000000000000),(423161536463/100000000000000),(399643939/12500000000000),(-32937159/100000000000000),(751493/3125000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((41/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((41/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (41/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((41/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (41/40) (1/40))

def c231 : Certificate := ⟨(12486890918201/50000000000000),(-1055686101/4000000000000),(-85755997/50000000000000),(2446237/100000000000000),(753229/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((41/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(10487265439/10000000000000),(105568610099/100000000000000),(686047973/100000000000000),(-1223119/12500000000000),(241539/4000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((41/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((41/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(6873921/6250000000000),(221425207/100000000000000),(112886267/100000000000000),(1427979/100000000000000),(4159/10000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((41/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((41/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(329890537/25000000000000),(33205073/1250000000000),(135392941/10000000000000),(16891391/100000000000000),(25183/5000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((41/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-14682170230741/100000000000000),(-7389800617487/50000000000000),(-19208496587/20000000000000),(685679207/50000000000000),(52838413/6250000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((41/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-7344935202711/25000000000000),(-29590210350889/100000000000000),(-8315900043/4000000000000),(1269937757/50000000000000),(339319381/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((41/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(10086290156527/25000000000000),(8116373413011/20000000000000),(58117727267/25000000000000),(-4184145633/100000000000000),(2332608981/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((41/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(55079299075183/50000000000000),(110932191710457/100000000000000),(95464083779/12500000000000),(-2439676999/25000000000000),(3178535003/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((41/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(55173669800669/50000000000000),(111312301473933/100000000000000),(957682850689/100000000000000),(-7181648157/100000000000000),(3213079103/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((41/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(25052463822879/25000000000000),(42271729081/20000000000000),(1484982213/100000000000000),(-725677/4000000000000),(605927/5000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((41/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((41/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((41/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((41/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(52610139310780613/100000000000000),(110893320301301/100000000000000),(74383393003/10000000000000),(-10051454831/100000000000000),(797108097/12500000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((41/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(47519357157/25000000000000),(-400651233/100000000000000),(-73717/4000000000000),(5733/12500000000000),(23289/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((41/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(209745385673/100000000000000),(211137452411/100000000000000),(1372331209/100000000000000),(-19488453/100000000000000),(12355147/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((41/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((41/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((41/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (41/40) (1/40))

def c259 : Certificate := ⟨(2492151013801/10000000000000),(-39422680907/50000000000000),(-346260853/100000000000000),(182343/2000000000000),(181989/4000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((41/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(104653149319/100000000000000),(21025429817/20000000000000),(461681137/100000000000000),(-12156201/100000000000000),(6104511/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((41/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((41/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(855647/781250000000),(13752359/6250000000000),(55741751/50000000000000),(47263/5000000000000),(24607/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((41/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((41/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1314044553/100000000000000),(1319881049/50000000000000),(1337105031/100000000000000),(11104737/100000000000000),(74201/12500000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((41/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-14651439529471/100000000000000),(-14717796727889/100000000000000),(-12926235737/20000000000000),(1703297449/100000000000000),(854650593/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((41/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-29318215002209/100000000000000),(-3683300877783/12500000000000),(-28975679993/20000000000000),(1635702843/50000000000000),(1716154261/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((41/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(40260780052491/100000000000000),(4041229347119/10000000000000),(36620766907/25000000000000),(-99229943/2000000000000),(472049717/20000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((41/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(21985588191843/20000000000000),(27617031071837/25000000000000),(263794330713/50000000000000),(-6216764093/50000000000000),(642912667/10000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((41/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(5505794644467/5000000000000),(110845851502127/100000000000000),(359574241353/50000000000000),(-10687462509/100000000000000),(1628030127/25000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((41/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(50104707910727/50000000000000),(105237167957/50000000000000),(64677861/6250000000000),(-11683571/50000000000000),(3064559/25000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((41/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((41/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((41/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((41/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(26304954367164253/50000000000000),(2760737417561/2500000000000),(507956947323/100000000000000),(-12640752121/100000000000000),(6452129291/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((41/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(47519565423/25000000000000),(-199489481/50000000000000),(-997769/100000000000000),(51617/100000000000000),(23607/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((41/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(4186127501/2000000000000),(105127264223/50000000000000),(230898651/25000000000000),(-12116471/50000000000000),(12549679/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((41/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((41/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(1055525830573/50000000000000),(529370121579/25000000000000),(386640627/6250000000000),(-119729489/50000000000000),(12619271/10000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((41/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(2059562596239/100000000000000),(2015601386741/100000000000000),(-10781410887/25000000000000),(818226449/100000000000000),(148606939/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((41/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((41/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((41/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((41/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((41/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((41/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (41/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((41/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(203116856646273587/25000000000000),(3614219646389011/50000000000000),(-45749615777077/100000000000000),0,(105831/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((41/40)+(1/40)*x)) := (SharedCertificates.h297 (41/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(12308185747/100000000000000),(-54752333/50000000000000),(1667319/100000000000000),(-21001/100000000000000),(287/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((41/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(602695316104153/100000000000000),(182517139179/50000000000000),(381403097/4000000000000),(-64321107/100000000000000),(13430703/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((41/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((41/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (41/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((41/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (41/40) (1/40))

def c307 : Certificate := ⟨(2022182458365389/100000000000000),(11091229182759/50000000000000),0,0,(201/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((41/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (41/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((41/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (41/40) (1/40))

def c311 : Certificate := ⟨(125176096352147/6250000000000),(2817541634481/100000000000000),0,0,(251/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((41/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (41/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(499296605513/10000000000000),(-3512024797/50000000000000),(1976271/20000000000000),(-13901/100000000000000),(3/12500000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((41/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(100966883718977/100000000000000),(482761758813/50000000000000),(-27165757/2000000000000),(1910823/100000000000000),(907/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((41/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((41/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (41/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((41/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (41/40) (1/40))

def c316 : Certificate := ⟨(24939715487847/100000000000000),(-30027270087/50000000000000),(7159209/3125000000000),(-436973/50000000000000),(213/6250000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((41/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(241138048611/100000000000000),(60054540173/25000000000000),(-183275751/20000000000000),(174789/5000000000000),(13689/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((41/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((41/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(2271389/390625000000),(115851477/10000000000000),(572628171/100000000000000),(-2192879/50000000000000),(1587/6250000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((41/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((41/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(697490269/10000000000000),(694689819/5000000000000),(3431610567/50000000000000),(-55337867/100000000000000),(42039/12500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((41/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-8439827496599/25000000000000),(-8407623059667/25000000000000),(128342887043/100000000000000),(-236591507/50000000000000),(1057087/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((41/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-33800030076203/50000000000000),(-13484655379999/20000000000000),(17641834819/10000000000000),(-364653967/100000000000000),(7349627/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((41/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(92675139249323/100000000000000),(23039755267767/25000000000000),(-513723891971/100000000000000),(2384274327/100000000000000),(1016483/10000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((41/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(253418426063883/100000000000000),(252673921706553/100000000000000),(-742903026477/100000000000000),(1600974337/100000000000000),(28144531/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((41/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(63604281884103/25000000000000),(127332584409397/50000000000000),(60878053209/25000000000000),(-450406823/10000000000000),(53838199/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((41/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(50241428786403/50000000000000),(240797418077/50000000000000),(-1260129339/100000000000000),(1302901/50000000000000),(5277/10000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((41/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((41/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((41/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((41/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(52753316176489039/100000000000000),(1972419629793/781250000000),(-844571931353/100000000000000),(1892133881/100000000000000),(5589887/12500000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((41/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(189561542757/100000000000000),(-113401753/12500000000000),(7376643/100000000000000),(-14157/25000000000000),(591/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((41/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(120569257999/25000000000000),(480439115017/100000000000000),(-228748147/12500000000000),(789451/10000000000000),(95711/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((41/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((41/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((41/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (41/40) (1/40))

def c344 : Certificate := ⟨(24820014490631/100000000000000),(-178438339301/100000000000000),(153387047/10000000000000),(-3296319/25000000000000),(114503/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((41/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(239980679157/100000000000000),(118958892867/50000000000000),(-511290157/25000000000000),(8790183/50000000000000),(154883/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((41/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((41/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(575907263/100000000000000),(285478359/25000000000000),(278116373/50000000000000),(-9647223/100000000000000),(31923/25000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((41/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((41/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((41/40)+(1/40)*x)) := (SharedCertificates.h144 (41/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(6908123023/100000000000000),(13694740117/100000000000000),(266668527/4000000000000),(-118320621/100000000000000),(800581/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((41/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((41/40)+(1/40)*x)) := (SharedCertificates.h148 (41/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1679863925191/5000000000000),(-33308440702377/100000000000000),(286370927683/100000000000000),(-611488189/25000000000000),(4422077/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((41/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((41/40)+(1/40)*x)) := (SharedCertificates.h151 (41/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-16818804285273/25000000000000),(-33388423864409/50000000000000),(494772624467/100000000000000),(-1785870167/50000000000000),(61210083/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((41/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((41/40)+(1/40)*x)) := (SharedCertificates.h154 (41/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(18446222790489/20000000000000),(1140975453349/1250000000000),(-471848797161/50000000000000),(72585063/781250000000),(22610179/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((41/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((41/40)+(1/40)*x)) := (SharedCertificates.h157 (41/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(252201049968507/100000000000000),(25025215889613/10000000000000),(-944532687/48828125000),(14385888323/100000000000000),(44231261/20000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((41/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((41/40)+(1/40)*x)) := (SharedCertificates.h160 (41/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(253190180699961/100000000000000),(252214850989113/100000000000000),(-976230088801/100000000000000),(-823587807/100000000000000),(50394143/12500000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((41/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((41/40)+(1/40)*x)) := (SharedCertificates.h41 (41/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(100480537265577/100000000000000),(59622185613/12500000000000),(-353408851/10000000000000),(25513509/100000000000000),(218729/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((41/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((41/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((41/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((41/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((41/40)+(1/40)*x)) := (SharedCertificates.h167 (41/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(1318802494547341/2500000000000),(62512720761993/25000000000000),(-2033161037841/100000000000000),(15625008263/100000000000000),(72756153/25000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((41/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(189565913799/100000000000000),(-449281871/50000000000000),(2313101/20000000000000),(-145603/100000000000000),(619/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((41/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(479962279693/100000000000000),(118959577963/25000000000000),(-4087627969/100000000000000),(9003019/25000000000000),(313629/25000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((41/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((41/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(2899685630631/50000000000000),(1441737941007/25000000000000),(-32082686583/100000000000000),(33358449/10000000000000),(10264047/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((41/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(5657923181719/100000000000000),(2744148138773/50000000000000),(-165161066851/100000000000000),(2176883493/50000000000000),(30803217/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((41/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((41/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(111761055175781/50000000000000),(6141641845703/25000000000000),(21853/2048000),(2337/10240000),(30029297/12500000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((41/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(25921/1600),(161/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((41/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(4173281/64000),(77763/64000),(483/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((41/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(14575321503282453/100000000000000),(1873514668143399/100000000000000),(20223103610681/20000000000000),(2973581440063/100000000000000),(52314865837/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((41/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(68609121231/10000000000000),(-17638059643/20000000000000),(3288138409/50000000000000),(-23342073/6250000000000),(1417621/5000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((41/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(238511132159/50000000000000),(456988680297/100000000000000),(-19420342701/100000000000000),(597484979/100000000000000),(12801963/10000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((41/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((41/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((41/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel0
