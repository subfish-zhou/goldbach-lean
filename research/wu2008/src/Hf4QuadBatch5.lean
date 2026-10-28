import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel16
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(73/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((73/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (73/40) (1/40)

def c3 : Certificate := ⟨(319809523809523/100000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((73/40)+(1/40)*x)) := (SharedCertificates.h2 (73/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((73/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-28547619047619/12500000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((73/40)+(1/40)*x)) := (SharedCertificates.h4 (73/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(5329/1600),(73/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((73/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(40319947089947/10000000000000),(69041005291/625000000000),(75661375661/100000000000000),0,(3/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((73/40)+(1/40)*x)) := (SharedCertificates.h8 (73/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((73/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((73/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(389017/64000),(15987/64000),(219/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((73/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(236877133912037/4000000000000),(243366918402777/100000000000000),(3333793402777/100000000000000),(608912037/4000000000000),(1/25000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((73/40)+(1/40)*x)) := (SharedCertificates.h13 (73/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((73/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((73/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(28398241/2560000),(389017/640000),(15987/1280000),(73/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((73/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(3099014394841269/100000000000000),(169809007936507/100000000000000),(872306547619/25000000000000),(6373015873/20000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((73/40)+(1/40)*x)) := (SharedCertificates.h18 (73/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((73/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1012241988769531/50000000000000),(34665821533203/25000000000000),(389017/10240000),(5329/10240000),(89355469/25000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((73/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(13189138209226703/100000000000000),(903365630768949/100000000000000),(12374871654369/50000000000000),(339037579571/100000000000000),(291067167/12500000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((73/40)+(1/40)*x)) := (SharedCertificates.h22 (73/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((73/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(923670814752197/25000000000000),(151836298315429/50000000000000),(259993661499/2500000000000),(189949707031/100000000000000),(1962255863/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((73/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(8296421032398569/100000000000000),(681897619101249/100000000000000),(5838164547099/25000000000000),(8530651393/2000000000000),(2203125367/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((73/40)+(1/40)*x)) := (SharedCertificates.h26 (73/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((73/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(3371398473845519/50000000000000),(129313914065307/20000000000000),(13285676102599/50000000000000),(60665187683/10000000000000),(1047364503/12500000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((73/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1600076418539381/100000000000000),(149835923183/97656250000),(6305424055043/100000000000000),(143959453311/100000000000000),(1988330073/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((73/40)+(1/40)*x)) := (SharedCertificates.h30 (73/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((73/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((73/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((73/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((73/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((73/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (73/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((73/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((73/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (73/40) (1/40))

def c43 : Certificate := ⟨(12769/1600),(113/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((73/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((73/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(59668318733/100000000000000),(-528038219/50000000000000),(14018713/100000000000000),(-165413/100000000000000),(939/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((73/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-52171115685471/5000000000000),(99165579671/50000000000000),(-1787839661/100000000000000),(3223851/20000000000000),(65492471/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((73/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((73/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (73/40) (1/40))

def c52 : Certificate := ⟨(63749999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((73/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (73/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((73/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (73/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((73/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (73/40) (1/40))

def c56 : Certificate := ⟨(23391812865497/100000000000000),(-22799037881/50000000000000),(88885137/100000000000000),(-86633/50000000000000),(171/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((73/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(6432748538011/100000000000000),(45598075761/25000000000000),(-355540553/100000000000000),(693061/100000000000000),(193/12500000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((73/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((73/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((73/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((73/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((73/40)+(1/40)*x)) := (SharedCertificates.h61 (73/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-92541294757351/100000000000000),(-2694286301107/100000000000000),(1628001483/50000000000000),(-1228053/50000000000000),(45627/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((73/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((73/40)+(1/40)*x)) := (SharedCertificates.h61 (73/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-48005714158857/50000000000000),(-579119420807/20000000000000),(601869221/100000000000000),(2507881/50000000000000),(60867/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((73/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((73/40)+(1/40)*x)) := (SharedCertificates.h67 (73/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-228234285706101/50000000000000),(-13128845148751/100000000000000),(19986568761/100000000000000),(-9366063/25000000000000),(12671/10000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((73/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((73/40)+(1/40)*x)) := (SharedCertificates.h67 (73/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-479655873014769/100000000000000),(-2888914069503/20000000000000),(240653267/6250000000000),(14522237/50000000000000),(88593/25000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((73/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((73/40)+(1/40)*x)) := (SharedCertificates.h72 (73/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(644583540332313/100000000000000),(1734715353829/10000000000000),(-61724481531/100000000000000),(129694689/100000000000000),(59821/25000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((73/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((73/40)+(1/40)*x)) := (SharedCertificates.h72 (73/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(716903034758141/50000000000000),(42885522698991/100000000000000),(-23908443563/100000000000000),(-44337587/25000000000000),(306119/20000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((73/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((73/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((73/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(56639649806777/50000000000000),(388250282503/100000000000000),(-106038411/25000000000000),(17833/10000000000000),(1773/25000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((73/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(1112919434799837/10000000000000),(1644955144289/10000000000000),(-73736637473/100000000000000),(10078521/6250000000000),(678903/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((73/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(898537637793/100000000000000),(-1328087249/100000000000000),(3958129/50000000000000),(-419/1250000000000),(59/25000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((73/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(3220821796891/25000000000000),(36630036703/10000000000000),(-134175947/20000000000000),(819141/50000000000000),(15589/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((73/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((73/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((73/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (73/40) (1/40))

def c87 : Certificate := ⟨(5181347150259/25000000000000),(-53692716583/50000000000000),(69550151/12500000000000),(-720727/25000000000000),(15017/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((73/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1424870466321/25000000000000),(71590288777/50000000000000),(-370934139/50000000000000),(3843877/100000000000000),(14141/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((73/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((73/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((73/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((73/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((73/40)+(1/40)*x)) := (SharedCertificates.h61 (73/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-81741791725939/100000000000000),(-131403418649/6250000000000),(9663507/100000000000),(-10924179/25000000000000),(64399/12500000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((73/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((73/40)+(1/40)*x)) := (SharedCertificates.h61 (73/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-16890320941951/20000000000000),(-2241395479513/100000000000000),(8533035363/100000000000000),(-30013109/100000000000000),(33277/5000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((73/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((73/40)+(1/40)*x)) := (SharedCertificates.h67 (73/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-201888517232627/50000000000000),(-5135653326521/50000000000000),(9966878987/20000000000000),(-245182347/100000000000000),(2236139/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((73/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((73/40)+(1/40)*x)) := (SharedCertificates.h67 (73/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-421976929425409/100000000000000),(-1398272747347/12500000000000),(21530029653/50000000000000),(-75506733/50000000000000),(3346843/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((73/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((73/40)+(1/40)*x)) := (SharedCertificates.h72 (73/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(71799387160817/12500000000000),(1724027153147/12500000000000),(-88327895903/100000000000000),(261710101/50000000000000),(80349/2000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((73/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((73/40)+(1/40)*x)) := (SharedCertificates.h72 (73/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1262366280519493/100000000000000),(4160616945119/12500000000000),(-4215242521/3125000000000),(453459779/100000000000000),(531291/5000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((73/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((73/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((73/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(22344760933179/20000000000000),(75670564303/25000000000000),(-54531803/4000000000000),(6001493/100000000000000),(1911/2500000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((73/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2765598325343621/25000000000000),(6586867773509/50000000000000),(-5841498191/6250000000000),(584051031/100000000000000),(7051579/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((73/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(451981760527/50000000000000),(-1076491863/100000000000000),(8919357/100000000000000),(-67443/100000000000000),(1371/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((73/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(5705665338991/50000000000000),(143647202593/50000000000000),(-1465050819/100000000000000),(7668591/100000000000000),(153429/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((73/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((73/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-253495463839543/100000000000000),(-677156989727/10000000000000),(23148709281/100000000000000),(-109115321/100000000000000),(18429721/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((73/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(10958904109589/20000000000000),(-18765246763/2500000000000),(10282326993/100000000000000),(-28170759/20000000000000),(391261/20000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((73/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-138901624021667/100000000000000),(-1807687285879/100000000000000),(37447063797/100000000000000),(-572762693/100000000000000),(28112057/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((73/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((73/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((73/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((73/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((73/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((73/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((73/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((73/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((73/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((73/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (73/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((73/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((73/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(2384826149/25000000000000),(-261350811/50000000000000),(895037/5000000000000),(-7663/1562500000000),(13583/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((73/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(63817500592337/50000000000000),(-684946379651/100000000000000),(1824990507/25000000000000),(-14625103/20000000000000),(44578271/12500000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((73/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((73/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (73/40) (1/40))

def c134 : Certificate := ⟨(29529/1600),(173/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((73/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((73/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(5899705014749/100000000000000),(-13052444723/25000000000000),(462033441/100000000000000),(-511099/12500000000000),(36509/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((73/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(108882743362827/100000000000000),(2497976871/800000000000),(924066873/100000000000000),(-8177593/100000000000000),(1279703/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((73/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((73/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (73/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((73/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (73/40) (1/40))

def c140 : Certificate := ⟨(12228444660877/50000000000000),(-9338365469/50000000000000),(-1640377/4000000000000),(28133/5000000000000),(77377/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((73/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1086221356491/50000000000000),(59765539/80000000000),(82018849/50000000000000),(-1125321/50000000000000),(161623/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((73/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((73/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(47195073411/100000000000000),(1622965121/50000000000000),(31469247/50000000000000),(147307/100000000000000),(551/3125000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((73/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((73/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(112858061813/20000000000000),(19369807489/50000000000000),(747522617/100000000000000),(10367/625000000000),(211457/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((73/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-304129720933781/100000000000000),(-10457706165127/100000000000000),(-5729792849/25000000000000),(315735213/100000000000000),(9051821/20000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((73/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-614891003595399/100000000000000),(-21372332284249/100000000000000),(-54739979273/100000000000000),(609607009/100000000000000),(1859553/2000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((73/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(823032289697679/100000000000000),(6959624453811/25000000000000),(5623756751/12500000000000),(-915368049/100000000000000),(62734877/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((73/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(1149472376817063/50000000000000),(79661907459793/100000000000000),(195364334607/100000000000000),(-2322307141/100000000000000),(346217681/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((73/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2380951364182713/100000000000000),(85338430353069/100000000000000),(307296132433/100000000000000),(-201430523/10000000000000),(376779527/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((73/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(167027328799/160000000000),(76329888871/50000000000000),(39101389/10000000000000),(-4353977/100000000000000),(166031/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((73/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((73/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((73/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((73/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(10958064573535677/20000000000000),(39528156291431/50000000000000),(18296688191/10000000000000),(-2367894097/100000000000000),(354484337/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((73/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(182513981969/100000000000000),(-263347279/100000000000000),(-229507/100000000000000),(4549/50000000000000),(1211/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((73/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(869113828703/20000000000000),(29896879351/20000000000000),(330657523/100000000000000),(-1116221/25000000000000),(730937/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((73/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((73/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((73/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (73/40) (1/40))

def c175 : Certificate := ⟨(93754051181/400000000000),(-3216324073/6250000000000),(-1965371/5000000000000),(88421/5000000000000),(43691/20000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((73/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(416396587933/20000000000000),(17153728389/25000000000000),(13102473/25000000000000),(-471579/20000000000000),(330081/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((73/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((73/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(4334652961/10000000000000),(714275397/25000000000000),(49262393/100000000000000),(-1313/5000000000000),(17411/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((73/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((73/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(518353420617/100000000000000),(34106765953/100000000000000),(117026243/20000000000000),(-19129/5000000000000),(208659/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((73/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-72866704880829/25000000000000),(-9605022133041/100000000000000),(-912691069/12500000000000),(13220179/4000000000000),(1444219/3125000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((73/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-29451175628173/5000000000000),(-9806070212051/50000000000000),(-10785010709/50000000000000),(663920209/100000000000000),(94860191/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((73/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(394650031364419/50000000000000),(25604262327357/100000000000000),(1490791117/25000000000000),(-905157267/100000000000000),(32037351/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((73/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(2202515179297029/100000000000000),(73120313163021/100000000000000),(73136552439/100000000000000),(-2495735051/100000000000000),(14130131/4000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((73/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1138897033600621/50000000000000),(9764108987179/12500000000000),(160727318679/100000000000000),(-1253283789/50000000000000),(383605551/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((73/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(5210365620447/5000000000000),(1400869287/1000000000000),(154082177/100000000000000),(-94841/2000000000000),(677573/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((73/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((73/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((73/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((73/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(2187784415393273/4000000000000),(72588657613601/100000000000000),(31720405093/50000000000000),(-2503433763/100000000000000),(90348381/25000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((73/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(91416685571/50000000000000),(-242649667/100000000000000),(21993/20000000000000),(8503/100000000000000),(1237/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((73/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(130142740023/3125000000000),(68644668633/50000000000000),(106827327/100000000000000),(-4693269/100000000000000),(14887/2000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((73/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((73/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(217238264729/2000000000000),(307733784733/100000000000000),(-784625759/100000000000000),(12873/50000000000000),(33382917/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((73/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(2975866640123/50000000000000),(21772664757/25000000000000),(-32459093/2000000000000),(11123181/50000000000000),(19280029/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((73/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((73/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((73/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((73/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((73/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((73/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (73/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((73/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((73/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((73/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (73/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((73/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(38849104977/100000000000000),(-41895919/25000000000000),(156607/6250000000000),(-37/200000000000),(199/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((73/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(92600483816271/20000000000000),(-664769010893/50000000000000),(-3368210383/100000000000000),(-185963/400000000000),(4665263/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((73/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((73/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((73/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((73/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (73/40) (1/40))

def c223 : Certificate := ⟨(23409/1600),(153/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((73/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2141666001/2560000),(12066957/640000),(189947/1280000),(293/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((73/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((73/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(34806519261/25000000000000),(-492835671/20000000000000),(8177583/25000000000000),(-385963/100000000000000),(4379/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((73/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(23294980910761/20000000000000),(281776042299/50000000000000),(312907831/20000000000000),(-8086237/100000000000000),(7395707/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((73/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((73/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (73/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((73/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (73/40) (1/40))

def c231 : Certificate := ⟨(48022101167/200000000000),(-4061312417/12500000000000),(-2889751/6250000000000),(325407/50000000000000),(428889/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((73/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(3955797665997/100000000000000),(64980998671/50000000000000),(92472031/50000000000000),(-2603261/100000000000000),(58027/3125000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((73/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((73/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(156483351743/100000000000000),(2056413463/20000000000000),(183533233/100000000000000),(137377/50000000000000),(158177/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((73/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((73/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(466354972841/25000000000000),(122164594443/100000000000000),(432114803/20000000000000),(1384189/50000000000000),(189309/10000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((73/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-553737881003057/100000000000000),(-3637484541351/20000000000000),(-12822241607/50000000000000),(7351027/2000000000000),(260010449/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((73/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1129528096651621/100000000000000),(-3782846570889/10000000000000),(-38729812187/50000000000000),(690903269/100000000000000),(542071247/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((73/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1478300255324719/100000000000000),(47070994138127/100000000000000),(8443846557/50000000000000),(-558074881/50000000000000),(718514213/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((73/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(1053016529073353/25000000000000),(140243359035109/100000000000000),(258767740761/100000000000000),(-2707058099/100000000000000),(2010036983/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((73/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(224341458776701/5000000000000),(79251877382077/50000000000000),(594769995021/100000000000000),(-1975554703/100000000000000),(2289012593/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((73/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(108068078683737/100000000000000),(270206061999/100000000000000),(553421357/100000000000000),(-616471/12500000000000),(774381/20000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((73/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((73/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((73/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((73/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(7085309014397503/12500000000000),(69112413809189/50000000000000),(109522241043/50000000000000),(-713604023/25000000000000),(521336581/25000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((73/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(4410534521/2500000000000),(-86043583/20000000000000),(91839/25000000000000),(193/2000000000000),(6571/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((73/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(7915725987409/100000000000000),(260331369909/100000000000000),(15354901/4000000000000),(-628607/12500000000000),(109487/2500000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((73/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((73/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((73/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (73/40) (1/40))

def c259 : Certificate := ⟨(22250667789341/100000000000000),(-837030753/1000000000000),(82498811/100000000000000),(882423/50000000000000),(1118859/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((73/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(1832888140439/50000000000000),(111604100399/100000000000000),(-6874901/6250000000000),(-2353129/100000000000000),(1860473/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((73/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((73/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(67189578707/50000000000000),(8182313281/100000000000000),(1456127/1250000000000),(-418047/100000000000000),(72849/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((73/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((73/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(160269781041/10000000000000),(97287923473/100000000000000),(685686709/50000000000000),(-2610803/50000000000000),(174491/10000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((73/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-128287482001683/25000000000000),(-3904804755441/25000000000000),(15556864091/100000000000000),(330632427/100000000000000),(130256903/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((73/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-522614143496027/50000000000000),(-32394410098729/100000000000000),(14502604227/100000000000000),(179403609/25000000000000),(270665703/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((73/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1373008137512447/100000000000000),(2538347151567/6250000000000),(-38410756273/50000000000000),(-803234117/100000000000000),(719436019/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((73/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(974849125390339/25000000000000),(120205440844161/100000000000000),(-74498336733/100000000000000),(-2662949093/100000000000000),(1004372571/50000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((73/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(826990279805029/20000000000000),(26940200653929/20000000000000),(138769631483/100000000000000),(-1640135591/50000000000000),(453254783/20000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((73/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(10746593171917/10000000000000),(231390514079/100000000000000),(-6469167/6250000000000),(-1024861/20000000000000),(966661/25000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((73/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((73/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((73/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((73/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(28187062215647791/50000000000000),(29653053961511/25000000000000),(-99695093771/100000000000000),(-525762857/20000000000000),(207835657/10000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((73/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(22173293379/12500000000000),(-93306051/25000000000000),(109897/10000000000000),(5299/100000000000000),(1649/25000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((73/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(7334839238279/100000000000000),(22350854967/10000000000000),(-52784123/25000000000000),(-4637241/100000000000000),(1082779/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((73/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((73/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(14122097183703/20000000000000),(2037428468919/100000000000000),(-3073367403/50000000000000),(-70437703/100000000000000),(8256587/20000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((73/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(4836334651953/12500000000000),(146597471031/25000000000000),(-5700406003/50000000000000),(7348719/6250000000000),(27330929/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((73/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((73/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((73/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((73/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((73/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((73/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (73/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((73/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(498464938699132579/50000000000000),(134389496345161/3125000000000),(-45749615777077/100000000000000),0,(129267/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((73/40)+(1/40)*x)) := (SharedCertificates.h297 (73/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(2507698943/25000000000000),(-43269919/100000000000000),(161743/25000000000000),(-4777/100000000000000),(53/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((73/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(622882638516251/100000000000000),(87713361041/10000000000000),(3780133587/50000000000000),(7609893/100000000000000),(612759/10000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((73/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((73/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (73/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((73/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (73/40) (1/40))

def c307 : Certificate := ⟨(2732021126061989/100000000000000),(11091229182759/50000000000000),0,0,(209/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((73/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (73/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((73/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (73/40) (1/40))

def c311 : Certificate := ⟨(261622359242219/12500000000000),(2817541634481/100000000000000),0,0,(261/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((73/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (73/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4777879091147/100000000000000),(-160798007/2500000000000),(8658569/100000000000000),(-11657/100000000000000),(21/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((73/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(65266333073917/50000000000000),(884129619287/100000000000000),(-148775513/12500000000000),(1602211/100000000000000),(3217/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((73/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((73/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (73/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((73/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (73/40) (1/40))

def c316 : Certificate := ⟨(4645408251817/20000000000000),(-23849195149/50000000000000),(10135189/6250000000000),(-275657/50000000000000),(971/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((73/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(886479370457/12500000000000),(47698390297/25000000000000),(-648652101/100000000000000),(1102627/50000000000000),(8939/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((73/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((73/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(502941231517/100000000000000),(27061528961/100000000000000),(68004789/25000000000000),(-2162387/100000000000000),(3489/25000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((73/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((73/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(5963959253997/100000000000000),(159490435307/50000000000000),(156445447/5000000000000),(-26351041/100000000000000),(17627/10000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((73/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-992433940764247/100000000000000),(-13338549059581/50000000000000),(91603100813/100000000000000),(-76643033/25000000000000),(663787/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((73/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-514023891756497/25000000000000),(-57207592962367/100000000000000),(28731637419/20000000000000),(-39160503/12500000000000),(4462139/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((73/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(2584541556699029/100000000000000),(65475555024051/100000000000000),(-167677277067/50000000000000),(1426631899/100000000000000),(6384187/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((73/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(7629718133607/100000000000),(209907796427653/100000000000000),(-74588629693/12500000000000),(704571663/50000000000000),(3289127/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((73/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(4264300374146943/50000000000000),(259219890115823/100000000000000),(-63719480279/100000000000000),(-1074106621/50000000000000),(8901023/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((73/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(114686611158829/100000000000000),(408648651337/100000000000000),(-512642523/50000000000000),(2248121/100000000000000),(15917/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((73/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((73/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((73/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((73/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(937949638878169/1562500000000),(204116809840309/100000000000000),(-167438876347/25000000000000),(1695136329/100000000000000),(5040857/20000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((73/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(83293384593/50000000000000),(-113289531/20000000000000),(3784749/100000000000000),(-11947/50000000000000),(213/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((73/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(2841504088671/20000000000000),(11984874409/3125000000000),(-1251707081/100000000000000),(142353/3125000000000),(130483/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((73/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((73/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((73/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (73/40) (1/40))

def c344 : Certificate := ⟨(20341824075081/100000000000000),(-1371914341/1250000000000),(9248939/1250000000000),(-4988231/100000000000000),(33993/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((73/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(776362654153/12500000000000),(29267505941/20000000000000),(-197310699/20000000000000),(3325487/50000000000000),(33039/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((73/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((73/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(48219117661/12500000000000),(9088879437/50000000000000),(91598999/100000000000000),(-1030613/50000000000000),(4717/12500000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((73/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((73/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((73/40)+(1/40)*x)) := (SharedCertificates.h144 (73/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(114527945677/2500000000000),(214746098537/100000000000000),(260554823/25000000000000),(-4887881/20000000000000),(454269/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((73/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((73/40)+(1/40)*x)) := (SharedCertificates.h148 (73/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-869241643947743/100000000000000),(-20467212595957/100000000000000),(34612819867/25000000000000),(-466471503/50000000000000),(9308997/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((73/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((73/40)+(1/40)*x)) := (SharedCertificates.h151 (73/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-1793040085286367/100000000000000),(-870354668517/2000000000000),(263458371329/100000000000000),(-1573503741/100000000000000),(23792609/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((73/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((73/40)+(1/40)*x)) := (SharedCertificates.h154 (73/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(569958256505497/25000000000000),(51013214926979/100000000000000),(-51181679099/12500000000000),(3158505789/100000000000000),(6725247/20000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((73/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((73/40)+(1/40)*x)) := (SharedCertificates.h157 (73/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(6663044472413847/100000000000000),(20019879739617/12500000000000),(-252288052977/25000000000000),(6228868783/100000000000000),(4258671/5000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((73/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((73/40)+(1/40)*x)) := (SharedCertificates.h160 (73/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(734911651750003/10000000000000),(193050114880607/100000000000000),(-411979750479/50000000000000),(2529929179/100000000000000),(74467901/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((73/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((73/40)+(1/40)*x)) := (SharedCertificates.h41 (73/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(14100944425967/12500000000000),(77713204571/25000000000000),(-1881507991/100000000000000),(5620361/50000000000000),(42473/25000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((73/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((73/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((73/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((73/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((73/40)+(1/40)*x)) := (SharedCertificates.h167 (73/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(59086891673222563/100000000000000),(78180325834283/50000000000000),(-1035853984167/100000000000000),(3319103313/50000000000000),(104376169/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((73/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(42310568879/25000000000000),(-447862999/100000000000000),(4152163/100000000000000),(-18927/50000000000000),(529/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((73/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(12437812024539/100000000000000),(146904216837/50000000000000),(-976970273/50000000000000),(660287/5000000000000),(205839/50000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((73/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((73/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(33193829983489/20000000000000),(890530270533/20000000000000),(-1501490513/12500000000000),(135747813/100000000000000),(318273/6250000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((73/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(22735499988691/25000000000000),(238805627813/20000000000000),(-22938426073/100000000000000),(388607377/100000000000000),(7360071/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((73/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((73/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1566895133300781/50000000000000),(49861798095703/25000000000000),(516913/10240000),(6497/10240000),(49560547/12500000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((73/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(37249/1600),(193/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((73/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(7189057/64000),(111747/64000),(579/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((73/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(352015575822559773/100000000000000),(3484431436429543/12500000000000),(471814806680999/50000000000000),(4448578823883/25000000000000),(20545313151/10000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((73/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(7101958469/25000000000000),(-449912589/20000000000000),(4079491/4000000000000),(-1740953/50000000000000),(75353/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((73/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(55767820039/1000000000000),(27031942687/100000000000000),(-322249709/20000000000000),(18164387/50000000000000),(29281363/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((73/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((73/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((73/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel16

namespace Hf4Quad.Panel17
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(15/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((15/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (15/8) (1/40)

def c3 : Certificate := ⟨(82142857142857/25000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((15/8)+(1/40)*x)) := (SharedCertificates.h2 (15/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((15/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-237142857142857/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((15/8)+(1/40)*x)) := (SharedCertificates.h4 (15/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(225/64),(3/32),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((15/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(212797619047619/50000000000000),(5674603174603/50000000000000),(75661375661/100000000000000),0,(1/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((15/8)+(1/40)*x)) := (SharedCertificates.h8 (15/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((15/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((15/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(3375/512),(135/512),(9/2560),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((15/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(131525/2048),(5261/2048),(3425130208333/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((15/8)+(1/40)*x)) := (SharedCertificates.h13 (15/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((15/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((15/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(50625/4096),(675/1024),(27/2048),(3/25600),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((15/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(3452845982142857/100000000000000),(36830357142857/20000000000000),(736607142857/20000000000000),(16369047619/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((15/8)+(1/40)*x)) := (SharedCertificates.h18 (15/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((15/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(2317428588867187/100000000000000),(38623809814453/25000000000000),(675/16384),(9/16384),(367187501/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((15/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(754880905151367/5000000000000),(62906742095947/6250000000000),(26840209960937/100000000000000),(71573893229/20000000000000),(95686343/4000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((15/8)+(1/40)*x)) := (SharedCertificates.h22 (15/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((15/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(173807144165039/4000000000000),(347614288330077/100000000000000),(2317428588867/20000000000000),(205993652343/100000000000000),(207094727/10000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((15/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(9757110050746369/100000000000000),(780568804059707/100000000000000),(26018960135321/100000000000000),(115639822823/25000000000000),(581289697/12500000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((15/8)+(1/40)*x)) := (SharedCertificates.h26 (15/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((15/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(8147209882736203/100000000000000),(760406255722043/100000000000000),(380203127861/1250000000000),(675916671751/100000000000000),(9084641123/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((15/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1933345837252479/100000000000000),(180445611476897/100000000000000),(288712978363/4000000000000),(16039609909/10000000000000),(2155799761/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((15/8)+(1/40)*x)) := (SharedCertificates.h30 (15/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((15/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((15/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((15/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((15/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((15/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (15/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((15/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((15/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (15/8) (1/40))

def c43 : Certificate := ⟨(529/64),(23/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((15/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((15/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(57610946079/100000000000000),(-500964749/50000000000000),(2613729/20000000000000),(-151521/100000000000000),(1691/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((15/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-130379084524351/12500000000000),(47842137891/25000000000000),(-847278153/50000000000000),(7504627/50000000000000),(61032649/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((15/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((15/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (15/8) (1/40))

def c52 : Certificate := ⟨(25833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((15/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (15/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((15/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (15/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((15/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (15/8) (1/40))

def c56 : Certificate := ⟨(11650485436893/50000000000000),(-45244603639/100000000000000),(87853599/100000000000000),(-17059/10000000000000),(67/20000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((15/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(6796116504853/100000000000000),(180978414553/100000000000000),(-175707199/50000000000000),(682357/100000000000000),(1527/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((15/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((15/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((15/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((15/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((15/8)+(1/40)*x)) := (SharedCertificates.h61 (15/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-19583372608159/20000000000000),(-1340645925281/50000000000000),(1620600381/50000000000000),(-2477673/100000000000000),(11229/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((15/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((15/8)+(1/40)*x)) := (SharedCertificates.h61 (15/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-25450043789523/25000000000000),(-2893129908053/100000000000000),(315805913/50000000000000),(4898793/100000000000000),(60251/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((15/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((15/8)+(1/40)*x)) := (SharedCertificates.h67 (15/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-482646613845599/100000000000000),(-815584115057/6250000000000),(19763732769/100000000000000),(-36816747/100000000000000),(31451/25000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((15/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((15/8)+(1/40)*x)) := (SharedCertificates.h67 (15/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-101705876304677/20000000000000),(-3607205988703/25000000000000),(1005441161/25000000000000),(14032449/50000000000000),(348631/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((15/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((15/8)+(1/40)*x)) := (SharedCertificates.h72 (15/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(679031983779827/100000000000000),(8550902714799/50000000000000),(-60951199347/100000000000000),(128068313/100000000000000),(238987/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((15/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((15/8)+(1/40)*x)) := (SharedCertificates.h72 (15/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(1519480075464913/100000000000000),(10696946734023/25000000000000),(-24952932281/100000000000000),(-42711071/25000000000000),(1502343/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((15/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((15/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((15/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(114054105005181/100000000000000),(386555836909/100000000000000),(-84612399/20000000000000),(185493/100000000000000),(3489/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((15/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11161799790798459/100000000000000),(16156532795063/100000000000000),(-72774480181/100000000000000),(79731449/50000000000000),(1336397/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((15/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(89591286239/10000000000000),(-1296820031/100000000000000),(3859221/50000000000000),(-32427/100000000000000),(113/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((15/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(13613217437543/100000000000000),(181818182353/50000000000000),(-330578467/50000000000000),(1602807/100000000000000),(30603/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((15/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((15/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((15/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (15/8) (1/40))

def c87 : Certificate := ⟨(1025641025641/5000000000000),(-26298487837/25000000000000),(3371601/625000000000),(-1383221/50000000000000),(14263/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((15/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1196581196581/20000000000000),(35064650449/25000000000000),(-359637441/50000000000000),(3688589/100000000000000),(3417/12500000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((15/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((15/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((15/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((15/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((15/8)+(1/40)*x)) := (SharedCertificates.h61 (15/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-85908393600687/100000000000000),(-412863781697/20000000000000),(293934447/3125000000000),(-21091163/50000000000000),(248119/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((15/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((15/8)+(1/40)*x)) := (SharedCertificates.h61 (15/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-11112562772653/12500000000000),(-551905149079/25000000000000),(4177563649/50000000000000),(-29292069/100000000000000),(320381/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((15/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((15/8)+(1/40)*x)) := (SharedCertificates.h67 (15/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-26507640766699/6250000000000),(-5037436295903/50000000000000),(48392182351/100000000000000),(-58908819/25000000000000),(2160801/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((15/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((15/8)+(1/40)*x)) := (SharedCertificates.h67 (15/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-17767130176363/4000000000000),(-11015740221721/100000000000000),(5270528739/12500000000000),(-18450371/12500000000000),(3218233/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((15/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((15/8)+(1/40)*x)) := (SharedCertificates.h72 (15/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(601630360847221/100000000000000),(13445093598677/100000000000000),(-42628438487/50000000000000),(500459399/100000000000000),(483527/12500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((15/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((15/8)+(1/40)*x)) := (SharedCertificates.h72 (15/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(332100053529563/25000000000000),(32750797660013/100000000000000),(-3304708859/2500000000000),(446296493/100000000000000),(10186387/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((15/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((15/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((15/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(28080940901453/25000000000000),(74325071037/25000000000000),(-1327892091/100000000000000),(5800857/100000000000000),(36799/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((15/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11088371535445659/100000000000000),(12806781470947/100000000000000),(-18007881343/20000000000000),(111542011/20000000000000),(13527091/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((15/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(901845682933/100000000000000),(-1041608369/100000000000000),(4263083/50000000000000),(-31833/50000000000000),(1301/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((15/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(5990059991549/50000000000000),(140762463509/50000000000000),(-142000841/10000000000000),(3674219/50000000000000),(146579/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((15/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((15/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-1668417951413/625000000000),(-1670066371931/25000000000000),(22508176889/100000000000000),(-104438359/100000000000000),(9006717/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((15/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(53333333333333/100000000000000),(-88888888889/12500000000000),(9481481481/100000000000000),(-63209877/50000000000000),(854189/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((15/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-71185832593621/50000000000000),(-832259695477/50000000000000),(4274744111/12500000000000),(-511673161/100000000000000),(2577241/10000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((15/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((15/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((15/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((15/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((15/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((15/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((15/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((15/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((15/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((15/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (15/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((15/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((15/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1712352211/20000000000000),(-456627257/100000000000000),(3805227/25000000000000),(-405891/100000000000000),(2729/25000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((15/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(63146867328603/50000000000000),(-328300733063/50000000000000),(859742441/12500000000000),(-6765889/10000000000000),(158019149/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((15/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((15/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (15/8) (1/40))

def c134 : Certificate := ⟨(1209/64),(7/32),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((15/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((15/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(231884057971/4000000000000),(-2520478891/5000000000000),(219172077/50000000000000),(-3811689/100000000000000),(33439/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((15/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(10951086956521/10000000000000),(157923755511/50000000000000),(876688291/100000000000000),(-762339/10000000000000),(600623/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((15/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((15/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (15/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((15/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (15/8) (1/40))

def c140 : Certificate := ⟨(12209688122097/50000000000000),(-753366983/4000000000000),(-37751023/100000000000000),(65503/12500000000000),(72421/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((15/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(2322495023223/100000000000000),(9417087287/12500000000000),(15100409/10000000000000),(-1048049/50000000000000),(6069/2000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((15/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((15/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(1685619729/3125000000000),(3499382137/100000000000000),(31885153/50000000000000),(130159/100000000000000),(4373/25000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((15/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((15/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(644772476139/100000000000000),(10437191679/25000000000000),(756846007/100000000000000),(145147/10000000000000),(209713/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((15/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-325134328442551/100000000000000),(-2636420599529/25000000000000),(-10545284557/50000000000000),(14705357/5000000000000),(21243789/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((15/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-164462458774827/25000000000000),(-21584143939817/100000000000000),(-12801676921/25000000000000),(568739847/100000000000000),(87415197/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((15/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(109860256782549/12500000000000),(14003867914821/50000000000000),(7938627971/20000000000000),(-425584991/50000000000000),(117799381/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((15/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(2459031766354347/100000000000000),(20104033050789/25000000000000),(181903416987/100000000000000),(-1083448591/50000000000000),(20335619/6250000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((15/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(1276420777585127/50000000000000),(17308792246603/20000000000000),(147797942497/50000000000000),(-29495299/1562500000000),(35574121/10000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((15/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(52349464938887/50000000000000),(154172778729/100000000000000),(182889243/50000000000000),(-4062037/100000000000000),(78049/12500000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((15/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((15/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((15/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((15/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(54949148741585187/100000000000000),(39880205666977/50000000000000),(42310137481/25000000000000),(-552451893/25000000000000),(66715341/20000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((15/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(90993220359/50000000000000),(-132079511/50000000000000),(-88537/50000000000000),(8389/100000000000000),(283/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((15/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(145182046357/3125000000000),(75377356709/50000000000000),(304810329/100000000000000),(-4155289/100000000000000),(689977/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((15/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((15/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((15/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (15/8) (1/40))

def c175 : Certificate := ⟨(5833861762841/25000000000000),(-257988869/500000000000),(-227569/781250000000),(1626461/100000000000000),(203309/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((15/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(2219403931513/100000000000000),(17199257933/25000000000000),(19419221/50000000000000),(-271077/12500000000000),(309751/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((15/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((15/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(769649033/1562500000000),(1526884027/50000000000000),(49054279/100000000000000),(-21411/50000000000000),(4287/25000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((15/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((15/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(588904009869/100000000000000),(36441890303/100000000000000),(582233857/100000000000000),(-115939/20000000000000),(2569/1250000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((15/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-310703480253073/100000000000000),(-1203796312657/12500000000000),(-5399160099/100000000000000),(75998829/25000000000000),(5421139/12500000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((15/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-25133154643189/4000000000000),(-19690660478387/100000000000000),(-17740674373/100000000000000),(613242581/100000000000000),(89131059/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((15/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(8405253580759/1000000000000),(25617570314643/100000000000000),(153687973/20000000000000),(-827533393/100000000000000),(1503139/1250000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((15/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(46980575618623/2000000000000),(9172962147329/12500000000000),(7343499227/12500000000000),(-575790687/25000000000000),(82949501/25000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((15/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(486928600464273/20000000000000),(39363184395383/50000000000000),(73092168949/50000000000000),(-585831669/25000000000000),(90435287/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((15/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(52244032700569/50000000000000),(70323915759/50000000000000),(126731163/100000000000000),(-2190027/50000000000000),(12733/2000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((15/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((15/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((15/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((15/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(54840021837276651/100000000000000),(18203294789609/25000000000000),(49015655223/100000000000000),(-72115829/3125000000000),(339842561/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((15/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(22793572251/12500000000000),(-242111131/100000000000000),(79239/50000000000000),(7679/100000000000000),(289/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((15/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(138735527947/3125000000000),(68830936149/50000000000000),(79818133/100000000000000),(-134851/3125000000000),(701523/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((15/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((15/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(11474243453973/100000000000000),(19037340931/6250000000000),(-783100151/100000000000000),(466849/100000000000000),(31506507/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((15/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1223919301757/20000000000000),(80857355827/100000000000000),(-373937873/25000000000000),(20192339/100000000000000),(8847731/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((15/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((15/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((15/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((15/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((15/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((15/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (15/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((15/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((15/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((15/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (15/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((15/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(38523815543/100000000000000),(-157776719/100000000000000),(2399259/100000000000000),(-17007/100000000000000),(91/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((15/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(460329499007957/100000000000000),(-268713474583/20000000000000),(-29169563/800000000000),(-23108861/50000000000000),(4304329/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((15/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((15/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((15/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((15/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (15/8) (1/40))

def c223 : Certificate := ⟨(961/64),(31/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((15/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3583569/4096),(99603/5120),(7739/51200),(59/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((15/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((15/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(33606385213/25000000000000),(-1168917747/50000000000000),(15246753/50000000000000),(-88387/25000000000000),(3941/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((15/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(117608203370473/100000000000000),(35607222183/6250000000000),(758884361/50000000000000),(-7512989/100000000000000),(3482231/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((15/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((15/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (15/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((15/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (15/8) (1/40))

def c231 : Certificate := ⟨(23945889758129/100000000000000),(-32667811029/100000000000000),(-42463157/100000000000000),(607457/100000000000000),(401709/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((15/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(105411024187/2500000000000),(26134248823/20000000000000),(1358821/800000000000),(-2429831/100000000000000),(874147/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((15/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((15/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(88891872161/50000000000000),(11019351739/100000000000000),(185073211/100000000000000),(14937/6250000000000),(158079/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((15/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((15/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(423682527721/20000000000000),(32709586871/25000000000000),(2175869337/100000000000000),(2335281/100000000000000),(1891369/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((15/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-295106206914423/50000000000000),(-9142844649133/50000000000000),(-11756528489/50000000000000),(343288799/100000000000000),(61203073/25000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((15/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1205489428906233/100000000000000),(-3813019155103/10000000000000),(-73446778147/100000000000000),(323692443/50000000000000),(511657883/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((15/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(393125255585189/25000000000000),(5890682991539/12500000000000),(10423669459/100000000000000),(-129954491/12500000000000),(676579443/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((15/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(4493566593174017/100000000000000),(3531165758443/2500000000000),(243035128399/100000000000000),(-2539702727/100000000000000),(379185099/20000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((15/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(4806200181325169/100000000000000),(20107445829889/12500000000000),(583242461583/100000000000000),(-1868888561/100000000000000),(1087658309/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((15/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(54305332839641/50000000000000),(272361839969/100000000000000),(524778461/100000000000000),(-462067/10000000000000),(3654667/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((15/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((15/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((15/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((15/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(56959775467547081/100000000000000),(69533728991033/50000000000000),(101221476603/50000000000000),(-2682026127/100000000000000),(1971353821/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((15/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(10972655613/6250000000000),(-107159083/25000000000000),(422543/100000000000000),(4379/50000000000000),(769/12500000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((15/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(8437884703491/100000000000000),(6545198503/2500000000000),(354760703/100000000000000),(-4680429/100000000000000),(32489/781250000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((15/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((15/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((15/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (15/8) (1/40))

def c259 : Certificate := ⟨(5520901347179/25000000000000),(-83352626279/100000000000000),(92548959/100000000000000),(794007/50000000000000),(207561/20000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((15/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(3888526148377/100000000000000),(55568417519/50000000000000),(-61699307/50000000000000),(-2117353/100000000000000),(874609/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((15/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((15/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(75603178033/50000000000000),(8643169781/100000000000000),(56958593/50000000000000),(-438951/100000000000000),(36123/25000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((15/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((15/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(450679218851/25000000000000),(102709761621/100000000000000),(267861703/20000000000000),(-5458749/100000000000000),(1730213/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((15/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-544323561655699/100000000000000),(-15553159526903/100000000000000),(4359952293/25000000000000),(297540707/100000000000000),(24493993/10000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((15/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-1109953485572319/100000000000000),(-32328046464533/100000000000000),(2327020243/12500000000000),(327264237/50000000000000),(102002223/20000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((15/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(1453921735603843/100000000000000),(20148514887669/50000000000000),(-81343272519/100000000000000),(-705645987/100000000000000),(676388791/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((15/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(2069744291330871/50000000000000),(29969119982653/25000000000000),(-44870437443/50000000000000),(-48431457/2000000000000),(1891411309/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((15/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(2202441323843807/50000000000000),(13521752652067/10000000000000),(14961246119/12500000000000),(-1541082487/50000000000000),(1073622797/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((15/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(5396412932641/5000000000000),(230916839857/100000000000000),(-66440021/50000000000000),(-4673657/100000000000000),(227683/6250000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((15/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((15/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((15/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((15/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(28305464780401029/50000000000000),(118182902098443/100000000000000),(-28678638183/25000000000000),(-1190728069/50000000000000),(1960626977/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((15/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(88322167447/50000000000000),(-184384361/50000000000000),(5639/500000000000),(4329/100000000000000),(6167/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((15/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(7780975655869/100000000000000),(222610270937/100000000000000),(-237536129/100000000000000),(-4170179/100000000000000),(4099527/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((15/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((15/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(37330099318521/50000000000000),(1006004304007/50000000000000),(-262409483/4000000000000),(-67475773/100000000000000),(9738577/25000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((15/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(19909386303211/50000000000000),(542154289521/100000000000000),(-1340939621/12500000000000),(107046479/100000000000000),(25054087/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((15/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((15/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((15/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((15/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((15/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((15/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (15/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((15/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(25133695167531179/2500000000000),(257341588746053/6250000000000),(-45749615777077/100000000000000),0,(130329/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((15/8)+(1/40)*x)) := (SharedCertificates.h297 (15/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4973403201/50000000000000),(-20368887/50000000000000),(309743/50000000000000),(-4391/100000000000000),(3/6250000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((15/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(624667212988101/100000000000000),(90747632211/10000000000000),(7613563141/100000000000000),(10111971/100000000000000),(2816763/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((15/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((15/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (15/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((15/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (15/8) (1/40))

def c307 : Certificate := ⟨(2776386042793027/100000000000000),(11091229182759/50000000000000),0,0,(1047/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((15/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (15/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((15/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (15/8) (1/40))

def c311 : Certificate := ⟨(1049306978603357/50000000000000),(2817541634481/100000000000000),0,0,(1047/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((15/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (15/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(1191262447967/25000000000000),(-3198712687/50000000000000),(536813/6250000000000),(-2883/25000000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((15/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(132296177353561/100000000000000),(175877592199/20000000000000),(-1180642201/100000000000000),(39627/2500000000000),(317/10000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((15/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((15/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (15/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((15/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (15/8) (1/40))

def c316 : Certificate := ⟨(5783072187463/25000000000000),(-4705629451/10000000000000),(39724903/25000000000000),(-536571/100000000000000),(469/25000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((15/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(747084500059/10000000000000),(188225178037/100000000000000),(-158899613/25000000000000),(2146283/100000000000000),(8709/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((15/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((15/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(139533812557/25000000000000),(14062011303/50000000000000),(129659013/50000000000000),(-1036011/50000000000000),(13483/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((15/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((15/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(6614228163859/100000000000000),(331184964861/100000000000000),(2974291831/100000000000000),(-629933/2500000000000),(21233/12500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((15/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1045424161348493/100000000000000),(-26314332967053/100000000000000),(8978732157/10000000000000),(-149363377/50000000000000),(51647/4000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((15/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-271242327357283/12500000000000),(-3539794023013/6250000000000),(70894968947/50000000000000),(-12378343/4000000000000),(866469/20000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((15/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(542832514880861/20000000000000),(32075541159407/50000000000000),(-65384987779/20000000000000),(69174657/5000000000000),(387817/6250000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((15/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(2011789532404317/25000000000000),(8301512088119/4000000000000),(-294152558227/50000000000000),(1392111053/100000000000000),(15936451/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((15/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(4523384336125833/50000000000000),(129469823706031/50000000000000),(-15259906197/20000000000000),(-2045859181/100000000000000),(34694561/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((15/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(7218739078213/6250000000000),(10114359467/2500000000000),(-505939439/50000000000000),(4337/195312500000),(30901/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((15/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((15/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((15/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((15/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(60434345006805047/100000000000000),(201458049013913/100000000000000),(-26385806167/4000000000000),(837449797/50000000000000),(24373007/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((15/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(165468824041/100000000000000),(-551590763/100000000000000),(3644833/100000000000000),(-22757/100000000000000),(201/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((15/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(3742395433921/25000000000000),(189281624601/50000000000000),(-76549969/6250000000000),(2207373/50000000000000),(126789/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((15/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((15/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((15/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (15/8) (1/40))

def c344 : Certificate := ⟨(20125238066027/100000000000000),(-53426143669/50000000000000),(71077503/10000000000000),(-4728031/100000000000000),(31791/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((15/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(649968257863/10000000000000),(142469716449/100000000000000),(-947700041/100000000000000),(6304041/100000000000000),(62921/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((15/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((15/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(422458736229/100000000000000),(18520158679/100000000000000),(19945303/25000000000000),(-940443/50000000000000),(17713/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((15/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((15/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((15/8)+(1/40)*x)) := (SharedCertificates.h144 (15/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(2507293940493/50000000000000),(109315324783/50000000000000),(902239541/100000000000000),(-2225569/10000000000000),(106437/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((15/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((15/8)+(1/40)*x)) := (SharedCertificates.h148 (15/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-90962962871331/10000000000000),(-4981101433871/25000000000000),(133000607661/100000000000000),(-884482713/100000000000000),(8860953/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((15/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((15/8)+(1/40)*x)) := (SharedCertificates.h151 (15/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-58719817516373/3125000000000),(-42482490486969/100000000000000),(127117472407/50000000000000),(-375413571/25000000000000),(903397/4000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((15/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((15/8)+(1/40)*x)) := (SharedCertificates.h154 (15/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(2380246536794469/100000000000000),(49412559159237/100000000000000),(-97764281899/25000000000000),(2975812323/100000000000000),(15913383/50000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((15/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((15/8)+(1/40)*x)) := (SharedCertificates.h157 (15/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(3489687588520987/50000000000000),(19524499032817/12500000000000),(-486331089763/50000000000000),(2968646149/50000000000000),(80824061/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((15/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((15/8)+(1/40)*x)) := (SharedCertificates.h160 (15/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(7731941172520347/100000000000000),(189784681715949/100000000000000),(-40437402989/5000000000000),(2538981637/100000000000000),(141069051/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((15/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((15/8)+(1/40)*x)) := (SharedCertificates.h41 (15/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(113421823893489/100000000000000),(303459591577/100000000000000),(-181561887/10000000000000),(2681799/25000000000000),(40317/25000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((15/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((15/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((15/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((15/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((15/8)+(1/40)*x)) := (SharedCertificates.h167 (15/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(11879104403375161/20000000000000),(38073899795749/25000000000000),(-249247822409/25000000000000),(631916113/10000000000000),(49396749/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((15/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(168362860707/100000000000000),(-431697911/100000000000000),(393299/10000000000000),(-8811/25000000000000),(61/12500000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((15/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(13017717346237/100000000000000),(286148290799/100000000000000),(-1876831403/100000000000000),(12505217/100000000000000),(386829/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((15/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((15/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(2185343514571/1250000000000),(4406213163701/100000000000000),(-5605970411/50000000000000),(26197039/20000000000000),(4843761/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((15/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(46620661644181/50000000000000),(1106762710127/100000000000000),(-5184134477/25000000000000),(346345941/100000000000000),(530881/4000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((15/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((15/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(3553390502929687/100000000000000),(55103302001953/25000000000000),(891/16384),(273/409600),(406250001/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((15/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1521/64),(39/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((15/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(59319/512),(4563/2560),(117/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((15/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(41168666258454317/10000000000000),(3983768373727791/12500000000000),(211081824302673/20000000000000),(19485403060913/100000000000000),(3444407191/1562500000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((15/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(607257953/2500000000000),(-1880400993/100000000000000),(83297409/100000000000000),(-173587/6250000000000),(117217/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((15/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2812340651479/50000000000000),(420052233/2000000000000),(-176035733/12500000000000),(31457627/100000000000000),(26749043/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((15/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((15/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((15/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel17

namespace Hf4Quad.Panel18
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(77/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((77/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (77/40) (1/40)

def c3 : Certificate := ⟨(337333333333333/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((77/40)+(1/40)*x)) := (SharedCertificates.h2 (77/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((77/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-122952380952381/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((77/40)+(1/40)*x)) := (SharedCertificates.h4 (77/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(5929/1600),(77/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((77/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(56074537037037/12500000000000),(11651851851851/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((77/40)+(1/40)*x)) := (SharedCertificates.h8 (77/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((77/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((77/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(456533/64000),(17787/64000),(231/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((77/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(347485548755787/5000000000000),(67691990017361/25000000000000),(13736199273/390625000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((77/40)+(1/40)*x)) := (SharedCertificates.h13 (77/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((77/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((77/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(35153041/2560000),(456533/640000),(17787/1280000),(77/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((77/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(1918072673611111/50000000000000),(199280277777777/100000000000000),(3882083333333/100000000000000),(33611111111/100000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((77/40)+(1/40)*x)) := (SharedCertificates.h18 (77/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((77/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(330417987915039/12500000000000),(42911427001953/25000000000000),(456533/10240000),(5929/10240000),(188476563/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((77/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(4305224005500397/25000000000000),(1118240001428671/100000000000000),(29045194842303/100000000000000),(377210322627/100000000000000),(2455779811/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((77/40)+(1/40)*x)) := (SharedCertificates.h22 (77/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((77/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(12721092534729/250000000000),(79300317099609/20000000000000),(2574685620117/20000000000000),(111458251953/50000000000000),(545642091/25000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((77/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(11426098776167169/100000000000000),(890345359181853/100000000000000),(28907316856551/100000000000000),(500559599247/100000000000000),(2450481519/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((77/40)+(1/40)*x)) := (SharedCertificates.h26 (77/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((77/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(979524125174133/10000000000000),(445238238715513/50000000000000),(34693888731077/100000000000000),(750949972533/100000000000000),(9828920909/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((77/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(581106574260051/25000000000000),(52827870387277/25000000000000),(8232914865549/100000000000000),(89100810233/50000000000000),(466483707/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((77/40)+(1/40)*x)) := (SharedCertificates.h30 (77/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((77/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((77/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((77/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((77/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((77/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (77/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((77/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((77/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (77/40) (1/40))

def c43 : Certificate := ⟨(13689/1600),(117/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((77/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((77/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(13914543829/25000000000000),(-951421801/100000000000000),(2439543/20000000000000),(-69503/50000000000000),(381/25000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((77/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1042656599488681/100000000000000),(92383063611/50000000000000),(-401912847/25000000000000),(13997103/100000000000000),(1778753/3125000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((77/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((77/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (77/40) (1/40))

def c52 : Certificate := ⟨(32708333333333/25000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((77/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (77/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((77/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (77/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((77/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (77/40) (1/40))

def c56 : Certificate := ⟨(2321083172147/10000000000000),(-44895225767/100000000000000),(2170949/2500000000000),(-83983/50000000000000),(41/12500000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((77/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(7156673114119/100000000000000),(179580903067/100000000000000),(-86837961/25000000000000),(33593/5000000000000),(1507/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((77/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((77/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((77/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((77/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((77/40)+(1/40)*x)) := (SharedCertificates.h61 (77/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-1613539090647/1562500000000),(-2668356861433/100000000000000),(3226273803/100000000000000),(-2497703/100000000000000),(44173/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((77/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((77/40)+(1/40)*x)) := (SharedCertificates.h61 (77/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-107583869567979/100000000000000),(-289054513753/10000000000000),(132131687/20000000000000),(4783759/100000000000000),(59587/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((77/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((77/40)+(1/40)*x)) := (SharedCertificates.h67 (77/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-508666543856831/100000000000000),(-3242682541481/25000000000000),(19544737737/100000000000000),(-36183877/100000000000000),(62333/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((77/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((77/40)+(1/40)*x)) := (SharedCertificates.h67 (77/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-537370719773051/100000000000000),(-7206201973119/50000000000000),(1046822581/25000000000000),(13557699/50000000000000),(342771/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((77/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((77/40)+(1/40)*x)) := (SharedCertificates.h72 (77/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(712992811157349/100000000000000),(1685953099233/10000000000000),(-15046907749/25000000000000),(63228403/50000000000000),(59563/25000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((77/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((77/40)+(1/40)*x)) := (SharedCertificates.h72 (77/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(401238620902097/25000000000000),(42685950545617/100000000000000),(-6489735647/25000000000000),(-164523339/100000000000000),(58959/4000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((77/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((77/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((77/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(114825525928861/100000000000000),(384865842549/100000000000000),(-421928353/100000000000000),(19233/10000000000000),(3431/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((77/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2798455757647317/25000000000000),(3173468252963/20000000000000),(-14364615173/20000000000000),(78836107/50000000000000),(328643/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((77/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(446674919403/50000000000000),(-316582787/25000000000000),(7527047/100000000000000),(-31379/100000000000000),(219/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((77/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(573514331689/4000000000000),(180505415927/50000000000000),(-325821991/50000000000000),(156833/10000000000000),(30067/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((77/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((77/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((77/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (77/40) (1/40))

def c87 : Certificate := ⟨(10152284263959/50000000000000),(-103068875777/100000000000000),(261596131/50000000000000),(-2655799/100000000000000),(6777/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((77/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(6260575296107/100000000000000),(137425167701/100000000000000),(-139517937/20000000000000),(442633/12500000000000),(6607/25000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((77/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((77/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((77/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((77/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((77/40)+(1/40)*x)) := (SharedCertificates.h61 (77/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-5624983895487/6250000000000),(-2027195621011/100000000000000),(2289298129/25000000000000),(-40731223/100000000000000),(239089/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((77/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((77/40)+(1/40)*x)) := (SharedCertificates.h61 (77/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-11660319472529/12500000000000),(-543637188223/25000000000000),(8181500459/100000000000000),(-28586059/100000000000000),(154291/25000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((77/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((77/40)+(1/40)*x)) := (SharedCertificates.h67 (77/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-88816059074049/20000000000000),(-9884094709813/100000000000000),(47005839163/100000000000000),(-226554459/100000000000000),(2088533/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((77/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((77/40)+(1/40)*x)) := (SharedCertificates.h67 (77/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-466042251994319/100000000000000),(-10848841021357/100000000000000),(41288738507/100000000000000),(-72117491/50000000000000),(1548047/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((77/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((77/40)+(1/40)*x)) := (SharedCertificates.h72 (77/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(628183479993457/100000000000000),(13109983401347/100000000000000),(-20579994913/25000000000000),(478700439/100000000000000),(931411/25000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((77/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((77/40)+(1/40)*x)) := (SharedCertificates.h72 (77/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1393376611707861/100000000000000),(4028421297901/12500000000000),(-129532695439/100000000000000),(109721619/25000000000000),(1221363/12500000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((77/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((77/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((77/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(28228274655649/25000000000000),(292057547601/100000000000000),(-646834429/50000000000000),(2804091/50000000000000),(8861/12500000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((77/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5556814675868443/50000000000000),(778325951727/6250000000000),(-86768660017/100000000000000),(532763949/100000000000000),(6490301/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((77/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(112474508591/12500000000000),(-504126679/50000000000000),(407743/5000000000000),(-3759/6250000000000),(309/25000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((77/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(6268773987361/50000000000000),(55186369057/20000000000000),(-688417867/50000000000000),(1409033/20000000000000),(140127/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((77/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((77/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-140109098540859/50000000000000),(-51495845397/781250000000),(21894869103/100000000000000),(-100035157/100000000000000),(17574177/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((77/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(51948051948051/100000000000000),(-6746500253/1000000000000),(27380277/312500000000),(-22757633/20000000000000),(11697/781250000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((77/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-145567894587903/100000000000000),(-1533647192787/100000000000000),(15645726993/50000000000000),(-458348833/100000000000000),(23671409/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((77/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((77/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((77/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((77/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((77/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((77/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((77/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((77/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((77/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((77/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (77/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((77/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((77/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(3853144183/50000000000000),(-400326669/100000000000000),(12997619/100000000000000),(-337601/100000000000000),(8823/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((77/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(12500751241791/10000000000000),(-62988139637/10000000000000),(1621749441/25000000000000),(-12550107/20000000000000),(140488957/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((77/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((77/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (77/40) (1/40))

def c134 : Certificate := ⟨(30929/1600),(177/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((77/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((77/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1139601139601/20000000000000),(-24350451701/50000000000000),(416247037/100000000000000),(-3557667/100000000000000),(1917/6250000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((77/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(110146011395997/100000000000000),(159632429929/50000000000000),(832494063/100000000000000),(-1423067/20000000000000),(28223/2500000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((77/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((77/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (77/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((77/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (77/40) (1/40))

def c140 : Certificate := ⟨(12190780505171/50000000000000),(-151832283/800000000000),(-34714871/100000000000000),(488523/100000000000000),(33929/50000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((77/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(2473755958631/100000000000000),(37958070749/50000000000000),(69429741/50000000000000),(-122131/6250000000000),(57039/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((77/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((77/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(15298671357/25000000000000),(3755960147/100000000000000),(32251347/50000000000000),(57077/50000000000000),(17327/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((77/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((77/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(731308610781/100000000000000),(447927819/1000000000000),(38248417/5000000000000),(78639/6250000000000),(103837/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((77/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-69261548683601/20000000000000),(-10626596564329/100000000000000),(-4846595897/25000000000000),(34279151/12500000000000),(39931797/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((77/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-175304619213671/25000000000000),(-10891149580831/50000000000000),(-47908410003/100000000000000),(265612247/50000000000000),(82280491/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((77/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(5844060063867/625000000000),(1759783471387/6250000000000),(1390630961/4000000000000),(-158420057/20000000000000),(110724587/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((77/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(2620574602011491/100000000000000),(81118326133789/100000000000000),(84668118457/50000000000000),(-1012088171/50000000000000),(306130197/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((77/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2727096997297809/100000000000000),(877041656713/1000000000000),(142311012867/50000000000000),(-442994051/25000000000000),(67252613/20000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((77/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(10500870660269/10000000000000),(155588243143/100000000000000),(171110829/50000000000000),(-1897019/50000000000000),(587717/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((77/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((77/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((77/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((77/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(13777332286473457/25000000000000),(80411449124423/100000000000000),(156423560401/100000000000000),(-1032280023/50000000000000),(39283293/12500000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((77/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(181457480157/100000000000000),(-66192327/25000000000000),(-64361/50000000000000),(7737/100000000000000),(1061/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((77/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4948521492733/100000000000000),(151925253171/100000000000000),(280743869/100000000000000),(-30967/800000000000),(81509/12500000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((77/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((77/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((77/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (77/40) (1/40))

def c175 : Certificate := ⟨(11616073866317/50000000000000),(-2067812173/4000000000000),(-790673/4000000000000),(1496043/100000000000000),(37883/20000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((77/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(2357136356487/100000000000000),(4307942027/6250000000000),(5271153/20000000000000),(-997363/50000000000000),(72747/25000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((77/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((77/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(5556091803/10000000000000),(3249410167/100000000000000),(9750379/20000000000000),(-11541/20000000000000),(8433/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((77/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((77/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(332055861581/50000000000000),(19381571459/50000000000000),(578215709/100000000000000),(-756443/100000000000000),(4043/2000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((77/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-164991717944653/50000000000000),(-9648418687577/100000000000000),(-912321109/25000000000000),(11185573/4000000000000),(20371281/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((77/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-166944084838523/25000000000000),(-987722729377/5000000000000),(-14202975007/100000000000000),(283319383/50000000000000),(8383779/10000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((77/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(891757098372561/100000000000000),(25611004774101/100000000000000),(-994994687/25000000000000),(-378144443/50000000000000),(14120007/12500000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((77/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(2496013105088643/100000000000000),(4599485901219/6250000000000),(2273384247/5000000000000),(-1063035239/50000000000000),(311980703/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((77/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1296331019518399/50000000000000),(15856720103153/20000000000000),(132582021927/100000000000000),(-2192797867/100000000000000),(341475879/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((77/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(26192458407751/25000000000000),(141103555031/100000000000000),(4058537/4000000000000),(-4047157/100000000000000),(299421/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((77/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((77/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((77/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((77/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(27492913082820587/50000000000000),(18245571093369/25000000000000),(35716911859/100000000000000),(-1063856307/50000000000000),(39989913/12500000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((77/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(181865049547/100000000000000),(-241388149/100000000000000),(202259/100000000000000),(277/4000000000000),(541/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((77/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(117878652547/2500000000000),(68965390227/50000000000000),(13745759/25000000000000),(-3968071/100000000000000),(330911/50000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((77/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((77/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(12080310468361/100000000000000),(150736086421/50000000000000),(-779183479/100000000000000),(412499/50000000000000),(14865229/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((77/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(627548595759/10000000000000),(3004364133/4000000000000),(-1380213539/100000000000000),(18353421/100000000000000),(406271/2500000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((77/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((77/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((77/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((77/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((77/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((77/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (77/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((77/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((77/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((77/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (77/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((77/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(19108862953/50000000000000),(-18547269/12500000000000),(2301397/100000000000000),(-7817/50000000000000),(169/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((77/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(91525482025197/20000000000000),(-42459564771/3125000000000),(-3923053293/100000000000000),(-1844519/4000000000000),(2003401/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((77/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((77/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((77/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((77/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (77/40) (1/40))

def c223 : Certificate := ⟨(24649/1600),(157/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((77/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2340890881/2560000),(12840873/640000),(197027/1280000),(297/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((77/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((77/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(64934537869/50000000000000),(-2219984201/100000000000000),(5692267/20000000000000),(-162173/50000000000000),(111/3125000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((77/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(29688411632713/25000000000000),(287849308717/50000000000000),(368571053/25000000000000),(-1397987/20000000000000),(1641287/25000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((77/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((77/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (77/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((77/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (77/40) (1/40))

def c231 : Certificate := ⟨(373131079083/1562500000000),(-16415268357/50000000000000),(-38939329/100000000000000),(113547/20000000000000),(376623/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((77/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(17913775019/400000000000),(65661073427/50000000000000),(31151463/20000000000000),(-1135471/50000000000000),(411937/25000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((77/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((77/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(50141146161/25000000000000),(1470297121/12500000000000),(18640607/10000000000000),(205681/100000000000000),(39413/25000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((77/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((77/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(2388810671497/100000000000000),(27913641861/20000000000000),(1094329329/50000000000000),(241579/12500000000000),(942859/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((77/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-62687514412267/10000000000000),(-18375713038349/100000000000000),(-21521001537/100000000000000),(80263941/25000000000000),(230737451/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((77/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-641019251036021/50000000000000),(-38416372989433/100000000000000),(-8710454863/12500000000000),(303797337/50000000000000),(483445129/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((77/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(833392736174607/50000000000000),(47154970397427/100000000000000),(4399749199/100000000000000),(-121166737/12500000000000),(637743167/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((77/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(4777011992379003/100000000000000),(142188921489257/100000000000000),(14266455051/6250000000000),(-298315843/12500000000000),(895057493/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((77/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1282559383240053/25000000000000),(81585252676597/50000000000000),(572322645847/100000000000000),(-354550837/20000000000000),(1034666989/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((77/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(1705585188971/1562500000000),(68601667669/25000000000000),(4979207/1000000000000),(-4336203/100000000000000),(863287/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((77/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((77/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((77/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((77/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(57238699024449413/100000000000000),(69922845959937/50000000000000),(5838488747/3125000000000),(-252406421/10000000000000),(18655073/1000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((77/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(174706975707/100000000000000),(-106711099/25000000000000),(472609/100000000000000),(3971/50000000000000),(1441/25000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((77/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(448144142021/5000000000000),(263172123737/100000000000000),(20478087/6250000000000),(-4361451/100000000000000),(3952529/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((77/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((77/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((77/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (77/40) (1/40))

def c259 : Certificate := ⟨(2739660338043/12500000000000),(-16592806777/20000000000000),(20317289/20000000000000),(142701/10000000000000),(24089/2500000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((77/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(205514486377/5000000000000),(22123742369/20000000000000),(-27089719/20000000000000),(-951341/50000000000000),(411537/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((77/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((77/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(168944816443/100000000000000),(9093499099/100000000000000),(55615167/50000000000000),(-18243/4000000000000),(143003/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((77/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((77/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(402689910889/20000000000000),(108000681709/100000000000000),(1305959673/100000000000000),(-5650429/100000000000000),(13697/800000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((77/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-115071560649079/20000000000000),(-7739976632707/50000000000000),(95666119/500000000000),(267403271/100000000000000),(230511739/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((77/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-293632499098649/25000000000000),(-32245963635947/100000000000000),(2795953337/12500000000000),(596821543/100000000000000),(60117873/12500000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((77/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(191773119914277/12500000000000),(7992710315441/20000000000000),(-85307520031/100000000000000),(-30861721/5000000000000),(63650919/10000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((77/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(875772732140231/20000000000000),(119489360831801/100000000000000),(-103598276993/100000000000000),(-2200873033/100000000000000),(356513413/20000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((77/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(4675772180374563/100000000000000),(33915012608657/25000000000000),(25438890363/25000000000000),(-1449131899/50000000000000),(127261843/6250000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((77/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(108389524271523/100000000000000),(230330922789/100000000000000),(-19958357/12500000000000),(-4261439/100000000000000),(3435299/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((77/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((77/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((77/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((77/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(2273872716818401/4000000000000),(117696391705381/100000000000000),(-25662977427/20000000000000),(-2155400063/100000000000000),(925621251/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((77/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(175911341493/100000000000000),(-364209131/100000000000000),(1151131/100000000000000),(433/12500000000000),(1443/25000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((77/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(8225213567653/100000000000000),(221611825363/100000000000000),(-52252491/20000000000000),(-749077/20000000000000),(3883509/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((77/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((77/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(78657440442221/100000000000000),(1984968521299/100000000000000),(-3478641159/50000000000000),(-64945383/100000000000000),(36791057/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((77/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(10215252005483/25000000000000),(500490036753/100000000000000),(-10114043241/100000000000000),(24403337/25000000000000),(11501797/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((77/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((77/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((77/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((77/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((77/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((77/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (77/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((77/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(126674967384751569/12500000000000),(30738023100223/781250000000),(-45749615777077/100000000000000),0,(26269/20000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((77/40)+(1/40)*x)) := (SharedCertificates.h297 (77/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9867774397/100000000000000),(-19155537/50000000000000),(297109/50000000000000),(-4037/100000000000000),(9/20000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((77/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(626512705664277/100000000000000),(117257709211/12500000000000),(3840750797/50000000000000),(624873/5000000000000),(2639837/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((77/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((77/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (77/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((77/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (77/40) (1/40))

def c307 : Certificate := ⟨(88148467485127/3125000000000),(11091229182759/50000000000000),0,0,(21/2000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((77/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (77/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((77/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (77/40) (1/40))

def c311 : Certificate := ⟨(2104249040475677/100000000000000),(2817541634481/100000000000000),0,0,(1049/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((77/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (77/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(95045784103/2000000000000),(-795400903/12500000000000),(8520189/100000000000000),(-11409/100000000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((77/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(134050243353627/100000000000000),(874684345513/100000000000000),(-1171182481/100000000000000),(1568167/100000000000000),(3153/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((77/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((77/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (77/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((77/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (77/40) (1/40))

def c316 : Certificate := ⟨(23038807495501/100000000000000),(-11606769357/25000000000000),(155723183/100000000000000),(-261159/50000000000000),(1817/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((77/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(7844770017991/100000000000000),(185708309709/100000000000000),(-622892733/100000000000000),(522317/25000000000000),(4247/50000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((77/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((77/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(615404166351/100000000000000),(29136779601/100000000000000),(123573379/50000000000000),(-1985731/100000000000000),(13033/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((77/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((77/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(7288295913149/100000000000000),(8569605379/2500000000000),(70660817/2500000000000),(-12048949/50000000000000),(20473/12500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((77/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1097696052466123/100000000000000),(-3244842219347/12500000000000),(88017890269/100000000000000),(-291121931/100000000000000),(314283/25000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((77/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1141323667925007/50000000000000),(-56073242779733/100000000000000),(139944702141/100000000000000),(-9550471/3125000000000),(1052409/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((77/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1420584011553651/50000000000000),(785747706453/1250000000000),(-7968739729/2500000000000),(268373571/20000000000000),(6034771/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((77/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(8459891616128019/100000000000000),(41040243669117/20000000000000),(-580004068263/100000000000000),(687431879/50000000000000),(96599/625000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((77/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(239108165025091/2500000000000),(32326286993519/12500000000000),(-68967197/78125000000),(-1947657641/100000000000000),(33821283/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((77/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(116304944202333/100000000000000),(400553399019/100000000000000),(-249659677/25000000000000),(438561/20000000000000),(30021/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((77/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((77/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((77/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((77/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(12166927176490483/20000000000000),(12427467822033/6250000000000),(-649657399387/100000000000000),(1654285543/100000000000000),(23586517/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((77/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(20547505247/12500000000000),(-537280161/100000000000000),(3511539/100000000000000),(-10843/50000000000000),(191/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((77/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(15721844081451/100000000000000),(373716483673/100000000000000),(-119871819/10000000000000),(4279821/100000000000000),(12331/10000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((77/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((77/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((77/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (77/40) (1/40))

def c344 : Certificate := ⟨(3982867852761/20000000000000),(-10406493367/10000000000000),(683145239/100000000000000),(-4484577/100000000000000),(29763/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((77/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(847610122699/12500000000000),(34688311223/25000000000000),(-910860321/100000000000000),(1195887/20000000000000),(59951/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((77/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((77/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(91960693773/20000000000000),(4704346197/25000000000000),(68995921/100000000000000),(-85839/5000000000000),(33299/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((77/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((77/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((77/40)+(1/40)*x)) := (SharedCertificates.h144 (77/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(2727642087217/50000000000000),(221980664057/100000000000000),(38737543/5000000000000),(-2027219/10000000000000),(399551/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((77/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((77/40)+(1/40)*x)) := (SharedCertificates.h148 (77/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-189790684219161/20000000000000),(-19402832656439/100000000000000),(127831295229/100000000000000),(-20977907/2500000000000),(8439801/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((77/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((77/40)+(1/40)*x)) := (SharedCertificates.h151 (77/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-1962994076901013/100000000000000),(-8296659044707/20000000000000),(61357639533/25000000000000),(-358445139/25000000000000),(10727581/50000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((77/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((77/40)+(1/40)*x)) := (SharedCertificates.h154 (77/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(2477530885882561/100000000000000),(47883348428331/100000000000000),(-373718153607/100000000000000),(1402940653/50000000000000),(30147371/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((77/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((77/40)+(1/40)*x)) := (SharedCertificates.h157 (77/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(3643961725662739/50000000000000),(152375474500889/100000000000000),(-468935933163/50000000000000),(1415529021/25000000000000),(76757681/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((77/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((77/40)+(1/40)*x)) := (SharedCertificates.h160 (77/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(324331834447977/4000000000000),(932900834133/500000000000),(-198377265597/25000000000000),(2539331979/100000000000000),(66865687/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((77/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((77/40)+(1/40)*x)) := (SharedCertificates.h41 (77/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(114021565432049/100000000000000),(74080968643/25000000000000),(-1752724721/100000000000000),(1024209/10000000000000),(153201/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((77/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((77/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((77/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((77/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((77/40)+(1/40)*x)) := (SharedCertificates.h167 (77/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(29848087595597921/50000000000000),(18547780392369/12500000000000),(-191997502967/20000000000000),(6018365277/100000000000000),(93597021/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((77/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(1308710311/781250000000),(-208189549/50000000000000),(1864403/50000000000000),(-32853/100000000000000),(451/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((77/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(13582605309683/100000000000000),(278788367667/100000000000000),(-1803784263/100000000000000),(11851159/100000000000000),(363813/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((77/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((77/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(45899024690103/25000000000000),(545364950893/12500000000000),(-65244623/625000000000),(31670449/25000000000000),(232069/5000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((77/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(95374596758653/100000000000000),(1027820617233/100000000000000),(-18771249409/100000000000000),(309591183/100000000000000),(12014057/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((77/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((77/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1004127391845703/25000000000000),(60744747314453/25000000000000),(598829/10240000),(7161/10240000),(208007813/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((77/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(38809/1600),(197/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((77/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(7645373/64000),(116427/64000),(591/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((77/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(479808028136097367/100000000000000),(36332736928760071/100000000000000),(73606201501171/6250000000000),(10649442312561/50000000000000),(236211971361/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((77/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(20841668779/100000000000000),(-1578203833/100000000000000),(4271923/6250000000000),(-1113597/50000000000000),(2293/2500000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((77/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5661296355213/100000000000000),(15729716707/100000000000000),(-154038149/12500000000000),(27312519/100000000000000),(24458567/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((77/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((77/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((77/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel18
