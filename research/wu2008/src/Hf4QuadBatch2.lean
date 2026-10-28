import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel7
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(11/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((11/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (11/8) (1/40)

def c3 : Certificate := ⟨(12047619047619/5000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((11/8)+(1/40)*x)) := (SharedCertificates.h2 (11/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((11/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-149523809523809/100000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((11/8)+(1/40)*x)) := (SharedCertificates.h4 (11/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(121/64),(11/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((11/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(228875661375661/100000000000000),(8322751322751/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((11/8)+(1/40)*x)) := (SharedCertificates.h8 (11/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((11/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((11/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1331/512),(363/2560),(33/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((11/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(101307740162037/4000000000000),(138146918402777/100000000000000),(2511762152777/100000000000000),(608912037/4000000000000),(1/25000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((11/8)+(1/40)*x)) := (SharedCertificates.h13 (11/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((11/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((11/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(14641/4096),(1331/5120),(363/51200),(11/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((11/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(124822513640873/12500000000000),(72624007936507/100000000000000),(123790922619/6250000000000),(24007936507/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((11/8)+(1/40)*x)) := (SharedCertificates.h18 (11/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((11/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(491488647460937/100000000000000),(11170196533203/25000000000000),(1331/81920),(121/409600),(269531251/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((11/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(50030586277997/1562500000000),(58217409487123/20000000000000),(10584983543113/100000000000000),(96227123119/50000000000000),(1755946189/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((11/8)+(1/40)*x)) := (SharedCertificates.h22 (11/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((11/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(168949222564697/25000000000000),(73723297119139/100000000000000),(83776473999/2500000000000),(10154724121/12500000000000),(223173829/20000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((11/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(1517503704898569/100000000000000),(41386464679051/25000000000000),(300992470393/4000000000000),(11401229939/6250000000000),(2505687119/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((11/8)+(1/40)*x)) := (SharedCertificates.h26 (11/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((11/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(929220724105833/100000000000000),(23652891159057/20000000000000),(6450788497923/100000000000000),(19547843933/10000000000000),(3593161629/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((11/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(55126388195961/25000000000000),(28064343081579/100000000000000),(1530782349903/100000000000000),(724802249/1562500000000),(852662961/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((11/8)+(1/40)*x)) := (SharedCertificates.h30 (11/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((11/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((11/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((11/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((11/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((11/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (11/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((11/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((11/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (11/8) (1/40))

def c43 : Certificate := ⟨(361/64),(19/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((11/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((11/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(42210790133/50000000000000),(-1777296427/100000000000000),(1122503/4000000000000),(-393861/100000000000000),(5341/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((11/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-209536736577157/20000000000000),(70647534037/25000000000000),(-3040110263/100000000000000),(32694153/100000000000000),(26431607/20000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((11/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((11/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (11/8) (1/40))

def c52 : Certificate := ⟨(56249999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((11/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (11/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((11/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (11/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((11/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (11/8) (1/40))

def c56 : Certificate := ⟨(3030303030303/12500000000000),(-4897459443/10000000000000),(49469287/50000000000000),(-49969/25000000000000),(407/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((11/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1515151515151/50000000000000),(48974594429/25000000000000),(-395754299/100000000000000),(799503/100000000000000),(431/25000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((11/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((11/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((11/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((11/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((11/8)+(1/40)*x)) := (SharedCertificates.h61 (11/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-10743801652889/25000000000000),(-2813813061739/100000000000000),(422737547/12500000000000),(-272557/12500000000000),(13259/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((11/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((11/8)+(1/40)*x)) := (SharedCertificates.h61 (11/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-43726521412457/100000000000000),(-1456016041537/50000000000000),(300904103/100000000000000),(6158169/100000000000000),(66827/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((11/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((11/8)+(1/40)*x)) := (SharedCertificates.h67 (11/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-53361564556137/25000000000000),(-27122635513/195312500000),(4436069043/20000000000000),(-11003559/25000000000000),(68037/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((11/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((11/8)+(1/40)*x)) := (SharedCertificates.h67 (11/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-43717856110437/20000000000000),(-909489749797/6250000000000),(503915057/25000000000000),(19701509/50000000000000),(103593/25000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((11/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((11/8)+(1/40)*x)) := (SharedCertificates.h72 (11/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(311557900589221/100000000000000),(19700152078543/100000000000000),(-69134854953/100000000000000),(7246619/5000000000000),(3721/1562500000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((11/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((11/8)+(1/40)*x)) := (SharedCertificates.h72 (11/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(32762296668441/5000000000000),(43553281676981/100000000000000),(-786240307/6250000000000),(-61283819/25000000000000),(227643/12500000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((11/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((11/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((11/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(53076216712579/50000000000000),(6307334131/1562500000000),(-107932991/25000000000000),(24227/25000000000000),(8267/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((11/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10808247766925293/100000000000000),(481650970003/2500000000000),(-2589982939/3125000000000),(177300307/100000000000000),(196867/12500000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((11/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(462609676223/50000000000000),(-824616179/50000000000000),(2006909/20000000000000),(-45711/100000000000000),(81/25000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((11/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(6062462181643/100000000000000),(392156862743/100000000000000),(-384467513/50000000000000),(1005143/50000000000000),(9073/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((11/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((11/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((11/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (11/8) (1/40))

def c87 : Certificate := ⟨(22857142857143/100000000000000),(-65306122449/50000000000000),(149271137/20000000000000),(-426489/10000000000000),(24513/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((11/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1428571428571/50000000000000),(174149659863/100000000000000),(-497570457/50000000000000),(5686519/100000000000000),(38813/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((11/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((11/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((11/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((11/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((11/8)+(1/40)*x)) := (SharedCertificates.h61 (11/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-10122448979589/25000000000000),(-2497803692893/100000000000000),(3113369431/25000000000000),(-15191129/25000000000000),(147289/20000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((11/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((11/8)+(1/40)*x)) := (SharedCertificates.h61 (11/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-41156851311941/100000000000000),(-10319895599/400000000000),(2068160067/20000000000000),(-74211/200000000000),(95551/10000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((11/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((11/8)+(1/40)*x)) := (SharedCertificates.h67 (11/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-12573494377339/6250000000000),(-12335864246973/100000000000000),(65871868313/100000000000000),(-71554807/20000000000000),(153903/5000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((11/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((11/8)+(1/40)*x)) := (SharedCertificates.h67 (11/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-41149576628773/20000000000000),(-6446638308833/50000000000000),(52061035523/100000000000000),(-36448697/20000000000000),(4880531/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((11/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((11/8)+(1/40)*x)) := (SharedCertificates.h72 (11/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(18382593065809/6250000000000),(17559025715011/100000000000000),(-123408453823/100000000000000),(390209/48828125000),(1430487/25000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((11/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((11/8)+(1/40)*x)) := (SharedCertificates.h72 (11/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(616806942231411/100000000000000),(38599224614769/100000000000000),(-8036369151/5000000000000),(493980237/100000000000000),(1000401/6250000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((11/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((11/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((11/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(21159183673469/20000000000000),(358250728861/100000000000000),(-1743865983/100000000000000),(1028989/12500000000000),(27451/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((11/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2158236734693857/20000000000000),(17196034985327/100000000000000),(-66418547863/50000000000000),(180235561/20000000000000),(10515997/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((11/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(185336480271/20000000000000),(-738346389/50000000000000),(2752081/20000000000000),(-58747/50000000000000),(1149/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((11/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(2857920691997/50000000000000),(174291938997/50000000000000),(-987274601/50000000000000),(721111/6250000000000),(119327/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((11/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((11/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-61699682288967/50000000000000),(-7727335549107/100000000000000),(30478223451/100000000000000),(-16836217/10000000000000),(9897551/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((11/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(9090909090909/12500000000000),(-1322314049587/100000000000000),(6010518407/25000000000000),(-109282153/25000000000000),(8094977/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((11/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-17948998484063/20000000000000),(-997038316109/25000000000000),(94677858227/100000000000000),(-921930409/50000000000000),(68786909/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((11/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((11/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((11/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((11/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((11/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((11/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((11/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((11/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((11/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((11/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (11/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((11/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((11/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(7401119347/25000000000000),(-2153052901/100000000000000),(2446651/2500000000000),(-1779383/50000000000000),(6741/5000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((11/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(71426815108019/50000000000000),(-52124065087/5000000000000),(2708441761/20000000000000),(-190531909/100000000000000),(635874479/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((11/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((11/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (11/8) (1/40))

def c134 : Certificate := ⟨(945/64),(31/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((11/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((11/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(7017543859649/100000000000000),(-36934441367/50000000000000),(388783593/50000000000000),(-4092459/50000000000000),(21769/25000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((11/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(103618421052629/100000000000000),(268928901187/100000000000000),(1555134363/100000000000000),(-204623/1250000000000),(300953/12500000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((11/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((11/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (11/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((11/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (11/8) (1/40))

def c140 : Certificate := ⟨(24775876120619/100000000000000),(-4127010063/25000000000000),(-84461773/100000000000000),(562367/50000000000000),(149093/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((11/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(896495517521/100000000000000),(33016080503/50000000000000),(337847089/100000000000000),(-2249469/50000000000000),(121431/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((11/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((11/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(8037042129/100000000000000),(1183950727/100000000000000),(4966003/10000000000000),(365509/100000000000000),(8263/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((11/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((11/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(96300402103/100000000000000),(221493227/1562500000000),(593412077/100000000000000),(2153347/50000000000000),(99433/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((11/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-15688563640519/12500000000000),(-1848862373657/20000000000000),(-47283586767/100000000000000),(630325331/100000000000000),(17001469/20000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((11/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-126071961532143/50000000000000),(-9327377952013/50000000000000),(-50774662949/50000000000000),(241709203/20000000000000),(34463403/20000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((11/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(85722578819403/25000000000000),(25088646855581/100000000000000),(7249421547/6250000000000),(-367998507/20000000000000),(235299769/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((11/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(944394289703527/100000000000000),(2791404221433/4000000000000),(373504315911/100000000000000),(-918890863/20000000000000),(321988329/50000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((11/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(479126599173441/50000000000000),(8979027207271/12500000000000),(459978786073/100000000000000),(-981609661/25000000000000),(336061041/50000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((11/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(101801028077171/100000000000000),(133248272739/100000000000000),(22667319/3125000000000),(-8632367/100000000000000),(307709/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((11/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((11/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((11/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((11/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(10688592495237553/20000000000000),(17393077117487/25000000000000),(364371010919/100000000000000),(-2336266081/50000000000000),(4073151/625000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((11/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(187115375657/100000000000000),(-243587707/100000000000000),(-958639/100000000000000),(4817/25000000000000),(2331/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((11/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(1793039071831/100000000000000),(3301873423/2500000000000),(84566299/12500000000000),(-4485699/50000000000000),(260487/20000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((11/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((11/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((11/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (11/8) (1/40))

def c175 : Certificate := ⟨(12169735788631/50000000000000),(-9558968231/20000000000000),(-36505899/20000000000000),(952613/25000000000000),(220397/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((11/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(17614091273/2000000000000),(63726454873/100000000000000),(243372659/100000000000000),(-5080603/100000000000000),(77453/12500000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((11/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((11/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(1939101321/25000000000000),(140310449/12500000000000),(22448699/50000000000000),(44139/20000000000000),(8809/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((11/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((11/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(92940241377/100000000000000),(13440145811/100000000000000),(536509557/100000000000000),(1291277/50000000000000),(21163/10000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((11/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-123297820382053/100000000000000),(-4460763043361/50000000000000),(-34058656077/100000000000000),(14233541/2000000000000),(86751163/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((11/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-123841583676493/50000000000000),(-18000552981699/100000000000000),(-37214873069/50000000000000),(278336791/20000000000000),(1407689/800000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((11/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(336889900046979/100000000000000),(24218313732641/100000000000000),(253028313/312500000000),(-505607899/25000000000000),(240422319/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((11/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(927706796556689/100000000000000),(67340757401057/100000000000000),(272507760837/100000000000000),(-5259021371/100000000000000),(131489159/20000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((11/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(941080504021631/100000000000000),(17320328292507/25000000000000),(350684592671/100000000000000),(-4846435177/100000000000000),(687634083/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((11/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(12721145691573/12500000000000),(64287696669/50000000000000),(132910679/25000000000000),(-9940511/100000000000000),(628433/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((11/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((11/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((11/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((11/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(53426325411492751/100000000000000),(33569551136611/50000000000000),(10570077151/4000000000000),(-2654669017/50000000000000),(665614053/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((11/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(2339670547/1250000000000),(-4704299/2000000000000),(-630193/100000000000000),(5139/25000000000000),(1193/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((11/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(440363667523/25000000000000),(31865699067/25000000000000),(974997/200000000000),(-1013927/10000000000000),(167043/12500000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((11/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((11/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(2538861673069/50000000000000),(20856508813/6250000000000),(-280708923/50000000000000),(-1106037/10000000000000),(10491987/20000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((11/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1846444853141/50000000000000),(175550471527/100000000000000),(-900032661/25000000000000),(11482603/20000000000000),(40745007/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((11/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((11/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((11/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((11/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((11/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((11/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (11/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((11/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((11/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((11/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (11/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((11/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(428096509/1000000000000),(-56285761/20000000000000),(4014937/100000000000000),(-20313/50000000000000),(239/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((11/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(486123652993359/100000000000000),(-627971847061/50000000000000),(-75723857/12500000000000),(-59534187/100000000000000),(1307403/12500000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((11/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((11/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((11/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((11/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (11/8) (1/40))

def c223 : Certificate := ⟨(729/64),(27/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((11/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2222721/4096),(14283/1024),(6371/51200),(11/25600),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((11/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((11/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(24622960911/12500000000000),(-1036756249/25000000000000),(32739671/50000000000000),(-919009/100000000000000),(623/5000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((11/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(106894477146599/100000000000000),(124291532959/25000000000000),(440093857/20000000000000),(-8386139/50000000000000),(13554717/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((11/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((11/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (11/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((11/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (11/8) (1/40))

def c231 : Certificate := ⟨(6144099122533/25000000000000),(-15014398897/50000000000000),(-96217341/100000000000000),(646501/50000000000000),(823029/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((11/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1694414039469/100000000000000),(120115191173/100000000000000),(384869361/100000000000000),(-5172011/100000000000000),(3405593/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((11/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((11/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(28710389371/100000000000000),(162819893/4000000000000),(9832447/6250000000000),(374651/50000000000000),(33651/25000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((11/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((11/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(68710345343/20000000000000),(9727810933/20000000000000),(936249491/50000000000000),(427997/5000000000000),(1615857/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((11/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-23721214433697/10000000000000),(-4203722489859/25000000000000),(-1680944923/3125000000000),(181661291/25000000000000),(476817407/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((11/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-119613821732073/25000000000000),(-3420209520529/10000000000000),(-64892522251/50000000000000),(1343418489/100000000000000),(972413967/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((11/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(64424239164127/10000000000000),(22545063008041/50000000000000),(103052268123/100000000000000),(-278905043/12500000000000),(263314383/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((11/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(179005087497463/10000000000000),(63829398568809/50000000000000),(462498543789/100000000000000),(-5204418779/100000000000000),(3627876401/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((11/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(367959297624173/20000000000000),(134747333955423/100000000000000),(185060010189/25000000000000),(-1849221199/50000000000000),(3860445643/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((11/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(103417538468309/100000000000000),(244300879671/100000000000000),(463528937/50000000000000),(-59967/625000000000),(694579/10000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((11/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((11/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((11/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((11/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(13571213712200249/25000000000000),(126909841247997/100000000000000),(432239988421/100000000000000),(-5413408227/100000000000000),(1845436497/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((11/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(184213442733/100000000000000),(-3445307/800000000000),(-459963/100000000000000),(11437/50000000000000),(317/2500000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((11/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(6619438379/195312500000),(240299373221/100000000000000),(96856483/12500000000000),(-2549981/25000000000000),(1484421/20000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((11/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((11/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((11/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (11/8) (1/40))

def c259 : Certificate := ⟨(11885421735977/50000000000000),(-42138782097/50000000000000),(-74215381/100000000000000),(276799/6250000000000),(1169461/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((11/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(1638875370727/100000000000000),(112370085591/100000000000000),(1236923/1250000000000),(-5905047/100000000000000),(860269/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((11/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((11/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(26859124807/100000000000000),(3683211313/100000000000000),(129513821/100000000000000),(7209/25000000000000),(133719/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((11/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((11/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(321429122521/100000000000000),(22008723013/50000000000000),(15415899/1000000000000),(49899/100000000000000),(1602789/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((11/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-229437284079057/100000000000000),(-15730729401479/100000000000000),(-2755698471/20000000000000),(41423213/5000000000000),(60221291/12500000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((11/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-462645294943597/100000000000000),(-15989624943887/50000000000000),(-22918279307/50000000000000),(1649489971/100000000000000),(982223607/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((11/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(623384837937237/100000000000000),(4221850798847/10000000000000),(476554287/50000000000000),(-287780233/12500000000000),(665449781/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((11/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(1731035639837149/100000000000000),(29845249168953/25000000000000),(75987494529/50000000000000),(-6231993549/100000000000000),(3664424173/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((11/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(355511634556589/20000000000000),(62895966917219/50000000000000),(380605802093/100000000000000),(-603119249/10000000000000),(779335657/20000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((11/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(103304609866261/100000000000000),(45684676499/20000000000000),(327421501/100000000000000),(-5890629/50000000000000),(7015871/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((11/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((11/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((11/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((11/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(10845235992969397/20000000000000),(118704397736241/100000000000000),(127073361159/100000000000000),(-6290535527/100000000000000),(1863227583/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((11/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(184412769007/100000000000000),(-20184537/5000000000000),(451551/100000000000000),(427/2000000000000),(6413/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((11/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(3278044247139/100000000000000),(224800550629/100000000000000),(202101891/100000000000000),(-11711237/100000000000000),(1874719/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((11/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((11/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(16205410068309/50000000000000),(435444900679/20000000000000),(-70786197/6250000000000),(-3139303/2500000000000),(7347609/10000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((11/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(23571505553903/100000000000000),(144357896777/12500000000000),(-5455301547/25000000000000),(12216961/4000000000000),(65381629/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((11/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((11/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((11/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((11/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((11/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((11/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (11/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((11/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(904698651991679753/100000000000000),(1486862512754973/25000000000000),(-45749615777077/100000000000000),0,(29393/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((11/8)+(1/40)*x)) := (SharedCertificates.h297 (11/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(11053404333/100000000000000),(-14532921/20000000000000),(259163/25000000000000),(-1049/10000000000000),(31/25000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((11/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(609534800660003/100000000000000),(302143269491/50000000000000),(7852885013/100000000000000),(-21095587/100000000000000),(13065941/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((11/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((11/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (11/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((11/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (11/8) (1/40))

def c307 : Certificate := ⟨(583184218870663/25000000000000),(11091229182759/50000000000000),0,0,(511/50000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((11/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (11/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((11/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (11/8) (1/40))

def c311 : Certificate := ⟨(2042263124517089/100000000000000),(2817541634481/100000000000000),0,0,(511/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((11/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (11/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4896528698947/100000000000000),(-1351067187/20000000000000),(4659889/50000000000000),(-6429/50000000000000),(11/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((11/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(114223130578927/100000000000000),(928586227581/100000000000000),(-320273421/25000000000000),(441853/25000000000000),(3423/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((11/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((11/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (11/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((11/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (11/8) (1/40))

def c316 : Certificate := ⟨(6035394490177/25000000000000),(-43295577/80000000000),(97993343/50000000000000),(-709741/100000000000000),(2639/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((11/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(858422039291/25000000000000),(216477884999/100000000000000),(-156789349/20000000000000),(35487/1250000000000),(11301/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((11/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((11/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(58951071803/50000000000000),(14866351/100000000000),(414790173/100000000000000),(-3199181/100000000000000),(19309/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((11/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((11/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(1406728939387/100000000000000),(88432409799/50000000000000),(4886480729/100000000000000),(-39739937/100000000000000),(62521/25000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((11/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-96133607863593/20000000000000),(-757444641411/2500000000000),(4411687041/4000000000000),(-77917477/20000000000000),(1710899/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((11/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-488968662773627/50000000000000),(-6269467928307/10000000000000),(40368088461/25000000000000),(-69131063/20000000000000),(1464711/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((11/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(1288390622376337/100000000000000),(79074227907939/100000000000000),(-212164323811/50000000000000),(947206229/50000000000000),(2065671/25000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((11/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(3649611881240747/100000000000000),(232806022417839/100000000000000),(-169159071241/25000000000000),(193006949/12500000000000),(22021637/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((11/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(3856005146919427/100000000000000),(129545325056583/50000000000000),(40556918823/50000000000000),(-3285520157/100000000000000),(44926979/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((11/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(53492639228967/50000000000000),(223911060499/50000000000000),(-1153103317/100000000000000),(2478739/100000000000000),(41911/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((11/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((11/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((11/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((11/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(56127537740372253/100000000000000),(114965140936157/50000000000000),(-382853922901/50000000000000),(1847432197/100000000000000),(3444257/10000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((11/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(178165663461/100000000000000),(-364933889/50000000000000),(5420539/100000000000000),(-38027/100000000000000),(369/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((11/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(6870077153099/100000000000000),(216733418327/50000000000000),(-768742951/50000000000000),(3066047/50000000000000),(1037/625000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((11/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((11/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((11/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (11/8) (1/40))

def c344 : Certificate := ⟨(22590222379653/100000000000000),(-71081160471/50000000000000),(545385001/50000000000000),(-8369159/100000000000000),(12973/20000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((11/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(401629603391/12500000000000),(37909952251/20000000000000),(-363590001/25000000000000),(5579439/50000000000000),(104937/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((11/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((11/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(25809014131/25000000000000),(12180607269/100000000000000),(132916437/50000000000000),(-959279/20000000000000),(70929/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((11/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((11/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((11/8)+(1/40)*x)) := (SharedCertificates.h144 (11/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(616099326629/50000000000000),(36248296259/25000000000000),(625947619/20000000000000),(-7240629/12500000000000),(435251/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((11/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((11/8)+(1/40)*x)) := (SharedCertificates.h148 (11/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-3513949725011/781250000000),(-26529972261663/100000000000000),(203967873829/100000000000000),(-312028577/20000000000000),(1486001/10000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((11/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((11/8)+(1/40)*x)) := (SharedCertificates.h151 (11/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-182820417487203/20000000000000),(-10955783678927/20000000000000),(46253545787/12500000000000),(-490468581/20000000000000),(19658999/50000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((11/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((11/8)+(1/40)*x)) := (SharedCertificates.h154 (11/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(241529748347483/20000000000000),(69483912937291/100000000000000),(-31928921387/5000000000000),(5613440377/100000000000000),(14264423/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((11/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((11/8)+(1/40)*x)) := (SharedCertificates.h157 (11/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(3412490867298771/100000000000000),(50887222084029/25000000000000),(-1433452733459/100000000000000),(2452743433/25000000000000),(35325407/25000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((11/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((11/8)+(1/40)*x)) := (SharedCertificates.h160 (11/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(1796488922530889/50000000000000),(9001767495531/4000000000000),(-946799673523/100000000000000),(876996987/50000000000000),(126159737/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((11/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((11/8)+(1/40)*x)) := (SharedCertificates.h41 (11/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(5326465485539/5000000000000),(391280129779/100000000000000),(-1321443567/50000000000000),(17521361/100000000000000),(280803/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((11/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((11/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((11/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((11/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((11/8)+(1/40)*x)) := (SharedCertificates.h167 (11/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(5589324495076739/10000000000000),(50301853135811/25000000000000),(-1490874115227/100000000000000),(10576287207/100000000000000),(35747627/20000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((11/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(178912496649/100000000000000),(-644058519/100000000000000),(1418151/20000000000000),(-957/1250000000000),(293/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((11/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(1285657273329/20000000000000),(189745647161/50000000000000),(-2888589939/100000000000000),(11221303/50000000000000),(187353/25000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((11/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((11/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(40529076785557/50000000000000),(1258905735937/25000000000000),(-10510785403/50000000000000),(208461859/100000000000000),(1555763/20000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((11/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(11790276883071/20000000000000),(259042787881/10000000000000),(-31193551919/50000000000000),(1285919603/100000000000000),(667167/1562500000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((11/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((11/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(848934936523437/100000000000000),(17669219970703/25000000000000),(9559/409600),(781/2048000),(308593751/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((11/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1225/64),(7/32),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((11/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(42875/512),(735/512),(21/2560),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((11/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(35545005276799181/50000000000000),(3568592190742471/50000000000000),(303851847648619/100000000000000),(7136643600463/100000000000000),(50814833807/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((11/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(140666739561/100000000000000),(-564897627/4000000000000),(816607197/100000000000000),(-35743909/100000000000000),(2025027/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((11/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1064655178011/25000000000000),(72109303349/50000000000000),(-5906929379/100000000000000),(6161279/4000000000000),(66048707/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((11/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((11/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((11/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel7

namespace Hf4Quad.Panel8
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(57/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((57/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (57/40) (1/40)

def c3 : Certificate := ⟨(49942857142857/20000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((57/40)+(1/40)*x)) := (SharedCertificates.h2 (57/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((57/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-79142857142857/50000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((57/40)+(1/40)*x)) := (SharedCertificates.h4 (57/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(3249/1600),(57/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((57/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(245823809523809/100000000000000),(2156349206349/25000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((57/40)+(1/40)*x)) := (SharedCertificates.h8 (57/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((57/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((57/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(185193/64000),(9747/64000),(171/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((57/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(36085199/1280000),(1899221/1280000),(2603098958333/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((57/40)+(1/40)*x)) := (SharedCertificates.h13 (57/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((57/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((57/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(10556001/2560000),(185193/640000),(9747/1280000),(57/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((57/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(287986138392857/25000000000000),(40419107142857/50000000000000),(2127321428571/100000000000000),(1244047619/5000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((57/40)+(1/40)*x)) := (SharedCertificates.h18 (57/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((57/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(293794949707031/50000000000000),(12885743408203/25000000000000),(185193/10240000),(3249/10240000),(69824219/25000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((57/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(3828039381738277/100000000000000),(83948232055663/25000000000000),(2945552001953/25000000000000),(41341080729/20000000000000),(1819567429/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((57/40)+(1/40)*x)) := (SharedCertificates.h22 (57/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((57/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(418657803332519/50000000000000),(22034621228027/25000000000000),(193286151123/5000000000000),(90426269531/100000000000000),(1198193363/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((57/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(376038881977399/20000000000000),(197915201040733/100000000000000),(4340245636857/50000000000000),(101526213727/50000000000000),(2690546369/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((57/40)+(1/40)*x)) := (SharedCertificates.h26 (57/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((57/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(1193174739497679/100000000000000),(146530231166379/100000000000000),(482007339363/6250000000000),(225500509643/100000000000000),(999509279/25000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((57/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(283142259610957/100000000000000),(695437128869/2000000000000),(1830097707549/100000000000000),(428093031/800000000000),(237185139/25000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((57/40)+(1/40)*x)) := (SharedCertificates.h30 (57/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((57/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((57/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((57/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((57/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((57/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (57/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((57/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((57/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (57/40) (1/40))

def c43 : Certificate := ⟨(9409/1600),(97/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((57/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((57/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(80976167701/100000000000000),(-834805853/50000000000000),(25818737/100000000000000),(-354897/100000000000000),(589/12500000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((57/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-209426081409751/20000000000000),(67702757311/25000000000000),(-2852100509/100000000000000),(7506959/25000000000000),(30369911/25000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((57/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((57/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (57/40) (1/40))

def c52 : Certificate := ⟨(22833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((57/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (57/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((57/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (57/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((57/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (57/40) (1/40))

def c56 : Certificate := ⟨(24144869215291/100000000000000),(-24290612893/50000000000000),(19549789/20000000000000),(-98339/50000000000000),(399/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((57/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(213782696177/6250000000000),(9716245157/5000000000000),(-195497891/50000000000000),(786711/100000000000000),(213/12500000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((57/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((57/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((57/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((57/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((57/40)+(1/40)*x)) := (SharedCertificates.h61 (57/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-24294661328123/50000000000000),(-2800311783277/100000000000000),(3368700083/100000000000000),(-554811/25000000000000),(52153/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((57/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((57/40)+(1/40)*x)) := (SharedCertificates.h61 (57/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-49549332968107/100000000000000),(-582151022131/20000000000000),(67489431/20000000000000),(3011601/50000000000000),(66169/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((57/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((57/40)+(1/40)*x)) := (SharedCertificates.h67 (57/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-15070716632347/6250000000000),(-3449648241293/25000000000000),(438373219/2000000000000),(-21608441/50000000000000),(2111/1562500000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((57/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((57/40)+(1/40)*x)) := (SharedCertificates.h67 (57/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-61921144327949/25000000000000),(-727165288649/5000000000000),(35127329/1562500000000),(38100311/100000000000000),(40709/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((57/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((57/40)+(1/40)*x)) := (SharedCertificates.h72 (57/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(350682821299091/100000000000000),(1942534487563/10000000000000),(-68270487259/100000000000000),(35797937/25000000000000),(47793/20000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((57/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((57/40)+(1/40)*x)) := (SharedCertificates.h72 (57/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(92787529155951/12500000000000),(43500054597573/100000000000000),(-7012637349/50000000000000),(-236714831/100000000000000),(1785959/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((57/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((57/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((57/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(13369755757887/12500000000000),(25121478927/6250000000000),(-431118087/100000000000000),(26909/25000000000000),(8127/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((57/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10846449741609847/100000000000000),(18936641579857/100000000000000),(-20455227921/25000000000000),(35108979/20000000000000),(9683/625000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((57/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(921960663463/100000000000000),(-804818123/50000000000000),(9765109/100000000000000),(-44113/100000000000000),(39/12500000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((57/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(6843716155337/100000000000000),(194552529183/50000000000000),(-151402747/20000000000000),(392743/20000000000000),(35713/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((57/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((57/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((57/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (57/40) (1/40))

def c87 : Certificate := ⟨(22598870056497/100000000000000),(-63838615979/50000000000000),(721340293/100000000000000),(-4075369/100000000000000),(11579/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((57/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(400188323917/12500000000000),(42559077319/25000000000000),(-961787059/100000000000000),(217353/4000000000000),(37439/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((57/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((57/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((57/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((57/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((57/40)+(1/40)*x)) := (SharedCertificates.h61 (57/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-45436070945967/100000000000000),(-612177462453/25000000000000),(12095694879/100000000000000),(-3657087/6250000000000),(176609/25000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((57/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((57/40)+(1/40)*x)) := (SharedCertificates.h61 (57/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-11568932771221/25000000000000),(-2539052627367/100000000000000),(632541767/6250000000000),(-18136569/50000000000000),(458067/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((57/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((57/40)+(1/40)*x)) := (SharedCertificates.h67 (57/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-28198372746799/12500000000000),(-12076607683233/100000000000000),(63771792501/100000000000000),(-42799281/12500000000000),(2967869/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((57/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((57/40)+(1/40)*x)) := (SharedCertificates.h67 (57/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-231327643490627/100000000000000),(-12687205992629/100000000000000),(6372205933/12500000000000),(-178873531/100000000000000),(233453/5000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((57/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((57/40)+(1/40)*x)) := (SharedCertificates.h72 (57/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(65750444467269/20000000000000),(2134353386907/12500000000000),(-23745788069/20000000000000),(23783169/3125000000000),(2747719/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((57/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((57/40)+(1/40)*x)) := (SharedCertificates.h72 (57/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(693366432315083/100000000000000),(9490559919431/25000000000000),(-157766193829/100000000000000),(246437633/50000000000000),(7625111/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((57/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((57/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((57/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(21301101925443/20000000000000),(87843217969/25000000000000),(-1695353461/100000000000000),(1985239/25000000000000),(105263/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((57/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(10825051515218189/100000000000000),(2084415341633/12500000000000),(-63781441939/50000000000000),(857321717/100000000000000),(20072431/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((57/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(461891566333/50000000000000),(-284606163/20000000000000),(1634749/12500000000000),(-110077/100000000000000),(2159/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((57/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(3202601074647/50000000000000),(85205487233/25000000000000),(-38139069/2000000000000),(10999621/100000000000000),(113283/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((57/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((57/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-3468336304321/2500000000000),(-3803704055327/50000000000000),(14747030401/50000000000000),(-159797239/100000000000000),(20063267/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((57/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(70175438596491/100000000000000),(-1231148045553/100000000000000),(10799544259/50000000000000),(-189465689/50000000000000),(3383317/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((57/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-12169601067793/12500000000000),(-3630517822523/100000000000000),(4219544083/5000000000000),(-1592680197/100000000000000),(61546793/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((57/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((57/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((57/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((57/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((57/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((57/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((57/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((57/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((57/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((57/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (57/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((57/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((57/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(25663077419/100000000000000),(-900458857/50000000000000),(78987619/100000000000000),(-346437/12500000000000),(100871/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((57/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(140821370420131/100000000000000),(-247621008513/25000000000000),(12483155683/100000000000000),(-8187397/5000000000000),(1082786557/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((57/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((57/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (57/40) (1/40))

def c134 : Certificate := ⟨(24249/1600),(157/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((57/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((57/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1718213058419/25000000000000),(-70854146739/100000000000000),(730455121/100000000000000),(-3765233/50000000000000),(15689/20000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((57/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(20832474226801/20000000000000),(274958373187/100000000000000),(1460910241/100000000000000),(-15060943/100000000000000),(557589/25000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((57/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((57/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (57/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((57/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (57/40) (1/40))

def c140 : Certificate := ⟨(6185632751969/25000000000000),(-3366550951/20000000000000),(-77984277/100000000000000),(517959/50000000000000),(34447/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((57/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(514937984247/50000000000000),(67331019019/100000000000000),(62387421/20000000000000),(-1035919/25000000000000),(562613/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((57/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((57/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(662902819/6250000000000),(10834781/781250000000),(51759791/100000000000000),(334711/100000000000000),(8493/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((57/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((57/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(127058874789/100000000000000),(331987501/2000000000000),(309058817/50000000000000),(3932163/100000000000000),(40861/20000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((57/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-144181327040343/100000000000000),(-9426086159651/100000000000000),(-43653255983/100000000000000),(145154459/25000000000000),(78771347/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((57/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-57970032003313/20000000000000),(-952342053909/5000000000000),(-23647099679/25000000000000),(139173461/12500000000000),(159909637/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((57/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(393517150727537/100000000000000),(12765562208463/50000000000000),(2107861197/2000000000000),(-847469897/50000000000000),(43617859/20000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((57/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(217084501097189/20000000000000),(14245093598481/20000000000000),(34703727029/10000000000000),(-2117009191/50000000000000),(37335973/6250000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((57/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(22074535559999/2000000000000),(36813144996881/50000000000000),(109341851257/25000000000000),(-3616338073/100000000000000),(156592489/25000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((57/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(25517589595523/25000000000000),(68024445003/50000000000000),(675634001/100000000000000),(-7952641/100000000000000),(285553/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((57/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((57/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((57/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((57/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(10716705589818317/20000000000000),(35487609457419/50000000000000),(337449044111/100000000000000),(-4307621081/100000000000000),(605316451/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((57/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(186624516577/100000000000000),(-123598767/50000000000000),(-847861/100000000000000),(8841/50000000000000),(431/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((57/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2059824763773/100000000000000),(134676322397/100000000000000),(624874363/100000000000000),(-8259223/100000000000000),(242851/20000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((57/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((57/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((57/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (57/40) (1/40))

def c175 : Certificate := ⟨(3030397700647/12500000000000),(-24240269181/50000000000000),(-80318809/50000000000000),(3491887/100000000000000),(99/24414062500)⟩
theorem h175 : c175.Valid (fun x => f175 ((57/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(504545596549/50000000000000),(12928143563/20000000000000),(214183489/100000000000000),(-4655851/100000000000000),(143607/25000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((57/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((57/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(10182650359/100000000000000),(1304567581/100000000000000),(46106837/100000000000000),(36587/20000000000000),(8961/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((57/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((57/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(30496574963/25000000000000),(7807659071/50000000000000),(550621341/100000000000000),(26591/1250000000000),(8607/4000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((57/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-17658942010089/12500000000000),(-14139787607/156250000000),(-29969777061/100000000000000),(652224297/100000000000000),(40211737/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((57/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-56794218539277/20000000000000),(-18282037268129/100000000000000),(-66426018139/100000000000000),(1278042073/100000000000000),(81674389/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((57/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(192817291027693/50000000000000),(24518632978077/100000000000000),(1387289697/2000000000000),(-369696023/20000000000000),(111462101/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((57/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1063437157357961/100000000000000),(68369446033783/100000000000000),(48453520063/20000000000000),(-603487301/12500000000000),(610095073/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((57/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1081007854150961/100000000000000),(35313700323599/50000000000000),(64545296093/20000000000000),(-4479024283/100000000000000),(640873149/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((57/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(20405673007311/20000000000000),(130586003211/100000000000000),(94894763/20000000000000),(-9128767/100000000000000),(583389/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((57/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((57/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((57/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((57/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(53561619048812591/100000000000000),(34067094483741/50000000000000),(46745731811/20000000000000),(-1218004721/25000000000000),(309200519/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((57/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(186700853663/100000000000000),(-47499353/20000000000000),(-512601/100000000000000),(1867/10000000000000),(2207/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((57/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(2018250891863/100000000000000),(25858920249/20000000000000),(85850809/20000000000000),(-1857811/20000000000000),(1245721/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((57/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((57/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(1435700506259/25000000000000),(331334783917/100000000000000),(-621079251/100000000000000),(-8878563/100000000000000),(5064637/10000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((57/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(4030036508797/100000000000000),(32362648589/20000000000000),(-3274673913/100000000000000),(6402481/12500000000000),(37867879/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((57/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((57/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((57/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((57/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((57/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((57/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (57/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((57/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((57/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((57/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (57/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((57/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(21131267699/50000000000000),(-265841919/100000000000000),(945517/25000000000000),(-18531/50000000000000),(429/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((57/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(241804435927541/50000000000000),(-629535029727/50000000000000),(-238681451/25000000000000),(-11370863/20000000000000),(4737359/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((57/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((57/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((57/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((57/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (57/40) (1/40))

def c223 : Certificate := ⟨(18769/1600),(137/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((57/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1461898641/2560000),(9248733/640000),(162587/1280000),(277/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((57/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((57/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(188944391303/100000000000000),(-1947880323/50000000000000),(60243721/100000000000000),(-828093/100000000000000),(1099/10000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((57/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(10789748002751/10000000000000),(252886272263/50000000000000),(2104147331/100000000000000),(-3840367/25000000000000),(12591731/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((57/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((57/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (57/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((57/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (57/40) (1/40))

def c231 : Certificate := ⟨(24515964156791/100000000000000),(-30398573613/100000000000000),(-88773377/100000000000000),(14877/1250000000000),(760867/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((57/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(968071686417/50000000000000),(121594294451/100000000000000),(177546753/50000000000000),(-2380321/50000000000000),(3163639/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((57/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((57/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(37486511601/100000000000000),(4708479747/100000000000000),(161601963/100000000000000),(679201/100000000000000),(70287/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((57/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((57/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(448386553991/100000000000000),(3514266763/6250000000000),(960624577/50000000000000),(1925311/25000000000000),(105427/6250000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((57/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-271051390790211/100000000000000),(-3404313470157/20000000000000),(-9921186029/20000000000000),(669153433/100000000000000),(3460511/781250000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((57/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-3421050549583/625000000000),(-17352773710363/50000000000000),(-122046364221/100000000000000),(247615771/20000000000000),(452751487/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((57/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(734817367581561/100000000000000),(4547628584267/10000000000000),(90204373161/100000000000000),(-1027228257/50000000000000),(244631363/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((57/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(2047177659240563/100000000000000),(64723995630859/50000000000000),(432500524959/100000000000000),(-4802266639/100000000000000),(1688018893/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((57/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(528055782658687/25000000000000),(27533021808707/20000000000000),(359468687481/50000000000000),(-3408434489/100000000000000),(1809771073/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((57/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(103909773257269/100000000000000),(247897068649/100000000000000),(34871559/4000000000000),(-8842083/100000000000000),(1616963/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((57/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((57/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((57/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((57/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(54540361033066127/100000000000000),(2008992640377/1562500000000),(401014657613/100000000000000),(-1250620967/25000000000000),(1720962857/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((57/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(183350454793/100000000000000),(-432237361/100000000000000),(-164567/50000000000000),(20771/100000000000000),(11713/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((57/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(3872770716261/100000000000000),(60819946501/25000000000000),(716182867/100000000000000),(-9371269/100000000000000),(1739211/25000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((57/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((57/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((57/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (57/40) (1/40))

def c259 : Certificate := ⟨(590050650777/2500000000000),(-84523033449/100000000000000),(-3059137/6250000000000),(4001721/100000000000000),(535599/25000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((57/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(465991322973/25000000000000),(112697377931/100000000000000),(16315397/25000000000000),(-5335629/100000000000000),(1597459/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((57/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((57/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(34743666093/100000000000000),(4201280019/100000000000000),(16179987/12500000000000),(-51813/100000000000000),(2161/1562500000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((57/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((57/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(415628773361/100000000000000),(50180429023/100000000000000),(1538938509/100000000000000),(-114169/12500000000000),(828857/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((57/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-130473696844401/50000000000000),(-15776229161831/100000000000000),(-9051113767/100000000000000),(14974319/2000000000000),(8946249/2000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((57/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-526774250578217/100000000000000),(-32143410127093/100000000000000),(-18195824637/50000000000000),(375339731/25000000000000),(456970643/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((57/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(707807748181017/100000000000000),(21097843863509/50000000000000),(-3030294491/25000000000000),(-2060115371/100000000000000),(1235694101/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((57/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(30786825738219/1562500000000),(119916440574449/100000000000000),(58157046547/50000000000000),(-1132939791/20000000000000),(681526917/20000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((57/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1015308546002383/50000000000000),(12724372949617/10000000000000),(43214739607/12500000000000),(-1121032749/20000000000000),(3648389763/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((57/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(103762674249877/100000000000000),(229596035881/100000000000000),(4061923/1562500000000),(-10723071/100000000000000),(326407/5000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((57/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((57/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((57/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((57/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(54464047929708203/100000000000000),(14892449088083/12500000000000),(22776484181/25000000000000),(-1427139591/25000000000000),(434003881/12500000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((57/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(22950919873/12500000000000),(-100409843/25000000000000),(571449/100000000000000),(9333/50000000000000),(11843/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((57/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(3728362413707/100000000000000),(28184136683/12500000000000),(135306561/100000000000000),(-2114773/20000000000000),(7017261/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((57/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((57/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(36759754178041/100000000000000),(542806730191/25000000000000),(-1856618721/100000000000000),(-115974163/100000000000000),(68544599/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((57/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(3224539840179/12500000000000),(535550509729/50000000000000),(-20094136287/100000000000000),(271143329/100000000000000),(58813993/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((57/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((57/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((57/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((57/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((57/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((57/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (57/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((57/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(916410553630611233/100000000000000),(5764451587911587/100000000000000),(-45749615777077/100000000000000),0,(119061/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((57/40)+(1/40)*x)) := (SharedCertificates.h297 (57/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10912139717/100000000000000),(-68640089/100000000000000),(39061/4000000000000),(-957/10000000000000),(57/50000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((57/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(61077462524429/10000000000000),(3971638257/625000000000),(193474029/2500000000000),(-16996773/100000000000000),(12049327/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((57/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((57/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (57/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((57/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (57/40) (1/40))

def c307 : Certificate := ⟨(2377101792213689/100000000000000),(11091229182759/50000000000000),0,0,(41/4000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((57/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (57/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((57/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (57/40) (1/40))

def c311 : Certificate := ⟨(511974551946513/25000000000000),(2817541634481/100000000000000),0,0,(1/97656250000)⟩
theorem h311 : c311.Valid (fun x => f311 ((57/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (57/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4883055203613/100000000000000),(-1679552637/25000000000000),(577691/6250000000000),(-12717/100000000000000),(11/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((57/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(29018798189967/25000000000000),(184696596833/20000000000000),(-79409213/6250000000000),(1748041/100000000000000),(17/500000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((57/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((57/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (57/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((57/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (57/40) (1/40))

def c316 : Certificate := ⟨(24034117327853/100000000000000),(-10668791977/20000000000000),(191789191/100000000000000),(-344773/50000000000000),(637/25000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((57/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(772706137717/20000000000000),(213375839539/100000000000000),(-383578383/50000000000000),(2758181/100000000000000),(2751/25000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((57/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((57/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(18658586727/12500000000000),(3297536417/20000000000000),(198006907/50000000000000),(-3060729/100000000000000),(18599/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((57/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((57/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(1779690242203/100000000000000),(24492645631/12500000000000),(4653494327/100000000000000),(-37937501/100000000000000),(240167/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((57/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-540825537523231/100000000000000),(-14930624929711/50000000000000),(107986174513/100000000000000),(-94783931/25000000000000),(1661847/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((57/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-220536710683543/20000000000000),(-31026462327183/50000000000000),(15940826059/10000000000000),(-42794581/12500000000000),(567863/10000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((57/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(180607099702619/12500000000000),(15479880829153/20000000000000),(-82628641059/20000000000000),(917220273/50000000000000),(2006397/25000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((57/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(4112529708796441/100000000000000),(230117956569963/100000000000000),(-667409207113/100000000000000),(4785917/312500000000),(21293059/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((57/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(4374484917767301/100000000000000),(25937627684487/10000000000000),(30923710161/50000000000000),(-3137619431/100000000000000),(21888483/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((57/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(53938165035493/50000000000000),(443239361163/100000000000000),(-569149859/50000000000000),(2455633/100000000000000),(40607/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((57/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((57/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((57/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((57/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(28292175113392533/50000000000000),(56722392141427/25000000000000),(-188665480821/25000000000000),(229290407/12500000000000),(16613903/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((57/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(35345461987/20000000000000),(-3543169/500000000000),(5198451/100000000000000),(-1441/4000000000000),(43/12500000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((57/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(3865454759341/50000000000000),(213694818987/50000000000000),(-150132123/10000000000000),(2962169/50000000000000),(80899/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((57/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((57/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((57/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (57/40) (1/40))

def c344 : Certificate := ⟨(5577548719097/25000000000000),(-137897654709/100000000000000),(260514413/25000000000000),(-3937283/50000000000000),(3757/6250000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((57/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(3586406831481/100000000000000),(183863539611/100000000000000),(-347352551/25000000000000),(10499419/100000000000000),(3979/4000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((57/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((57/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(16077892451/12500000000000),(1318818909/10000000000000),(238398207/100000000000000),(-2178067/50000000000000),(65713/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((57/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((57/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((57/40)+(1/40)*x)) := (SharedCertificates.h144 (57/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(383562944291/25000000000000),(9802457671/6250000000000),(43730567/1562500000000),(-52498339/100000000000000),(804417/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((57/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((57/40)+(1/40)*x)) := (SharedCertificates.h148 (57/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-62755241487099/12500000000000),(-25732449719731/100000000000000),(97442428313/50000000000000),(-734336813/50000000000000),(14075447/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((57/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((57/40)+(1/40)*x)) := (SharedCertificates.h151 (57/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-511099589478563/50000000000000),(-53327733492053/100000000000000),(177843524939/50000000000000),(-116468497/5000000000000),(7411993/20000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((57/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((57/40)+(1/40)*x)) := (SharedCertificates.h154 (57/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1344106408934723/100000000000000),(261701022191/390625000000),(-30300713129/5000000000000),(1311582607/25000000000000),(53626099/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((57/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((57/40)+(1/40)*x)) := (SharedCertificates.h157 (57/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(1906966148563729/50000000000000),(197930768025661/100000000000000),(-1376109775487/100000000000000),(2327146753/25000000000000),(133112973/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((57/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((57/40)+(1/40)*x)) := (SharedCertificates.h160 (57/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(504911678744941/12500000000000),(221278783603431/100000000000000),(-935723801071/100000000000000),(386498031/20000000000000),(118528421/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((57/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((57/40)+(1/40)*x)) := (SharedCertificates.h41 (57/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(10730143680257/10000000000000),(47614408539/12500000000000),(-2540422201/100000000000000),(1040169/6250000000000),(264663/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((57/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((57/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((57/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((57/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((57/40)+(1/40)*x)) := (SharedCertificates.h167 (57/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(28144889880569181/50000000000000),(24421072684083/12500000000000),(-1429095136819/100000000000000),(5011267041/50000000000000),(83816589/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((57/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(22206517867/12500000000000),(-61658879/10000000000000),(6650299/100000000000000),(-2199/3125000000000),(133/12500000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((57/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(1793972834449/25000000000000),(368200670449/100000000000000),(-2758088469/100000000000000),(2634501/12500000000000),(349301/50000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((57/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((57/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(45523478533533/50000000000000),(154812212427/3125000000000),(-19806087049/100000000000000),(49220269/25000000000000),(744929/10000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((57/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(15973150362643/25000000000000),(2355561937823/100000000000000),(-6903082061/12500000000000),(55350789/5000000000000),(3741069/10000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((57/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((57/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(499966844238281/50000000000000),(20119844970703/25000000000000),(263169/10240000),(4161/10240000),(19897461/6250000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((57/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(31329/1600),(177/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((57/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(5545233/64000),(93987/64000),(531/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((57/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(86638520111749239/100000000000000),(4220763130660561/50000000000000),(87290168860519/25000000000000),(7978300555297/100000000000000),(110686717423/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((57/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(57711050391/50000000000000),(-702876369/6250000000000),(630582453/100000000000000),(-6686639/25000000000000),(731927/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((57/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(4524609727917/100000000000000),(61167418147/50000000000000),(-5059789969/100000000000000),(129179227/100000000000000),(60747421/50000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((57/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((57/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((57/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel8

namespace Hf4Quad.Panel9
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(59/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((59/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (59/40) (1/40)

def c3 : Certificate := ⟨(25847619047619/10000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((59/40)+(1/40)*x)) := (SharedCertificates.h2 (59/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((59/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-167047619047619/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((59/40)+(1/40)*x)) := (SharedCertificates.h4 (59/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(3481/1600),(59/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((59/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(2057634755291/781250000000),(4464021164021/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((59/40)+(1/40)*x)) := (SharedCertificates.h8 (59/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((59/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((59/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(205379/64000),(10443/64000),(177/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((59/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(156322181568287/5000000000000),(39742927517361/25000000000000),(168402235243/6250000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((59/40)+(1/40)*x)) := (SharedCertificates.h13 (59/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((59/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((59/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(12117361/2560000),(205379/640000),(10443/1280000),(59/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((59/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(41322845672123/3125000000000),(89649563492063/100000000000000),(569806547619/25000000000000),(25753968253/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((59/40)+(1/40)*x)) := (SharedCertificates.h18 (59/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((59/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(698168260742187/100000000000000),(14791700439453/25000000000000),(205379/10240000),(3481/10240000),(289062501/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((59/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(1137109232079173/25000000000000),(96365189159251/25000000000000),(6533233163339/50000000000000),(2768319137/1250000000000),(941594333/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((59/40)+(1/40)*x)) := (SharedCertificates.h22 (59/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((59/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(41191927383789/4000000000000),(104725239111327/100000000000000),(887502026367/20000000000000),(100282714843/100000000000000),(128344727/10000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((59/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(578103636960319/25000000000000),(235160801475381/100000000000000),(15569438657/156250000000),(112592550739/50000000000000),(2881984243/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((59/40)+(1/40)*x)) := (SharedCertificates.h26 (59/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((59/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(1518952322277219/100000000000000),(7208587292163/4000000000000),(9163458422239/100000000000000),(258854757689/100000000000000),(2216119389/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((59/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(45056224638977/12500000000000),(2672826885363/6250000000000),(2174503228769/100000000000000),(767833061/1250000000000),(1051777299/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((59/40)+(1/40)*x)) := (SharedCertificates.h30 (59/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((59/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((59/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((59/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((59/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((59/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (59/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((59/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((59/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (59/40) (1/40))

def c43 : Certificate := ⟨(9801/1600),(99/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((59/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((59/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(38868725737/50000000000000),(-785226783/50000000000000),(95179/400000000000),(-320469/100000000000000),(521/12500000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((59/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-104659995820501/10000000000000),(32469128921/12500000000000),(-1339637721/50000000000000),(27637713/100000000000000),(111861973/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((59/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((59/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (59/40) (1/40))

def c52 : Certificate := ⟨(28958333333333/25000000000000),(833333333333/100000000000000),0,0,(1/25000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((59/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (59/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((59/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (59/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((59/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (59/40) (1/40))

def c56 : Certificate := ⟨(187875751503/781250000000),(-2409628877/5000000000000),(96578311/100000000000000),(-24193/12500000000000),(391/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((59/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(190380761523/5000000000000),(192770310159/100000000000000),(-386313247/100000000000000),(387087/50000000000000),(1681/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((59/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((59/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((59/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((59/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((59/40)+(1/40)*x)) := (SharedCertificates.h61 (59/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-27088244625517/50000000000000),(-222949101/8000000000),(3355273773/100000000000000),(-11279/500000000000),(25621/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((59/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((59/40)+(1/40)*x)) := (SharedCertificates.h61 (59/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-55369445482491/100000000000000),(-1454666788831/50000000000000),(373186409/100000000000000),(5890247/100000000000000),(65463/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((59/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((59/40)+(1/40)*x)) := (SharedCertificates.h67 (59/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-268641321571413/100000000000000),(-428482305979/3125000000000),(10830852467/50000000000000),(-1697521/4000000000000),(133901/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((59/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((59/40)+(1/40)*x)) := (SharedCertificates.h67 (59/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-276761894007663/100000000000000),(-3633465265323/25000000000000),(2472945231/100000000000000),(9209653/25000000000000),(399749/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((59/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((59/40)+(1/40)*x)) := (SharedCertificates.h72 (59/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(194630785584977/50000000000000),(1915397429787/10000000000000),(-67416531883/100000000000000),(70730829/50000000000000),(119637/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((59/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((59/40)+(1/40)*x)) := (SharedCertificates.h72 (59/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(82924236413699/10000000000000),(21720572947373/50000000000000),(-963805803/6250000000000),(-228530501/100000000000000),(175087/10000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((59/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((59/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((59/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(6735013112397/6250000000000),(25013782731/6250000000000),(-215220607/50000000000000),(29477/25000000000000),(7983/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((59/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10883997141957901/100000000000000),(744458296781/4000000000000),(-80772935059/100000000000000),(173778649/100000000000000),(95189/6250000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((59/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(114847512701/12500000000000),(-785549487/50000000000000),(297033/3125000000000),(-42583/100000000000000),(301/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((59/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(3809456917897/50000000000000),(96525096529/25000000000000),(-372683771/50000000000000),(1918573/100000000000000),(35133/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((59/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((59/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((59/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (59/40) (1/40))

def c87 : Certificate := ⟨(22346368715083/100000000000000),(-7802503043/6250000000000),(697430439/100000000000000),(-194813/5000000000000),(21893/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((59/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1769087523277/50000000000000),(665813593/400000000000),(-929907253/100000000000000),(1298753/25000000000000),(903/2500000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((59/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((59/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((59/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((59/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((59/40)+(1/40)*x)) := (SharedCertificates.h61 (59/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-314284822571/625000000000),(-2401020526713/100000000000000),(11751118471/100000000000000),(-2254461/4000000000000),(84747/12500000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((59/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((59/40)+(1/40)*x)) := (SharedCertificates.h61 (59/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-51313642198527/100000000000000),(-312375240927/12500000000000),(9905505601/100000000000000),(-35449279/100000000000000),(878801/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((59/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((59/40)+(1/40)*x)) := (SharedCertificates.h67 (59/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-249487819742527/100000000000000),(-2365114048263/20000000000000),(61761477487/100000000000000),(-327844397/100000000000000),(715549/25000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((59/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((59/40)+(1/40)*x)) := (SharedCertificates.h67 (59/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-128249784520551/50000000000000),(-12485428207073/100000000000000),(6239334837/12500000000000),(-87720279/50000000000000),(4469519/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((59/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((59/40)+(1/40)*x)) := (SharedCertificates.h72 (59/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(362432976141839/100000000000000),(8304449130903/50000000000000),(-1142714043/1000000000000),(725131263/100000000000000),(659893/12500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((59/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((59/40)+(1/40)*x)) := (SharedCertificates.h72 (59/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(768663786021007/100000000000000),(18668540715223/50000000000000),(-154815197683/100000000000000),(490610249/100000000000000),(145407/1000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((59/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((59/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((59/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(26800384229927/25000000000000),(172342810851/50000000000000),(-1648550661/100000000000000),(1915479/25000000000000),(50479/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((59/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5428949341771857/50000000000000),(16175191186013/100000000000000),(-15318031527/12500000000000),(815956731/100000000000000),(2395949/12500000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((59/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(46049425821/5000000000000),(-68600591/5000000000000),(2487671/20000000000000),(-51613/50000000000000),(2033/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((59/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(1769826299783/25000000000000),(16666203717/5000000000000),(-1842490233/100000000000000),(2623301/25000000000000),(107631/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((59/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((59/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-153831554276417/100000000000000),(-7491317032949/100000000000000),(14279719731/50000000000000),(-37959201/25000000000000),(20172143/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((59/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(67796610169491/100000000000000),(-1149095087619/100000000000000),(779047517/4000000000000),(-330104881/100000000000000),(5691467/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((59/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-26073144792613/25000000000000),(-3311188171991/100000000000000),(75484165263/100000000000000),(-1382332837/100000000000000),(55255689/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((59/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((59/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((59/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((59/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((59/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((59/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((59/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((59/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((59/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((59/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (59/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((59/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((59/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(22356309339/100000000000000),(-151568199/10000000000000),(64223813/100000000000000),(-2177079/100000000000000),(19061/25000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((59/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(6944453459821/5000000000000),(-942429089111/100000000000000),(36139981/312500000000),(-143240447/100000000000000),(927133653/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((59/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((59/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (59/40) (1/40))

def c134 : Certificate := ⟨(24881/1600),(159/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((59/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((59/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3367003367003/50000000000000),(-68020270041/100000000000000),(343536717/50000000000000),(-867517/12500000000000),(70821/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((59/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(52359006734001/50000000000000),(280626126577/100000000000000),(1374146857/100000000000000),(-13880277/100000000000000),(1034851/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((59/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((59/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (59/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((59/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (59/40) (1/40))

def c140 : Certificate := ⟨(24708561683011/100000000000000),(-1070786901/6250000000000),(-72013943/100000000000000),(955513/100000000000000),(31887/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((59/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(582876633977/50000000000000),(3426518083/5000000000000),(288055771/100000000000000),(-3822053/100000000000000),(261111/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((59/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((59/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(13589806817/100000000000000),(1597789861/100000000000000),(53680143/100000000000000),(305699/100000000000000),(1083/6250000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((59/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((59/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(162760834569/100000000000000),(19117599469/100000000000000),(25625677/4000000000000),(3579519/100000000000000),(104163/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((59/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-163203560123813/100000000000000),(-9593916227771/100000000000000),(-20153384717/50000000000000),(535617031/100000000000000),(73116489/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((59/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-328313465862681/100000000000000),(-3882437329349/20000000000000),(-22042589031/25000000000000),(205479667/20000000000000),(148648183/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((59/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(222493841602431/50000000000000),(518657932667/2000000000000),(47812327713/50000000000000),(-1563306549/100000000000000),(1619811/800000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((59/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(1229228389810653/100000000000000),(72564145001621/100000000000000),(322627027649/100000000000000),(-781630897/20000000000000),(555087859/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((59/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(313175117900343/25000000000000),(75333506848767/100000000000000),(416519298427/100000000000000),(-417249087/12500000000000),(584731179/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((59/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(4093803853709/4000000000000),(138658513181/100000000000000),(125958337/20000000000000),(-7338407/100000000000000),(265443/25000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((59/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((59/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((59/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((59/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(10745358880430707/20000000000000),(72274676976073/100000000000000),(39076252233/12500000000000),(-3977518807/100000000000000),(281594011/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((59/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(93063434281/50000000000000),(-25038269/10000000000000),(-746161/100000000000000),(203/1250000000000),(399/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((59/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2331612160253/100000000000000),(137079352137/100000000000000),(577285103/100000000000000),(-1522893/20000000000000),(283473/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((59/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((59/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((59/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (59/40) (1/40))

def c175 : Certificate := ⟨(24145605316913/100000000000000),(-49082372979/100000000000000),(-1757119/1250000000000),(400251/12500000000000),(373591/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((59/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(569596455391/50000000000000),(65443163971/100000000000000),(7497041/4000000000000),(-853869/20000000000000),(266687/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((59/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((59/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(12977604879/100000000000000),(1491047769/100000000000000),(9419673/20000000000000),(74021/50000000000000),(4527/25000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((59/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((59/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(77717789319/50000000000000),(2230201937/12500000000000),(562107073/100000000000000),(426751/25000000000000),(217311/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((59/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-39871309199597/25000000000000),(-9161737983561/100000000000000),(-6555318143/25000000000000),(59812241/10000000000000),(466723/625000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((59/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-40098857441289/12500000000000),(-18532827966521/100000000000000),(-5907264593/10000000000000),(1174707831/100000000000000),(37969949/25000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((59/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(13591713872527/3125000000000),(12387278889133/50000000000000),(58756353679/100000000000000),(-21125179/1250000000000),(207021091/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((59/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1201107303229567/100000000000000),(69282187298511/100000000000000),(26811888753/12500000000000),(-4435747657/100000000000000),(283524289/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((59/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(305879603704913/25000000000000),(71865922945669/100000000000000),(148433819323/50000000000000),(-4145984053/100000000000000),(149553419/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((59/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(102291363426443/100000000000000),(132377375711/100000000000000),(84390083/20000000000000),(-1048831/12500000000000),(135607/12500000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((59/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((59/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((59/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((59/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(13424696045914191/25000000000000),(34506134304597/50000000000000),(102854518671/50000000000000),(-4474070267/100000000000000),(287719291/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((59/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(18622395557/10000000000000),(-119665071/50000000000000),(-81161/20000000000000),(8477/50000000000000),(1021/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((59/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(569621097301/25000000000000),(16362914507/12500000000000),(75175349/20000000000000),(-851551/10000000000000),(581441/50000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((59/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((59/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(6402920186597/100000000000000),(164375871271/50000000000000),(-133712167/20000000000000),(-6997527/100000000000000),(1942883/4000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((59/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(434096283837/10000000000000),(37326723997/25000000000000),(-2983886939/100000000000000),(11457567/25000000000000),(35017049/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((59/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((59/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((59/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((59/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((59/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((59/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (59/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((59/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((59/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((59/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (59/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((59/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(41745689953/100000000000000),(-251145233/100000000000000),(892369/25000000000000),(-33859/100000000000000),(77/20000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((59/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(481086462888049/100000000000000),(-1263561589323/100000000000000),(-1288758693/100000000000000),(-27279327/50000000000000),(8589889/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((59/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((59/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((59/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((59/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (59/40) (1/40))

def c223 : Certificate := ⟨(19321/1600),(139/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((59/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1537198081/2560000),(9577239/640000),(165923/1280000),(279/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((59/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((59/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(90693693387/50000000000000),(-3664391653/100000000000000),(11104217/20000000000000),(-747759/100000000000000),(4859/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((59/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(13614665179033/12500000000000),(20560400029/4000000000000),(403169177/20000000000000),(-563817/4000000000000),(2343517/20000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((59/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((59/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (59/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((59/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (59/40) (1/40))

def c231 : Certificate := ⟨(24454821245953/100000000000000),(-15369882893/50000000000000),(-40957673/50000000000000),(548733/50000000000000),(28183/4000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((59/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(2180715016187/100000000000000),(6147953157/5000000000000),(163830691/50000000000000),(-2194933/50000000000000),(58879/2000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((59/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((59/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(23777589909/50000000000000),(5362773507/100000000000000),(82740017/50000000000000),(614317/100000000000000),(14541/10000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((59/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((59/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(568588071921/100000000000000),(32001220831/50000000000000),(24563043/1250000000000),(6907097/100000000000000),(1744199/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((59/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-76321925745179/25000000000000),(-8606086999089/50000000000000),(-45749181637/100000000000000),(308666407/50000000000000),(206095289/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((59/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-617257659313833/100000000000000),(-17589632520829/50000000000000),(-22981416807/20000000000000),(571688029/50000000000000),(211166831/25000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((59/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(826114650766773/100000000000000),(91626211117/200000000000),(39182613171/50000000000000),(-1894625393/100000000000000),(45533273/4000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((59/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(2307765973236541/100000000000000),(6556092620217/5000000000000),(404791597429/100000000000000),(-1110118001/25000000000000),(1573569979/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((59/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(597600591307499/25000000000000),(70250509493539/50000000000000),(699274871737/100000000000000),(-3150915789/100000000000000),(679927213/20000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((59/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(3262780787881/3125000000000),(251280899787/100000000000000),(410401399/50000000000000),(-1633083/20000000000000),(603331/10000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((59/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((59/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((59/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((59/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(547990768939917/1000000000000),(130121077326461/100000000000000),(372129243991/100000000000000),(-4632510199/100000000000000),(803851757/25000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((59/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(182484825781/100000000000000),(-6770507/1562500000000),(-26289/12500000000000),(4717/25000000000000),(5421/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((59/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(2181060795827/50000000000000),(246035128713/100000000000000),(662234823/100000000000000),(-4312229/50000000000000),(653187/10000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((59/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((59/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((59/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (59/40) (1/40))

def c259 : Certificate := ⟨(5858203849441/25000000000000),(-21168094937/25000000000000),(-81601/312500000000),(3616179/100000000000000),(982739/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((59/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(2089579469647/100000000000000),(112896506329/100000000000000),(1392657/4000000000000),(-2410787/50000000000000),(742793/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((59/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((59/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(43663423599/100000000000000),(1179531109/25000000000000),(25782249/20000000000000),(-122889/100000000000000),(70881/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((59/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((59/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(522136319317/100000000000000),(56321726353/100000000000000),(765431967/50000000000000),(-5499/312500000000),(42477/2500000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((59/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-9141569228039/3125000000000),(-15803744525167/100000000000000),(-4778543831/100000000000000),(169176579/25000000000000),(415991953/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((59/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-295597451411263/50000000000000),(-32271509966181/100000000000000),(-3474021809/12500000000000),(1367388489/100000000000000),(425888279/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((59/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(158426921699823/20000000000000),(5265422212373/12500000000000),(-23815656169/100000000000000),(-920920301/50000000000000),(574573993/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((59/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(552652681320129/25000000000000),(30078956349047/25000000000000),(83891213909/100000000000000),(-5151553969/100000000000000),(3173948073/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((59/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1143221689433951/50000000000000),(128560925772631/100000000000000),(78316807883/25000000000000),(-1043583391/20000000000000),(3421249/100000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((59/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(104222822362893/100000000000000),(115255568547/50000000000000),(39708819/20000000000000),(-9766037/100000000000000),(3042053/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((59/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((59/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((59/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((59/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(27351323478004027/50000000000000),(59718836675291/50000000000000),(58460659009/100000000000000),(-5182036051/100000000000000),(3240213303/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((59/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(91403255203/50000000000000),(-49892431/12500000000000),(135223/20000000000000),(16267/100000000000000),(1369/12500000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((59/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(4179767353317/100000000000000),(225891644669/100000000000000),(74994511/100000000000000),(-954791/10000000000000),(1644087/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((59/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((59/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(20546935694593/50000000000000),(2162443793773/100000000000000),(-2526459249/100000000000000),(-107482487/100000000000000),(500309/781250000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((59/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(13930125894639/50000000000000),(993855931553/100000000000000),(-9278934759/50000000000000),(120835339/50000000000000),(26517771/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((59/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((59/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((59/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((59/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((59/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((59/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (59/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((59/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(185551291668665221/20000000000000),(5581453124803283/100000000000000),(-45749615777077/100000000000000),0,(120501/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((59/40)+(1/40)*x)) := (SharedCertificates.h297 (59/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10778690797/100000000000000),(-64845421/100000000000000),(460817/50000000000000),(-8743/100000000000000),(103/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((59/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(61207637775983/10000000000000),(166557544111/25000000000000),(3824378687/50000000000000),(-6601651/50000000000000),(11017009/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((59/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((59/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (59/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((59/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (59/40) (1/40))

def c307 : Certificate := ⟨(2421466708944727/100000000000000),(11091229182759/50000000000000),0,0,(1027/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((59/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (59/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((59/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (59/40) (1/40))

def c311 : Certificate := ⟨(1026766645527507/50000000000000),(2817541634481/100000000000000),0,0,(1027/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((59/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (59/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4869655653287/100000000000000),(-6681390367/100000000000000),(9167173/100000000000000),(-6289/50000000000000),(21/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((59/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(117917090484589/100000000000000),(459210847201/50000000000000),(-252023319/20000000000000),(432233/25000000000000),(3357/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((59/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((59/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (59/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((59/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (59/40) (1/40))

def c316 : Certificate := ⟨(4785638217573/20000000000000),(-52584999043/100000000000000),(187710711/100000000000000),(-41879/6250000000000),(123/5000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((59/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(2143617824269/50000000000000),(210339996169/100000000000000),(-750842849/100000000000000),(1340127/50000000000000),(10711/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((59/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((59/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(9190194753/5000000000000),(18035542597/100000000000000),(75609667/20000000000000),(-2928829/100000000000000),(7/39062500000)⟩
theorem h319 : c319.Valid (fun x => f319 ((59/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((59/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(437977305699/20000000000000),(214106832529/100000000000000),(4431052611/100000000000000),(-18112103/50000000000000),(721/312500000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((59/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-37507444074963/6250000000000),(-2943381399197/10000000000000),(6608867389/6250000000000),(-369017213/100000000000000),(806913/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((59/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1226154501802437/100000000000000),(-30709693198197/50000000000000),(78682134691/50000000000000),(-84739331/25000000000000),(2751891/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((59/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(799008795889851/50000000000000),(9471076420531/12500000000000),(-402310961409/100000000000000),(222083113/12500000000000),(3897033/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((59/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(4570108210829587/100000000000000),(227466645035589/100000000000000),(-658259916979/100000000000000),(75907169/5000000000000),(51473/250000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((59/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(1223365011936949/25000000000000),(64896647259401/25000000000000),(4345070443/10000000000000),(-37444767/1250000000000),(42649823/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((59/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(13594784399017/12500000000000),(87743106987/20000000000000),(-1123637363/100000000000000),(2431679/100000000000000),(19671/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((59/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((59/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((59/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((59/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(11407025072576077/20000000000000),(223892876634057/100000000000000),(-743698375817/100000000000000),(1819997561/100000000000000),(32058801/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((59/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(175330551767/100000000000000),(-172066167/25000000000000),(4987989/100000000000000),(-683/2000000000000),(81/25000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((59/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(8579730502213/100000000000000),(421454642321/100000000000000),(-1466375167/100000000000000),(357863/6250000000000),(78901/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((59/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((59/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((59/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (59/40) (1/40))

def c344 : Certificate := ⟨(5509626434743/25000000000000),(-33455512507/25000000000000),(996203229/100000000000000),(-3707987/50000000000000),(6971/12500000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((59/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(1974329507351/50000000000000),(44607350009/25000000000000),(-664135487/50000000000000),(2471991/25000000000000),(4717/5000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((59/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((59/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(155919080143/100000000000000),(7045568589/50000000000000),(53368181/25000000000000),(-30931/781250000000),(12197/20000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((59/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((59/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((59/40)+(1/40)*x)) := (SharedCertificates.h144 (59/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(232339442011/12500000000000),(8371220663/5000000000000),(124933533/5000000000000),(-23807821/50000000000000),(186177/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((59/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((59/40)+(1/40)*x)) := (SharedCertificates.h148 (59/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-552738867719707/100000000000000),(-12485094245437/50000000000000),(186330645941/100000000000000),(-691888419/50000000000000),(13339233/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((59/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((59/40)+(1/40)*x)) := (SharedCertificates.h151 (59/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-140931287155567/12500000000000),(-3245779265897/6250000000000),(342061146997/100000000000000),(-8855139/400000000000),(8740279/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((59/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((59/40)+(1/40)*x)) := (SharedCertificates.h154 (59/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1475714552861839/100000000000000),(64632980123499/100000000000000),(-575564693159/100000000000000),(4908111003/100000000000000),(2522099/5000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((59/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((59/40)+(1/40)*x)) := (SharedCertificates.h157 (59/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(1051090725289987/25000000000000),(3008376791513/1562500000000),(-1321688859247/100000000000000),(8836607147/100000000000000),(125509221/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((59/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((59/40)+(1/40)*x)) := (SharedCertificates.h160 (59/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(4478123874851977/100000000000000),(217559698333459/100000000000000),(-23091777273/2500000000000),(1040151647/50000000000000),(222937799/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((59/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((59/40)+(1/40)*x)) := (SharedCertificates.h41 (59/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(108053237109547/100000000000000),(1483799749/400000000000),(-305383653/12500000000000),(395419/2500000000000),(49933/20000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((59/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((59/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((59/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((59/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((59/40)+(1/40)*x)) := (SharedCertificates.h167 (59/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(56674879664301903/100000000000000),(94885179451703/50000000000000),(-685268022929/50000000000000),(9502603049/100000000000000),(15740013/10000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((59/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(44111253783/25000000000000),(-295404543/50000000000000),(1249027/20000000000000),(-64783/100000000000000),(483/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((59/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(1975356587153/25000000000000),(35741607991/10000000000000),(-131773459/5000000000000),(9906779/50000000000000),(651711/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((59/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((59/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(20175453573089/20000000000000),(487708614443/10000000000000),(-9328372407/50000000000000),(11649411/6250000000000),(3555607/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((59/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(4274460502773/6250000000000),(2147323351403/100000000000000),(-24521975797/50000000000000),(239404977/25000000000000),(16448883/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((59/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((59/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1171502674804687/100000000000000),(22814317626953/25000000000000),(288923/10240000),(177/409600),(328125001/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((59/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(32041/1600),(179/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((59/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(5735339/64000),(96123/64000),(537/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((59/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(20996765560661371/20000000000000),(9937495846675857/100000000000000),(199869976177581/50000000000000),(4447106191589/50000000000000),(30077569737/25000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((59/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(23813191539/25000000000000),(-2254094721/25000000000000),(245389659/50000000000000),(-315541/1562500000000),(534603/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((59/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(4750030495159/100000000000000),(103560296891/100000000000000),(-434784161/10000000000000),(108802779/100000000000000),(111305253/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((59/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((59/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((59/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel9
