import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel1
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(43/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((43/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (43/40) (1/40)

def c3 : Certificate := ⟨(23547619047619/12500000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((43/40)+(1/40)*x)) := (SharedCertificates.h2 (43/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((43/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-96952380952381/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((43/40)+(1/40)*x)) := (SharedCertificates.h4 (43/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(1849/1600),(43/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((43/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(139897883597883/100000000000000),(3253439153439/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((43/40)+(1/40)*x)) := (SharedCertificates.h8 (43/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((43/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((43/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(79507/64000),(5547/64000),(129/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((43/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(151289904152199/12500000000000),(84440876736111/100000000000000),(490935329861/25000000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((43/40)+(1/40)*x)) := (SharedCertificates.h13 (43/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((43/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((43/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(3418801/2560000),(79507/640000),(5547/1280000),(43/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((43/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(373083442460317/100000000000000),(1084544890873/3125000000000),(75665922619/6250000000000),(18769841269/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((43/40)+(1/40)*x)) := (SharedCertificates.h18 (43/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((43/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(143562932617187/100000000000000),(4173341064453/25000000000000),(79507/10240000),(1849/10240000),(210937501/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((43/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(93528592027271/10000000000000),(108754176775893/100000000000000),(505833380353/10000000000000),(117635669849/100000000000000),(1374218759/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((43/40)+(1/40)*x)) := (SharedCertificates.h22 (43/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((43/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(38582538140869/25000000000000),(21534439892577/100000000000000),(250400463867/20000000000000),(38821777343/100000000000000),(683447269/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((43/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(10829648933191/3125000000000),(48355641748199/100000000000000),(1405687260121/50000000000000),(43587201863/50000000000000),(1534682653/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((43/40)+(1/40)*x)) := (SharedCertificates.h26 (43/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((43/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(20738114250717/12500000000000),(27007776698607/100000000000000),(1884263490599/100000000000000),(73033468627/100000000000000),(1722336431/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((43/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(19684749717347/50000000000000),(3204494140033/50000000000000),(447138717213/100000000000000),(17330958031/100000000000000),(408713171/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((43/40)+(1/40)*x)) := (SharedCertificates.h30 (43/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((43/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((43/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((43/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((43/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((43/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (43/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((43/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((43/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (43/40) (1/40))

def c43 : Certificate := ⟨(6889/1600),(83/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((43/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((43/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(110597294513/100000000000000),(-2664995049/100000000000000),(48162561/100000000000000),(-12089/1562500000000),(12059/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((43/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-262894348476627/25000000000000),(372566312477/100000000000000),(-575141097/12500000000000),(56791569/100000000000000),(228523721/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((43/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((43/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (43/40) (1/40))

def c52 : Certificate := ⟨(51249999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((43/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (43/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((43/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (43/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((43/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (43/40) (1/40))

def c56 : Certificate := ⟨(12422360248447/50000000000000),(-10287668943/20000000000000),(13312201/12500000000000),(-55123/25000000000000),(23/5000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((43/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(621118012421/100000000000000),(25719172357/12500000000000),(-425990433/100000000000000),(881967/100000000000000),(1857/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((43/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((43/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((43/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((43/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((43/40)+(1/40)*x)) := (SharedCertificates.h61 (43/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-1089849928627/12500000000000),(-2895882959551/100000000000000),(3455549727/100000000000000),(-1895399/100000000000000),(29447/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((43/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((43/40)+(1/40)*x)) := (SharedCertificates.h61 (43/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-1749961241523/20000000000000),(-1458236689543/50000000000000),(32046659/50000000000000),(7009887/100000000000000),(35451/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((43/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((43/40)+(1/40)*x)) := (SharedCertificates.h67 (43/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-21766303745939/50000000000000),(-14438854283321/100000000000000),(23856259221/100000000000000),(-49215549/100000000000000),(142397/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((43/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((43/40)+(1/40)*x)) := (SharedCertificates.h67 (43/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-43748649735879/100000000000000),(-364549716387/2500000000000),(22226001/5000000000000),(48165877/100000000000000),(462901/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((43/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((43/40)+(1/40)*x)) := (SharedCertificates.h72 (43/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(8118207570063/12500000000000),(669484971773/3125000000000),(-18635700943/25000000000000),(19444043/12500000000000),(57469/25000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((43/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((43/40)+(1/40)*x)) := (SharedCertificates.h72 (43/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(8202597562529/6250000000000),(8748319202763/20000000000000),(-2778084271/100000000000000),(-300981963/100000000000000),(513181/25000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((43/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((43/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((43/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(20249218780139/20000000000000),(207031350153/50000000000000),(-27120509/6250000000000),(2191/10000000000000),(9199/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((43/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2112961959666707/20000000000000),(1333326901799/6250000000000),(-11180954673/12500000000000),(93739069/50000000000000),(4357/250000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((43/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(118317321737/12500000000000),(-1911319361/100000000000000),(2968351/25000000000000),(-11391/20000000000000),(409/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((43/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(310562999963/25000000000000),(411522633743/100000000000000),(-105844299/12500000000000),(464611/20000000000000),(1241/3125000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((43/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((43/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((43/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (43/40) (1/40))

def c87 : Certificate := ⟨(24539877300613/100000000000000),(-150551394483/100000000000000),(923628187/100000000000000),(-5666431/100000000000000),(34981/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((43/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(306748466257/50000000000000),(100367596321/50000000000000),(-4926017/400000000000),(188881/2500000000000),(48391/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((43/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((43/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((43/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((43/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((43/40)+(1/40)*x)) := (SharedCertificates.h61 (43/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-8611539764369/100000000000000),(-2825070747981/100000000000000),(2982809067/20000000000000),(-3066593/4000000000000),(956321/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((43/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((43/40)+(1/40)*x)) := (SharedCertificates.h61 (43/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-8641788587493/100000000000000),(-44451731411/1562500000000),(588384849/5000000000000),(-8433143/20000000000000),(621947/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((43/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((43/40)+(1/40)*x)) := (SharedCertificates.h67 (43/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-42997802383879/100000000000000),(-14086264036463/100000000000000),(40336589379/50000000000000),(-471121287/100000000000000),(120281/3125000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((43/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((43/40)+(1/40)*x)) := (SharedCertificates.h67 (43/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-21604287737327/50000000000000),(-14224194004157/100000000000000),(58953655491/100000000000000),(-199593301/100000000000000),(1292361/20000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((43/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((43/40)+(1/40)*x)) := (SharedCertificates.h72 (43/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(1283041892577/2000000000000),(10451597708151/50000000000000),(-6278684607/4000000000000),(1082323477/100000000000000),(916003/12500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((43/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((43/40)+(1/40)*x)) := (SharedCertificates.h72 (43/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(64810749046661/50000000000000),(42668423041647/100000000000000),(-178201801743/100000000000000),(46455017/10000000000000),(10892267/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((43/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((43/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((43/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(10123075764989/10000000000000),(201966696891/50000000000000),(-1037586403/50000000000000),(10259057/100000000000000),(71629/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((43/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(528200977798973/5000000000000),(20816199434129/100000000000000),(-85397396589/50000000000000),(613617393/50000000000000),(28224311/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((43/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(59163086237/6250000000000),(-1865275763/100000000000000),(18979887/100000000000000),(-88763/50000000000000),(1711/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((43/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(613504629589/50000000000000),(401485496333/100000000000000),(-245815671/10000000000000),(15589737/100000000000000),(331169/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((43/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((43/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-25966193196451/100000000000000),(-2135052517721/25000000000000),(37669078557/100000000000000),(-59171269/25000000000000),(3023273/25000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((43/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(93023255813953/100000000000000),(-1081665765279/50000000000000),(25155017797/50000000000000),(-292500207/25000000000000),(5571433/20000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((43/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-603864958057/2500000000000),(-7382646616583/100000000000000),(51682614877/25000000000000),(-5027857269/100000000000000),(14569501/10000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((43/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((43/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((43/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((43/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((43/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((43/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((43/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((43/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((43/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((43/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (43/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((43/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((43/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(79238151299/100000000000000),(-7370990819/100000000000000),(428545977/100000000000000),(-4983093/25000000000000),(500159/50000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((43/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(19721051095479/12500000000000),(-1497796391781/100000000000000),(27960309189/100000000000000),(-211105739/25000000000000),(3858919597/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((43/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((43/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (43/40) (1/40))

def c134 : Certificate := ⟨(20049/1600),(143/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((43/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((43/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1004016064257/12500000000000),(-967726327/1000000000000),(1165935333/100000000000000),(-7023707/50000000000000),(10707/6250000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((43/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(50323795180721/50000000000000),(223121401261/100000000000000),(1165935329/50000000000000),(-1755927/6250000000000),(3968423/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((43/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((43/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (43/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((43/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (43/40) (1/40))

def c140 : Certificate := ⟨(24959591023569/100000000000000),(-556001739/4000000000000),(-68765097/50000000000000),(1907747/100000000000000),(62191/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((43/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(161635905723/100000000000000),(55600173899/100000000000000),(22004831/4000000000000),(-476937/6250000000000),(7799/781250000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((43/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((43/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(13063083/5000000000000),(179739689/100000000000000),(16346089/50000000000000),(587067/100000000000000),(4947/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((43/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((43/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(1567147667/50000000000000),(269500587/12500000000000),(78399541/20000000000000),(3502307/50000000000000),(59853/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((43/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-11314510867537/50000000000000),(-7784019118309/100000000000000),(-77015058907/100000000000000),(534289887/50000000000000),(69882117/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((43/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-22647315113339/50000000000000),(-97457576481/625000000000),(-19826339513/12500000000000),(1027244887/50000000000000),(70225309/25000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((43/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(7769576414693/12500000000000),(21355678828111/100000000000000),(25327637277/12500000000000),(-48517563/1562500000000),(193067421/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((43/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(169818168410819/100000000000000),(58449260222829/100000000000000),(295085026597/50000000000000),(-7792164053/100000000000000),(1052136543/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((43/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(332552100153/195312500000),(29378985485073/50000000000000),(646398857873/100000000000000),(-3382147447/50000000000000),(8548857/800000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((43/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(50161766536553/50000000000000),(111380087487/100000000000000),(35404179/3125000000000),(-14674917/100000000000000),(1003219/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((43/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((43/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((43/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((43/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(822965192182787/1562500000000),(7302206635967/12500000000000),(584394860021/100000000000000),(-7901955157/100000000000000),(132103099/12500000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((43/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(189862221979/100000000000000),(-21058199/10000000000000),(-374609/20000000000000),(16449/50000000000000),(387/10000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((43/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(323272092973/100000000000000),(1390007979/1250000000000),(550172179/50000000000000),(-1524859/10000000000000),(515463/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((43/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((43/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((43/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (43/40) (1/40))

def c175 : Certificate := ⟨(24879163700401/100000000000000),(-10357955659/25000000000000),(-91003003/25000000000000),(3272139/50000000000000),(376427/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((43/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(161115066131/100000000000000),(2762121509/5000000000000),(121337337/25000000000000),(-1745141/20000000000000),(202711/20000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((43/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((43/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(51916129/20000000000000),(35601551/20000000000000),(16040601/50000000000000),(12703/2500000000000),(11769/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((43/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((43/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(778532823/25000000000000),(533808167/25000000000000),(384671857/100000000000000),(242347/4000000000000),(142057/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((43/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-11278052120503/50000000000000),(-7733935064697/100000000000000),(-67947094287/100000000000000),(244366211/20000000000000),(35475759/25000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((43/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-9029711959789/20000000000000),(-15492801525131/100000000000000),(-14038918003/10000000000000),(2372061903/100000000000000),(11417713/4000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((43/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(61956559328457/100000000000000),(21218433220253/100000000000000),(177855582553/100000000000000),(-438047969/12500000000000),(392543369/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((43/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(42317660197271/25000000000000),(58072964090743/100000000000000),(521925651453/100000000000000),(-4485903607/50000000000000),(1068885833/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((43/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(33943252089449/20000000000000),(3648668669319/6250000000000),(288551779151/50000000000000),(-4040038949/50000000000000),(217729657/20000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((43/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(100322489712907/100000000000000),(22132573623/20000000000000),(501389949/50000000000000),(-1694329/10000000000000),(2038879/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((43/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((43/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((43/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((43/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(52669225067679923/100000000000000),(58041662002983/100000000000000),(258129203521/50000000000000),(-9067532773/100000000000000),(107440359/10000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((43/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(47466048661/25000000000000),(-209230977/100000000000000),(-1630457/100000000000000),(18267/50000000000000),(789/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((43/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(161115205539/50000000000000),(110485147157/100000000000000),(19415991/2000000000000),(-1743849/10000000000000),(526861/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((43/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((43/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(1018399029171/100000000000000),(85020455747/25000000000000),(63846793/50000000000000),(-5211629/20000000000000),(20508557/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((43/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(29604622941/3125000000000),(294323836869/100000000000000),(-3362977831/50000000000000),(66088719/50000000000000),(42808301/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((43/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((43/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((43/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((43/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((43/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((43/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (43/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((43/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((43/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((43/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (43/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((43/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(46846375217/100000000000000),(-399222057/100000000000000),(5994497/100000000000000),(-73177/100000000000000),(971/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((43/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(501219616091261/100000000000000),(-1270268205329/100000000000000),(981270517/50000000000000),(-17404407/20000000000000),(19880179/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((43/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((43/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((43/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((43/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (43/40) (1/40))

def c223 : Certificate := ⟨(15129/1600),(123/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((43/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1004701761/2560000),(7132647/640000),(139907/1280000),(263/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((43/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((43/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(51612070773/20000000000000),(-310916089/5000000000000),(112379309/100000000000000),(-1805291/100000000000000),(14067/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((43/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(101278785926737/100000000000000),(435568278291/100000000000000),(1504729053/50000000000000),(-928043/3125000000000),(2200487/10000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((43/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((43/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (43/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((43/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (43/40) (1/40))

def c231 : Certificate := ⟨(24920330579911/100000000000000),(-13524893249/50000000000000),(-39383257/25000000000000),(2218133/100000000000000),(686403/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((43/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(9958677511/3125000000000),(27049786497/25000000000000),(630132109/100000000000000),(-1774507/20000000000000),(69079/1250000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((43/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((43/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(1015554639/100000000000000),(689613057/100000000000000),(30271683/25000000000000),(261409/20000000000000),(62597/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((43/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((43/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(190315359/1562500000000),(1653752751/20000000000000),(1450763921/100000000000000),(15405669/100000000000000),(377671/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((43/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-11153709108439/25000000000000),(-7573920454381/50000000000000),(-88204848517/100000000000000),(310956183/25000000000000),(386856503/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((43/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-223429820061/250000000000),(-30392306536677/100000000000000),(-96694523297/50000000000000),(575335939/25000000000000),(778067391/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((43/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(24481219709681/20000000000000),(10365779511257/25000000000000),(208537196903/100000000000000),(-380141953/10000000000000),(2135037283/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((43/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(335001645285063/100000000000000),(56936839671727/50000000000000),(353968667853/50000000000000),(-1106528583/12500000000000),(2913676041/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((43/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(33674671531427/10000000000000),(57529910562807/50000000000000),(14324896781/1562500000000),(-1616238661/25000000000000),(2966417031/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((43/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(100638370915343/100000000000000),(217087905033/100000000000000),(27627019/2000000000000),(-657521/4000000000000),(11115237/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((43/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((43/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((43/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((43/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(26417411394348537/50000000000000),(22750368168939/20000000000000),(686347443791/100000000000000),(-4565030529/50000000000000),(5719497/97656250000)⟩
theorem h254 : c254.Valid (fun x => f254 ((43/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(189269112153/100000000000000),(-407490909/100000000000000),(-1581373/100000000000000),(10351/25000000000000),(4243/20000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((43/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(637357518279/100000000000000),(108200244819/50000000000000),(78813949/6250000000000),(-17652111/100000000000000),(2281863/20000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((43/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((43/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((43/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (43/40) (1/40))

def c259 : Certificate := ⟨(12381252712073/50000000000000),(-80124745923/100000000000000),(-294341441/100000000000000),(1641337/20000000000000),(2056173/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((43/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(316659434471/100000000000000),(53416497281/50000000000000),(392455253/100000000000000),(-1367781/12500000000000),(349269/6250000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((43/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((43/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(501365987/50000000000000),(84574189/12500000000000),(5830919/5000000000000),(192311/25000000000000),(34653/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((43/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((43/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(12026433197/100000000000000),(2028173663/25000000000000),(1397228473/100000000000000),(8971791/100000000000000),(417007/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((43/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-8866456548621/20000000000000),(-14956580700869/100000000000000),(-13732649183/25000000000000),(1533466353/100000000000000),(391190129/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((43/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-88805024007703/100000000000000),(-7501990351609/25000000000000),(-126213961177/100000000000000),(1478077183/50000000000000),(1574429493/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((43/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(12163267278453/10000000000000),(8188161359803/20000000000000),(11828868023/10000000000000),(-17368333/390625000000),(2160864627/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((43/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(332877567528321/100000000000000),(112434231044079/100000000000000),(45666823163/10000000000000),(-1122970367/10000000000000),(58947677/1000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((43/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(167300291320091/50000000000000),(113597957637683/100000000000000),(657816684603/100000000000000),(-391003041/4000000000000),(1503181021/25000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((43/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(25158580400229/25000000000000),(53585645659/25000000000000),(450764443/50000000000000),(-5278813/25000000000000),(5622957/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((43/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((43/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((43/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((43/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(26416350488168627/50000000000000),(112314699993591/100000000000000),(435875189347/100000000000000),(-28524873/250000000000),(5926925499/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((43/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(189276713383/100000000000000),(-201187493/50000000000000),(-353081/50000000000000),(45697/100000000000000),(21507/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((43/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(633320985781/100000000000000),(213668131639/100000000000000),(196410303/25000000000000),(-5449529/25000000000000),(11588439/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((43/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((43/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(6368889919803/100000000000000),(267430908433/12500000000000),(2410098029/50000000000000),(-216395901/100000000000000),(58035009/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((43/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(5924548762607/100000000000000),(463100825209/25000000000000),(-19297621611/50000000000000),(696265283/100000000000000),(26201481/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((43/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((43/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((43/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((43/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((43/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((43/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (43/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((43/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(82674130670754209/10000000000000),(3522720414834859/50000000000000),(-45749615777077/100000000000000),0,(107649/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((43/40)+(1/40)*x)) := (SharedCertificates.h297 (43/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(12095682069/100000000000000),(-25769673/25000000000000),(386943/25000000000000),(-3779/20000000000000),(253/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((43/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(301731514087013/50000000000000),(402437774399/100000000000000),(9174962857/100000000000000),(-13990771/25000000000000),(12046837/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((43/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((43/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (43/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((43/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (43/40) (1/40))

def c307 : Certificate := ⟨(2066547375096427/100000000000000),(11091229182759/50000000000000),0,0,(1007/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((43/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (43/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((43/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (43/40) (1/40))

def c311 : Certificate := ⟨(1004226312451657/50000000000000),(2817541634481/100000000000000),0,0,(1007/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((43/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (43/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(1244739342617/25000000000000),(-174617259/2500000000000),(612401/6250000000000),(-6873/50000000000000),(3/12500000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((43/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(6430782052911/6250000000000),(960113210447/100000000000000),(-1346887123/100000000000000),(1889461/100000000000000),(901/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((43/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((43/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (43/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((43/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (43/40) (1/40))

def c316 : Certificate := ⟨(2482051584763/10000000000000),(-59148543087/100000000000000),(8957201/4000000000000),(-33911/4000000000000),(3283/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((43/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(717936609479/100000000000000),(118297086173/50000000000000),(-111965013/12500000000000),(3391097/100000000000000),(2663/20000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((43/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((43/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(644291219/12500000000000),(1698596179/50000000000000),(273453309/50000000000000),(-523719/12500000000000),(24387/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((43/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((43/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(61777947383/100000000000000),(40693139233/100000000000000),(1634760937/25000000000000),(-26372127/50000000000000),(321919/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((43/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1256383522507/1250000000000),(-33122745814473/100000000000000),(125543484987/100000000000000),(-57502957/12500000000000),(1024927/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((43/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-50435963408801/25000000000000),(-66721970990873/100000000000000),(6969470393/4000000000000),(-362502591/100000000000000),(7110123/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((43/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(137478600833397/50000000000000),(90132420696133/100000000000000),(-249827282669/50000000000000),(576501151/25000000000000),(9866363/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((43/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(377903729182057/50000000000000),(62430376831019/25000000000000),(-733308104417/100000000000000),(159704377/10000000000000),(1696827/6250000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((43/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(764685876834487/100000000000000),(63896489502559/25000000000000),(108538872129/50000000000000),(-430869627/10000000000000),(13119089/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((43/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(10144102754871/10000000000000),(9531710741/2000000000000),(-124453359/10000000000000),(1296221/50000000000000),(51017/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((43/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((43/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((43/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((43/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(53254892452477691/100000000000000),(124557066394547/50000000000000),(-41660903389/5000000000000),(946028771/50000000000000),(1345003/3125000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((43/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(18777617491/10000000000000),(-878373739/100000000000000),(1761687/25000000000000),(-26689/50000000000000),(11/2000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((43/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(358974472399/25000000000000),(47321273563/10000000000000),(-356698833/20000000000000),(1520973/20000000000000),(47081/25000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((43/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((43/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((43/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (43/40) (1/40))

def c344 : Certificate := ⟨(24469169594521/100000000000000),(-86228765081/50000000000000),(9108769/625000000000),(-3079053/25000000000000),(13143/12500000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((43/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(707773873971/100000000000000),(57485843387/25000000000000),(-971602027/50000000000000),(8210807/50000000000000),(5851/4000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((43/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((43/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(2504719283/50000000000000),(650991649/20000000000000),(501232569/100000000000000),(-8704083/100000000000000),(58337/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((43/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((43/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((43/40)+(1/40)*x)) := (SharedCertificates.h144 (43/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(60042351797/100000000000000),(38990385707/100000000000000),(5992921207/100000000000000),(-106506033/100000000000000),(45561/3125000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((43/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((43/40)+(1/40)*x)) := (SharedCertificates.h148 (43/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-99087917391861/100000000000000),(-8047914567387/25000000000000),(272179472953/100000000000000),(-114337363/5000000000000),(20850207/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((43/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((43/40)+(1/40)*x)) := (SharedCertificates.h151 (43/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-99439001551721/50000000000000),(-648398348403/1000000000000),(473926445721/100000000000000),(-675820097/20000000000000),(57268483/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((43/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((43/40)+(1/40)*x)) := (SharedCertificates.h154 (43/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(271085334931793/100000000000000),(87611972615473/100000000000000),(-445004765721/50000000000000),(4307739389/50000000000000),(84429817/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((43/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((43/40)+(1/40)*x)) := (SharedCertificates.h157 (43/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(186270309711591/25000000000000),(242683979642379/100000000000000),(-925236663697/50000000000000),(271983841/2000000000000),(103357913/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((43/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((43/40)+(1/40)*x)) := (SharedCertificates.h160 (43/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(376854774183189/50000000000000),(62075594926599/25000000000000),(-97944402819/10000000000000),(-261864967/100000000000000),(375672657/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((43/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((43/40)+(1/40)*x)) := (SharedCertificates.h41 (43/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(25355139296627/25000000000000),(463141705341/100000000000000),(-3385175539/100000000000000),(4827829/20000000000000),(51153/12500000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((43/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((43/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((43/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((43/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((43/40)+(1/40)*x)) := (SharedCertificates.h167 (43/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(1064883842675149/2000000000000),(60525552515993/25000000000000),(-1942043539837/100000000000000),(1475686723/10000000000000),(270214101/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((43/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(1878139117/1000000000000),(-21349823/2500000000000),(1341687/12500000000000),(-16501/12500000000000),(2207/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((43/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(1415571385643/100000000000000),(45990978599/10000000000000),(-3879117501/100000000000000),(8382283/25000000000000),(1162889/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((43/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((43/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(17207562835809/100000000000000),(564252481503/10000000000000),(-30154909079/100000000000000),(6189157/2000000000000),(155563/1562500000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((43/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(16007035196101/100000000000000),(4876603660583/100000000000000),(-141460465669/100000000000000),(1788823019/50000000000000),(13031383/12500000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((43/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((43/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(277109846679687/100000000000000),(7279083251953/25000000000000),(123883/10240000),(2537/10240000),(250000001/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((43/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(26569/1600),(163/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((43/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(4330747/64000),(79707/64000),(489/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((43/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(1171965465994643/6250000000000),(578840103022971/25000000000000),(120243718728209/100000000000000),(852500270111/25000000000000),(2319727407/4000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((43/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(33330760277/6250000000000),(-65848973447/100000000000000),(4711053559/100000000000000),(-128213791/50000000000000),(9271197/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((43/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1317861625577/100000000000000),(193004539231/50000000000000),(-4045085207/25000000000000),(486525169/100000000000000),(974241/625000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((43/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((43/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((43/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel1

namespace Hf4Quad.Panel2
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(9/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((9/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (9/8) (1/40)

def c3 : Certificate := ⟨(197142857142857/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((9/8)+(1/40)*x)) := (SharedCertificates.h2 (9/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((9/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-52857142857143/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((9/8)+(1/40)*x)) := (SharedCertificates.h4 (9/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(81/64),(9/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((9/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(30642857142857/20000000000000),(6809523809523/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((9/8)+(1/40)*x)) := (SharedCertificates.h8 (9/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((9/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((9/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(729/512),(243/2560),(27/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((9/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(142047/10240),(47349/51200),(5261/256000),(608912037/4000000000000),(1/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((9/8)+(1/40)*x)) := (SharedCertificates.h13 (9/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((9/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((9/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(6561/4096),(729/5120),(243/51200),(9/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((9/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(223744419642857/50000000000000),(7955357142857/20000000000000),(662946428571/50000000000000),(9821428571/50000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((9/8)+(1/40)*x)) := (SharedCertificates.h18 (9/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((9/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(22525405883789/12500000000000),(5005645751953/25000000000000),(729/81920),(81/409600),(110351563/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((9/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(586995391845701/50000000000000),(16305427551269/12500000000000),(2898742675781/50000000000000),(32208251953/25000000000000),(718919999/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((9/8)+(1/40)*x)) := (SharedCertificates.h22 (9/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((9/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(202728652954101/100000000000000),(13515243530273/50000000000000),(300338745117/20000000000000),(22247314453/50000000000000),(374096681/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((9/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(455227726527621/100000000000000),(60697030203681/100000000000000),(674411446707/20000000000000),(99912806919/100000000000000),(52502193/3125000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((9/8)+(1/40)*x)) := (SharedCertificates.h26 (9/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((9/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(228069734573363/100000000000000),(17738757133483/50000000000000),(591291904449/25000000000000),(43799400329/50000000000000),(493197023/25000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((9/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(5412131002971/10000000000000),(1683774089813/20000000000000),(561258029937/100000000000000),(20787334441/100000000000000),(468145749/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((9/8)+(1/40)*x)) := (SharedCertificates.h30 (9/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((9/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((9/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((9/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((9/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((9/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (9/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((9/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((9/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (9/8) (1/40))

def c43 : Certificate := ⟨(289/64),(17/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((9/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((9/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(26363486571/25000000000000),(-99250773/4000000000000),(8757421/20000000000000),(-686857/100000000000000),(5223/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((9/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1050850222437971/100000000000000),(354821520061/100000000000000),(-855306659/20000000000000),(51518791/100000000000000),(207478371/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((9/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((9/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (9/8) (1/40))

def c52 : Certificate := ⟨(20833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((9/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (9/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((9/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (9/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((9/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (9/8) (1/40))

def c56 : Certificate := ⟨(24742268041237/100000000000000),(-51014985653/100000000000000),(105185537/100000000000000),(-108439/50000000000000),(451/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((9/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1030927835051/100000000000000),(12753746413/6250000000000),(-8414843/2000000000000),(867509/100000000000000),(1833/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((9/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((9/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((9/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((9/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((9/8)+(1/40)*x)) := (SharedCertificates.h61 (9/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-14496758422779/100000000000000),(-576416745099/20000000000000),(430501633/12500000000000),(-1949653/100000000000000),(14461/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((9/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((9/8)+(1/40)*x)) := (SharedCertificates.h61 (9/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-583297632339/4000000000000),(-1458066738393/50000000000000),(52855483/50000000000000),(1372601/20000000000000),(1097/1562500000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((9/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((9/8)+(1/40)*x)) := (SharedCertificates.h67 (9/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-14463056578979/20000000000000),(-114752129077/800000000000),(23563734479/100000000000000),(-9659253/20000000000000),(141267/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((9/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((9/8)+(1/40)*x)) := (SharedCertificates.h67 (9/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-7291046683393/10000000000000),(-14579638962329/100000000000000),(728745381/100000000000000),(46584593/100000000000000),(454187/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((9/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((9/8)+(1/40)*x)) := (SharedCertificates.h72 (9/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(53747884191549/50000000000000),(84508829443/400000000000),(-14722970149/20000000000000),(153765957/100000000000000),(46337/20000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((9/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((9/8)+(1/40)*x)) := (SharedCertificates.h72 (9/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(54677813239059/25000000000000),(21863456038559/50000000000000),(-4553909059/100000000000000),(-58201317/20000000000000),(1005759/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((9/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((9/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((9/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(6379530237007/6250000000000),(412327306713/100000000000000),(-86750959/20000000000000),(8943/25000000000000),(1129/12500000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((9/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(424284798608039/4000000000000),(10488841539321/50000000000000),(-88327679859/100000000000000),(23229541/12500000000000),(342611/20000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((9/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(235690744349/25000000000000),(-932250367/50000000000000),(5769001/50000000000000),(-27431/50000000000000),(393/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((9/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(206192872027/10000000000000),(51020408163/12500000000000),(-832986257/100000000000000),(2266627/100000000000000),(9789/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((9/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((9/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((9/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (9/8) (1/40))

def c87 : Certificate := ⟨(3030303030303/12500000000000),(-18365472911/12500000000000),(890447171/100000000000000),(-107933/2000000000000),(3291/10000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((9/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(10101010101/1000000000000),(48974594429/25000000000000),(-74203931/6250000000000),(1798883/25000000000000),(23311/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((9/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((9/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((9/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((9/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((9/8)+(1/40)*x)) := (SharedCertificates.h61 (9/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-14202632384437/100000000000000),(-2766322545929/100000000000000),(7231510367/50000000000000),(-73699689/100000000000000),(914219/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((9/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((9/8)+(1/40)*x)) := (SharedCertificates.h61 (9/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-892804692161/6250000000000),(-1399171333219/50000000000000),(11517213257/100000000000000),(-41327501/100000000000000),(148591/12500000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((9/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((9/8)+(1/40)*x)) := (SharedCertificates.h67 (9/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-3542568118721/5000000000000),(-1376913636619/10000000000000),(38956214671/50000000000000),(-89869369/20000000000000),(5791/156250000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((9/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((9/8)+(1/40)*x)) := (SharedCertificates.h67 (9/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-35711370517007/50000000000000),(-13990765295119/100000000000000),(462104593/800000000000),(-98609599/50000000000000),(3077399/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((9/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((9/8)+(1/40)*x)) := (SharedCertificates.h72 (9/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(52669582115937/50000000000000),(20288092807607/100000000000000),(-6025553809/4000000000000),(1027663591/100000000000000),(3514117/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((9/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((9/8)+(1/40)*x)) := (SharedCertificates.h72 (9/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(107124638022437/50000000000000),(20980617604389/50000000000000),(-175381633419/100000000000000),(237518961/50000000000000),(5161701/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((9/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((9/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((9/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(51015202530353/50000000000000),(24734643651/6250000000000),(-1007374579/50000000000000),(988477/10000000000000),(136831/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((9/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5302489232700381/50000000000000),(4029498311143/20000000000000),(-81811026403/50000000000000),(145540477/12500000000000),(13413581/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((9/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(942953352769/100000000000000),(-895718213/50000000000000),(561001/3125000000000),(-165273/100000000000000),(3191/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((9/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(505067682937/25000000000000),(39183673469/10000000000000),(-2367013747/100000000000000),(7400017/50000000000000),(312969/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((9/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((9/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-42897802021893/100000000000000),(-4196158628647/50000000000000),(36291202701/100000000000000),(-222808501/100000000000000),(144497/1000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((9/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(11111111111111/12500000000000),(-246913580247/12500000000000),(43895747599/100000000000000),(-487730529/50000000000000),(5542393/25000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((9/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-4766422446877/12500000000000),(-6612473571483/100000000000000),(179202703989/100000000000000),(-522541789/12500000000000),(7947763/6250000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((9/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((9/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((9/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((9/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((9/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((9/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((9/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((9/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((9/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((9/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (9/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((9/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((9/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(66062971107/100000000000000),(-5872264099/100000000000000),(163118447/50000000000000),(-7249709/50000000000000),(8629/1250000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((9/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(7743922117841/5000000000000),(-1395029741283/100000000000000),(23660329817/100000000000000),(-24250323/4000000000000),(1571633051/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((9/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((9/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (9/8) (1/40))

def c134 : Certificate := ⟨(825/64),(29/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((9/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((9/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(7843137254901/100000000000000),(-92272202999/100000000000000),(1085555329/100000000000000),(-319281/2500000000000),(152041/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((9/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(50551470588229/50000000000000),(116061130333/50000000000000),(2171110653/100000000000000),(-2554249/10000000000000),(226991/6250000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((9/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((9/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (9/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((9/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (9/8) (1/40))

def c140 : Certificate := ⟨(2493125572869/10000000000000),(-1442796561/10000000000000),(-63299789/50000000000000),(1738999/100000000000000),(56817/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((9/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(274977085239/100000000000000),(14427965609/25000000000000),(50639831/10000000000000),(-6955997/100000000000000),(914081/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((9/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((9/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(378061987/50000000000000),(158694397/50000000000000),(36091549/100000000000000),(68281/12500000000000),(11629/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((9/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((9/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(1133666169/12500000000000),(475755911/12500000000000),(432526101/100000000000000),(1626801/25000000000000),(140473/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((9/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-38496766994883/100000000000000),(-2019911260301/25000000000000),(-14178466317/20000000000000),(194825147/20000000000000),(127977451/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((9/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-38549720577357/50000000000000),(-16203755855723/100000000000000),(-146844325077/100000000000000),(374241429/20000000000000),(257570651/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((9/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(412711609457/390625000000),(2213001489889/10000000000000),(184817641549/100000000000000),(-2834352561/100000000000000),(353707389/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((9/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(144508232131803/50000000000000),(30359641509073/50000000000000),(13638327659/2500000000000),(-7100212247/100000000000000),(964399997/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((9/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(58063079519907/20000000000000),(61264977355589/100000000000000),(303865007363/50000000000000),(-6138415239/100000000000000),(983881959/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((9/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(25137677573613/25000000000000),(57870556833/50000000000000),(1048888169/100000000000000),(-6682873/50000000000000),(1839791/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((9/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((9/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((9/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((9/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(13197220853464733/25000000000000),(1895727529601/3125000000000),(539116628159/100000000000000),(-1801051901/25000000000000),(12123511/1250000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((9/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(189433823057/100000000000000),(-54422809/25000000000000),(-842233/50000000000000),(30011/100000000000000),(1769/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((9/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(109991111319/20000000000000),(57712298811/50000000000000),(20259749/2000000000000),(-13896071/100000000000000),(950113/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((9/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((9/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((9/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (9/8) (1/40))

def c175 : Certificate := ⟨(6198723792161/25000000000000),(-21405856197/50000000000000),(-65302181/20000000000000),(2983059/50000000000000),(68553/10000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((9/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(136736554237/50000000000000),(5708228319/10000000000000),(13604621/3125000000000),(-318193/4000000000000),(929161/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((9/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((9/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(74787541/10000000000000),(78052347/25000000000000),(34964989/100000000000000),(3543/781250000000),(13409/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((9/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((9/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(8970414443/100000000000000),(3743951229/100000000000000),(104756421/25000000000000),(107941/2000000000000),(161647/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((9/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-38286210654689/100000000000000),(-7991504287383/100000000000000),(-60945379973/100000000000000),(556972517/50000000000000),(2601753/2000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((9/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-15335434572623/20000000000000),(-8013374275789/50000000000000),(-126792484697/100000000000000),(1081931541/50000000000000),(262042281/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((9/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(105077455314371/100000000000000),(10944540549871/50000000000000),(19722492617/12500000000000),(-3192738661/100000000000000),(360009777/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((9/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(287434122481053/100000000000000),(60056238710611/100000000000000),(94099798207/20000000000000),(-4092149109/50000000000000),(490447721/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((9/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(288718873956827/100000000000000),(60593020594727/100000000000000),(530754263211/100000000000000),(-295320379/4000000000000),(1003528067/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((9/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(50273847046179/50000000000000),(14309596971/12500000000000),(905660733/100000000000000),(-7728073/50000000000000),(1871731/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((9/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((9/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((9/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((9/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(26393651263735963/50000000000000),(6000115300073/10000000000000),(18571314943/4000000000000),(-8271575521/100000000000000),(39486271/4000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((9/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(37887899253/20000000000000),(-8613123/4000000000000),(-1421433/100000000000000),(16597/50000000000000),(903/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((9/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(109389516089/20000000000000),(3567669381/3125000000000),(108860059/12500000000000),(-15894651/100000000000000),(486161/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((9/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((9/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(169886649281/10000000000000),(170141659201/50000000000000),(-12806419/50000000000000),(-24748233/100000000000000),(6039271/12500000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((9/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(377525887291/25000000000000),(268916204153/100000000000000),(-1199736523/20000000000000),(27826407/25000000000000),(4722663/10000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((9/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((9/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((9/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((9/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((9/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((9/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (9/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((9/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((9/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((9/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (9/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((9/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(11517834647/25000000000000),(-4701157/1250000000000),(5577427/100000000000000),(-32999/50000000000000),(427/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((9/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(124671561745457/25000000000000),(-631717972241/50000000000000),(1459916263/100000000000000),(-80680019/100000000000000),(17727271/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((9/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((9/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((9/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((9/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (9/8) (1/40))

def c223 : Certificate := ⟨(625/64),(5/32),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((9/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1700625/4096),(11865/1024),(5723/51200),(53/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((9/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((9/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(61514801999/25000000000000),(-723703553/12500000000000),(102169913/100000000000000),(-801333/50000000000000),(2437/10000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((9/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(102161728661669/100000000000000),(447261516827/100000000000000),(2840012471/100000000000000),(-3355617/12500000000000),(20186189/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((9/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((9/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (9/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((9/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (9/8) (1/40))

def c231 : Certificate := ⟨(24865618201111/100000000000000),(-6913533363/25000000000000),(-36210579/25000000000000),(1008097/50000000000000),(1254001/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((9/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(268763597777/50000000000000),(22123306761/20000000000000),(579369263/100000000000000),(-403239/5000000000000),(5070213/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((9/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((9/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(2889354859/100000000000000),(1189187903/100000000000000),(12858871/10000000000000),(239011/20000000000000),(80367/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((9/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((9/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(34641196171/100000000000000),(1425107821/10000000000000),(384754441/25000000000000),(7015009/50000000000000),(968097/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((9/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-7525362117171/10000000000000),(-15486199810389/100000000000000),(-10135932429/12500000000000),(226185359/20000000000000),(354929239/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((9/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-75456061717279/50000000000000),(-15569557474121/50000000000000),(-90112777293/50000000000000),(2090868059/100000000000000),(143091293/10000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((9/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(206136776583441/100000000000000),(10563262635897/25000000000000),(37353811363/20000000000000),(-865325077/25000000000000),(489764537/25000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((9/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(282755798282937/50000000000000),(58301251745013/50000000000000),(164318703421/25000000000000),(-1006481283/12500000000000),(535522601/10000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((9/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(285241556291403/50000000000000),(59325999740967/50000000000000),(175983976803/20000000000000),(-5840567939/100000000000000),(5491648321/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((9/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(101077943745967/100000000000000),(222422255513/100000000000000),(321831809/25000000000000),(-2986901/20000000000000),(10220793/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((9/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((9/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((9/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((9/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(53065000508981789/100000000000000),(29097756917811/25000000000000),(31702991597/5000000000000),(-1663178947/20000000000000),(1078562989/20000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((9/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(47112031961/25000000000000),(-413335929/100000000000000),(-1345121/100000000000000),(37421/100000000000000),(1937/10000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((9/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(67191546583/6250000000000),(221239459999/100000000000000),(232017503/20000000000000),(-16025999/100000000000000),(528123/5000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((9/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((9/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((9/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (9/8) (1/40))

def c259 : Certificate := ⟨(24601142537993/100000000000000),(-81206976589/100000000000000),(-123793427/50000000000000),(7393487/100000000000000),(465641/12500000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((9/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(531809949341/100000000000000),(6767248049/6250000000000),(82528951/25000000000000),(-9857983/100000000000000),(512789/10000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((9/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((9/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(1414109111/50000000000000),(1151644749/100000000000000),(120748031/100000000000000),(30501/5000000000000),(86007/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((9/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((9/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(8477134293/25000000000000),(13801363303/100000000000000),(144517949/10000000000000),(7045223/100000000000000),(103369/10000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((9/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-37226606289383/50000000000000),(-757926275897/5000000000000),(-9238694291/20000000000000),(1381762087/100000000000000),(44870089/6250000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((9/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-74651367703789/50000000000000),(-30478500743609/100000000000000),(-109336908777/100000000000000),(334358257/12500000000000),(57914073/4000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((9/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(203952823694749/100000000000000),(41362501299291/100000000000000),(11627419513/12500000000000),(-1992689979/50000000000000),(1982982449/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((9/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(27974254410821/5000000000000),(114130569016123/100000000000000),(392575209889/100000000000000),(-1015492067/10000000000000),(5417676977/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((9/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(282175620768239/50000000000000),(116115258464671/100000000000000),(120328591641/20000000000000),(-8965544483/100000000000000),(2782425239/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((9/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(12633306014613/12500000000000),(217703582317/100000000000000),(780979639/100000000000000),(-9552973/50000000000000),(10341787/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((9/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((9/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((9/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((9/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(53058984871768479/100000000000000),(5696290219513/5000000000000),(92694083413/25000000000000),(-10310295059/100000000000000),(5457479719/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((9/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(23558686677/12500000000000),(-202336501/50000000000000),(-448131/100000000000000),(40413/100000000000000),(3927/20000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((9/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(106362992601/10000000000000),(27069757787/12500000000000),(6614973/1000000000000),(-19624281/100000000000000),(10725123/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((9/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((9/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(2133075238179/20000000000000),(2156214996091/100000000000000),(89598121/2500000000000),(-196131623/100000000000000),(4280417/4000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((9/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(4740167195953/50000000000000),(852980727241/50000000000000),(-4340567947/12500000000000),(597317303/100000000000000),(57917073/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((9/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((9/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((9/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((9/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((9/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((9/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (9/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((9/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(420324594951886611/50000000000000),(3431221183280707/50000000000000),(-45749615777077/100000000000000),0,(109421/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((9/8)+(1/40)*x)) := (SharedCertificates.h297 (9/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(1486946059/12500000000000),(-48553341/50000000000000),(288017/20000000000000),(-17041/100000000000000),(223/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((9/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(151076042947617/25000000000000),(219248663971/50000000000000),(1107774833/12500000000000),(-48505621/100000000000000),(2162917/10000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((9/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((9/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (9/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((9/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (9/8) (1/40))

def c307 : Certificate := ⟨(263864036478433/12500000000000),(11091229182759/50000000000000),0,0,(101/10000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((9/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (9/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((9/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (9/8) (1/40))

def c311 : Certificate := ⟨(2014087708172277/100000000000000),(2817541634481/100000000000000),0,0,(1009/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((9/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (9/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2482513536879/50000000000000),(-3472830513/50000000000000),(9716403/100000000000000),(-13593/100000000000000),(3/12500000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((9/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(104807366792519/100000000000000),(477374125563/50000000000000),(-1335613621/100000000000000),(4671/250000000000),(179/5000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((9/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((9/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (9/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((9/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (9/8) (1/40))

def c316 : Certificate := ⟨(12351553875161/50000000000000),(-3641430909/6250000000000),(54729861/25000000000000),(-822577/100000000000000),(791/25000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((9/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(1187568998709/100000000000000),(9322063127/4000000000000),(-437838889/50000000000000),(658061/20000000000000),(12951/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((9/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((9/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(7051600633/50000000000000),(2767648293/50000000000000),(20893273/4000000000000),(-4003413/100000000000000),(23433/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((9/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((9/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(168903444699/100000000000000),(66226352633/100000000000000),(6230022603/100000000000000),(-2514223/5000000000000),(61661/20000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((9/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-83128826987157/50000000000000),(-8156510207181/25000000000000),(122821737247/100000000000000),(-447295069/100000000000000),(496931/25000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((9/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3344937439951/1000000000000),(-16507341180453/25000000000000),(172068748997/100000000000000),(-22508171/6250000000000),(6879731/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((9/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(226620860248329/50000000000000),(88161170382617/100000000000000),(-486045898569/100000000000000),(278837271/12500000000000),(4788319/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((9/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(1252330006806283/100000000000000),(246807418794677/100000000000000),(-1413558077/195312500000),(1591478949/100000000000000),(26196109/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((9/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(1276692014489173/100000000000000),(256403323557631/100000000000000),(191792886093/100000000000000),(-412082749/10000000000000),(3196379/6250000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((9/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(25597310299671/25000000000000),(58954806617/12500000000000),(-1229023731/100000000000000),(2577197/100000000000000),(9867/20000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((9/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((9/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((9/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((9/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(53749802978669391/100000000000000),(122901978769589/50000000000000),(-164374417157/20000000000000),(37790811/2000000000000),(10359251/25000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((9/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(93023596793/50000000000000),(-850814961/100000000000000),(1347133/20000000000000),(-50353/100000000000000),(513/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((9/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(2375249663693/100000000000000),(18646756043/4000000000000),(-1738698859/100000000000000),(7329129/100000000000000),(184959/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((9/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((9/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((9/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (9/8) (1/40))

def c344 : Certificate := ⟨(12064993627137/50000000000000),(-166772450913/100000000000000),(1385935103/100000000000000),(-2303517/20000000000000),(9669/10000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((9/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(1160016994301/100000000000000),(111181633941/50000000000000),(-1804603/97656250000),(7678389/50000000000000),(17277/12500000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((9/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((9/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(1345639427/10000000000000),(5158903393/100000000000000),(56447751/12500000000000),(-196547/2500000000000),(53421/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((9/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((9/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((9/8)+(1/40)*x)) := (SharedCertificates.h144 (9/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(161164538319/100000000000000),(61727308247/100000000000000),(336628847/6250000000000),(-5998871/6250000000000),(1330661/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((9/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((9/8)+(1/40)*x)) := (SharedCertificates.h148 (9/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-162400509666107/100000000000000),(-31129783085481/100000000000000),(258904645987/100000000000000),(-1070100811/50000000000000),(19674627/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((9/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((9/8)+(1/40)*x)) := (SharedCertificates.h151 (9/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-326688631915239/100000000000000),(-3936496553837/6250000000000),(90839785599/20000000000000),(-1599351871/50000000000000),(13411051/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((9/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((9/8)+(1/40)*x)) := (SharedCertificates.h154 (9/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(221408449578609/50000000000000),(8415279815277/10000000000000),(-420097068381/50000000000000),(1999736389/25000000000000),(1972487/2500000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((9/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((9/8)+(1/40)*x)) := (SharedCertificates.h157 (9/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(122315459529991/10000000000000),(235442280163551/100000000000000),(-1771113501521/100000000000000),(6431027201/50000000000000),(193462497/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((9/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((9/8)+(1/40)*x)) := (SharedCertificates.h160 (9/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(249279089272031/20000000000000),(244383465258149/100000000000000),(-979530961617/100000000000000),(220544257/100000000000000),(5476781/1562500000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((9/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((9/8)+(1/40)*x)) := (SharedCertificates.h41 (9/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(12791686297859/12500000000000),(449885439157/100000000000000),(-405530617/12500000000000),(5712919/25000000000000),(191637/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((9/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((9/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((9/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((9/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((9/8)+(1/40)*x)) := (SharedCertificates.h167 (9/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(10744148955131581/20000000000000),(234507810913637/100000000000000),(-185596964307/10000000000000),(13943208393/100000000000000),(62825199/25000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((9/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(186147828771/100000000000000),(-203148337/25000000000000),(4989173/50000000000000),(-29987/25000000000000),(1973/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((9/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(23201380613/1000000000000),(222393193983/50000000000000),(-14739399/400000000000),(31260543/100000000000000),(215731/20000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((9/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((9/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(2837442390387/10000000000000),(5525529964531/100000000000000),(-14182050657/50000000000000),(143935011/50000000000000),(9614879/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((9/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(25221710136773/100000000000000),(435109974321/10000000000000),(-121903639907/100000000000000),(2964854239/100000000000000),(22176207/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((9/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((9/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(85095977783203/25000000000000),(8565216064453/25000000000000),(5589/409600),(549/2048000),(129882813/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((9/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1089/64),(33/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((9/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(35937/512),(3267/2560),(99/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((9/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(23891360574960673/100000000000000),(2839139699935877/100000000000000),(71064527034759/50000000000000),(3893187332153/100000000000000),(16023543609/25000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((9/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(104640336081/25000000000000),(-248699551/500000000000),(1710426359/50000000000000),(-178823223/100000000000000),(123499/1000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((9/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1014430200007/50000000000000),(81687409181/25000000000000),(-3384617601/25000000000000),(198682257/50000000000000),(33298871/20000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((9/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((9/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((9/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel2

namespace Hf4Quad.Panel3
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(47/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((47/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (47/40) (1/40)

def c3 : Certificate := ⟨(205904761904761/100000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((47/40)+(1/40)*x)) := (SharedCertificates.h2 (47/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((47/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-11447619047619/10000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((47/40)+(1/40)*x)) := (SharedCertificates.h4 (47/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(2209/1600),(47/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((47/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(83567989417989/50000000000000),(7112169312169/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((47/40)+(1/40)*x)) := (SharedCertificates.h8 (47/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((47/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((47/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(103823/64000),(6627/64000),(141/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((47/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1580476860532407/100000000000000),(100881501736111/100000000000000),(429282986111/20000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((47/40)+(1/40)*x)) := (SharedCertificates.h13 (47/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((47/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((47/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(4879681/2560000),(103823/640000),(6627/1280000),(47/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((47/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(266252435515873/50000000000000),(45319563492063/100000000000000),(1446369047619/100000000000000),(4103174603/20000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((47/40)+(1/40)*x)) := (SharedCertificates.h18 (47/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((47/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(223969733398437/100000000000000),(5956641845703/25000000000000),(103823/10240000),(2209/10240000),(230468751/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((47/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(1459121337214261/100000000000000),(155225674171727/100000000000000),(3302673918547/50000000000000),(70269657841/50000000000000),(375365309/25000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((47/40)+(1/40)*x)) := (SharedCertificates.h22 (47/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((47/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(263164436743163/100000000000000),(6719092001953/20000000000000),(178699255371/10000000000000),(25347412109/50000000000000),(101983643/12500000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((47/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(295468219454493/50000000000000),(15087738865761/20000000000000),(4012696506849/100000000000000),(56917680947/50000000000000),(458009081/25000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((47/40)+(1/40)*x)) := (SharedCertificates.h26 (47/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((47/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(9663069161663/3125000000000),(11513444107513/25000000000000),(2939602750853/100000000000000),(52120616149/50000000000000),(2246413581/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((47/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(18344493202141/25000000000000),(10928634248083/100000000000000),(697572398813/100000000000000),(12368304943/50000000000000),(66634689/12500000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((47/40)+(1/40)*x)) := (SharedCertificates.h30 (47/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((47/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((47/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((47/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((47/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((47/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (47/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((47/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((47/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (47/40) (1/40))

def c43 : Certificate := ⟨(7569/1600),(87/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((47/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((47/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(50330609189/50000000000000),(-1157025499/50000000000000),(3989743/10000000000000),(-122291/20000000000000),(9079/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((47/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1050157283151401/100000000000000),(42289283023/12500000000000),(-796350627/20000000000000),(46838919/100000000000000),(188798803/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((47/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((47/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (47/40) (1/40))

def c52 : Certificate := ⟨(26458333333333/25000000000000),(833333333333/100000000000000),0,0,(1/25000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((47/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (47/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((47/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (47/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((47/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (47/40) (1/40))

def c56 : Certificate := ⟨(6160164271047/25000000000000),(-12649207949/25000000000000),(103894931/100000000000000),(-213337/100000000000000),(443/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((47/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1437371663243/100000000000000),(10119366359/5000000000000),(-25973733/6250000000000),(426673/50000000000000),(1811/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((47/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((47/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((47/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((47/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((47/40)+(1/40)*x)) := (SharedCertificates.h61 (47/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-202471655233/1000000000000),(-2868331277611/100000000000000),(1716079741/50000000000000),(-400213/20000000000000),(56843/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((47/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((47/40)+(1/40)*x)) := (SharedCertificates.h61 (47/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-5103557576311/25000000000000),(-583125771729/20000000000000),(146453187/100000000000000),(3359037/50000000000000),(13907/20000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((47/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((47/40)+(1/40)*x)) := (SharedCertificates.h67 (47/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-100909444788687/100000000000000),(-14250337140699/100000000000000),(23276660121/100000000000000),(-5924837/12500000000000),(28051/20000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((47/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((47/40)+(1/40)*x)) := (SharedCertificates.h67 (47/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-102066460191939/100000000000000),(-7288085569379/50000000000000),(1003635819/100000000000000),(450539/1000000000000),(222911/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((47/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((47/40)+(1/40)*x)) := (SharedCertificates.h72 (47/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(3736423756601/2500000000000),(4166917203927/20000000000000),(-72697601119/100000000000000),(75992393/50000000000000),(116719/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((47/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((47/40)+(1/40)*x)) := (SharedCertificates.h72 (47/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(153072276492357/50000000000000),(2731577714553/6250000000000),(-783839293/12500000000000),(-140653747/50000000000000),(98583/5000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((47/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((47/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((47/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(25723850924867/25000000000000),(410592770541/100000000000000),(-86700001/20000000000000),(24531/50000000000000),(8873/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((47/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10648723504010797/100000000000000),(10313297876043/50000000000000),(-43608825427/50000000000000),(184169199/100000000000000),(1684503/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((47/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(187815938619/20000000000000),(-909499491/50000000000000),(1401859/12500000000000),(-52863/100000000000000),(189/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((47/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(574988265719/20000000000000),(404858299593/100000000000000),(-819551219/100000000000000),(553003/25000000000000),(9649/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((47/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((47/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((47/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (47/40) (1/40))

def c87 : Certificate := ⟨(23952095808383/100000000000000),(-35856430851/25000000000000),(858836667/100000000000000),(-1028547/20000000000000),(30983/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((47/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(698602794411/50000000000000),(191234297871/100000000000000),(-1145115557/100000000000000),(6856979/100000000000000),(1797/4000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((47/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((47/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((47/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((47/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((47/40)+(1/40)*x)) := (SharedCertificates.h61 (47/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-3935601850191/20000000000000),(-1354671702883/50000000000000),(14029379819/100000000000000),(-14173827/20000000000000),(1749/200000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((47/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((47/40)+(1/40)*x)) := (SharedCertificates.h61 (47/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-4958955122133/25000000000000),(-1376383185253/50000000000000),(11271779183/100000000000000),(-5060389/12500000000000),(1136653/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((47/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((47/40)+(1/40)*x)) := (SharedCertificates.h67 (47/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-19616307681999/20000000000000),(-2692559109717/20000000000000),(2352452767/3125000000000),(-428836437/100000000000000),(1784731/50000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((47/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((47/40)+(1/40)*x)) := (SharedCertificates.h67 (47/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-6198424497113/6250000000000),(-6881034662053/50000000000000),(14146887163/25000000000000),(-12161427/6250000000000),(5866989/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((47/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((47/40)+(1/40)*x)) := (SharedCertificates.h72 (47/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(36330227772607/25000000000000),(19697660657663/100000000000000),(-72314309883/50000000000000),(244067519/25000000000000),(842741/12500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((47/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((47/40)+(1/40)*x)) := (SharedCertificates.h72 (47/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(59494807487117/20000000000000),(41265443032029/100000000000000),(-172506603897/100000000000000),(241447417/50000000000000),(9793451/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((47/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((47/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((47/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(51406966506109/50000000000000),(387812468337/100000000000000),(-391304957/20000000000000),(4762931/50000000000000),(130777/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((47/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1330578519297347/12500000000000),(9753367467153/50000000000000),(-78407711579/50000000000000),(221030957/20000000000000),(2551741/10000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((47/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(234860247229/25000000000000),(-860782833/50000000000000),(16994577/100000000000000),(-154041/100000000000000),(149/5000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((47/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(2794593039053/100000000000000),(191271637603/50000000000000),(-2280454991/100000000000000),(14060981/100000000000000),(59199/20000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((47/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((47/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-14884757020657/25000000000000),(-4124887070961/50000000000000),(34993085973/100000000000000),(-210076623/100000000000000),(4065197/25000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((47/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(85106382978723/100000000000000),(-1810774105931/100000000000000),(9631777159/25000000000000),(-204931429/25000000000000),(17820127/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((47/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-50671513261811/100000000000000),(-5942967072661/100000000000000),(156227457693/100000000000000),(-3502777077/100000000000000),(22301401/20000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((47/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((47/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((47/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((47/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((47/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((47/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((47/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((47/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((47/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((47/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (47/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((47/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((47/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(3469738479/6250000000000),(-472475027/10000000000000),(251316503/100000000000000),(-133679/1250000000000),(4843/1000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((47/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(152178524365903/100000000000000),(-1306976958097/100000000000000),(5130211243/25000000000000),(-225483797/50000000000000),(1291659661/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((47/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((47/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (47/40) (1/40))

def c134 : Certificate := ⟨(21209/1600),(147/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((47/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((47/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3831417624521/50000000000000),(-88078566081/100000000000000),(1012397311/100000000000000),(-11636751/100000000000000),(8457/6250000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((47/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(50787835249041/50000000000000),(30063691813/12500000000000),(1012397309/50000000000000),(-11636753/50000000000000),(3331373/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((47/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((47/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (47/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((47/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (47/40) (1/40))

def c140 : Certificate := ⟨(24901906999487/100000000000000),(-7457057911/50000000000000),(-364457/312500000000),(1588249/100000000000000),(52019/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((47/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(7847440041/2000000000000),(14914115821/25000000000000),(116626239/25000000000000),(-6352999/100000000000000),(838851/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((47/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((47/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(1539557879/100000000000000),(234075259/50000000000000),(7849961/20000000000000),(101349/20000000000000),(13059/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((47/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((47/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(18462612959/100000000000000),(5612295541/100000000000000),(470116721/100000000000000),(150649/2500000000000),(15757/10000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((47/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-13733001961219/25000000000000),(-4175935912271/50000000000000),(-2040794219/3125000000000),(889748967/100000000000000),(23489037/20000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((47/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-27519924598237/25000000000000),(-8384675309649/50000000000000),(-34029079933/25000000000000),(853949939/50000000000000),(236706227/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((47/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(75315649436407/50000000000000),(22836270472729/100000000000000),(168552796987/100000000000000),(-1295820983/50000000000000),(324713123/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((47/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(412581637195601/100000000000000),(62818750885353/100000000000000),(31551098223/6250000000000),(-3241651231/50000000000000),(442976491/50000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((47/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(41522831181241/10000000000000),(63624516055043/100000000000000),(572592047109/100000000000000),(-2792765551/50000000000000),(90792847/10000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((47/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(100786283561979/100000000000000),(59890538543/50000000000000),(972259717/100000000000000),(-12199253/100000000000000),(1690761/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((47/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((47/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((47/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((47/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(52912310096140573/100000000000000),(31367928826881/50000000000000),(99558819213/20000000000000),(-6581671567/100000000000000),(892088411/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((47/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(188991937449/100000000000000),(-112039819/50000000000000),(-1512337/100000000000000),(27409/100000000000000),(1621/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((47/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(784748031331/100000000000000),(59657381743/50000000000000),(466651783/50000000000000),(-12687673/100000000000000),(438761/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((47/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((47/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((47/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (47/40) (1/40))

def c175 : Certificate := ⟨(12354006177003/50000000000000),(-44048302049/100000000000000),(-146152639/50000000000000),(1088931/20000000000000),(625401/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((47/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(97329215331/25000000000000),(58731069397/100000000000000),(38974037/10000000000000),(-7259541/100000000000000),(426787/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((47/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((47/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(303135237/20000000000000),(457299911/100000000000000),(7505607/20000000000000),(50159/12500000000000),(14723/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((47/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((47/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(9088156327/50000000000000),(1096451579/20000000000000),(89899049/20000000000000),(4764713/100000000000000),(35463/20000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((47/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-54504289821911/100000000000000),(-8222317697083/100000000000000),(-54558611211/100000000000000),(101663833/10000000000000),(5975261/5000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((47/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-54610457780571/50000000000000),(-16508721252627/100000000000000),(-114381189807/100000000000000),(988248819/50000000000000),(60265469/25000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((47/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(18682722021171/12500000000000),(4496608774141/20000000000000),(2179426729/1562500000000),(-2910817957/100000000000000),(66169257/20000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((47/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(409364584286061/100000000000000),(61842933647061/100000000000000),(105889366381/25000000000000),(-467197191/6250000000000),(11275313/1250000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((47/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(411970155092029/100000000000000),(15657500299867/25000000000000),(488358300407/100000000000000),(-6760584693/100000000000000),(46348663/5000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((47/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(100780149398833/100000000000000),(23583887741/20000000000000),(32680351/4000000000000),(-1411781/10000000000000),(1721871/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((47/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((47/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((47/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((47/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(3306818579478711/6250000000000),(30880984527431/50000000000000),(416842288767/100000000000000),(-1510857237/20000000000000),(908882127/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((47/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(189003413697/100000000000000),(-2206279/1000000000000),(-1231513/100000000000000),(30161/100000000000000),(663/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((47/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(97329707067/12500000000000),(117463919163/100000000000000),(48735071/6250000000000),(-14502233/100000000000000),(449461/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((47/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((47/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(2379137269943/100000000000000),(339893214561/100000000000000),(-83453143/50000000000000),(-694623/3125000000000),(163679/312500000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((47/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(2024797676547/100000000000000),(123095009637/50000000000000),(-269006671/5000000000000),(95553531/100000000000000),(1515169/3125000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((47/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((47/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((47/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((47/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((47/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((47/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (47/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((47/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((47/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((47/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (47/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((47/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(9068189669/20000000000000),(-354548683/100000000000000),(5200849/100000000000000),(-29829/50000000000000),(189/25000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((47/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(496164580834699/100000000000000),(-314635395557/25000000000000),(19855329/2000000000000),(-75170389/100000000000000),(15875933/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((47/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((47/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((47/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((47/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (47/40) (1/40))

def c223 : Certificate := ⟨(16129/1600),(127/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((47/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1123368721/2560000),(7704963/640000),(146267/1280000),(267/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((47/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((47/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(46975235243/20000000000000),(-5399452327/100000000000000),(18618801/20000000000000),(-1426729/100000000000000),(1059/5000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((47/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(25766850553517/25000000000000),(458309818199/100000000000000),(671663971/25000000000000),(-3040767/12500000000000),(18561251/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((47/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((47/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (47/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((47/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (47/40) (1/40))

def c231 : Certificate := ⟨(4961949264599/20000000000000),(-28210046917/100000000000000),(-133293611/100000000000000),(1836927/100000000000000),(1148033/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((47/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(47563419251/6250000000000),(7052511729/6250000000000),(533174443/100000000000000),(-14351/195312500000),(4662553/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((47/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((47/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(2895716929/50000000000000),(1717460849/100000000000000),(135444151/100000000000000),(218287/20000000000000),(95359/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((47/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((47/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(69409058969/100000000000000),(20570319799/100000000000000),(1619330583/100000000000000),(6378737/50000000000000),(22949/2000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((47/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-106541530909093/100000000000000),(-15797391408489/100000000000000),(-37304258509/50000000000000),(1030708597/100000000000000),(26111473/4000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((47/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-53473728741211/25000000000000),(-198973091759/625000000000),(-84125242077/50000000000000),(476153881/25000000000000),(263773503/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((47/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(291362890823579/100000000000000),(8591967701653/20000000000000),(8346392949/5000000000000),(-789563071/25000000000000),(1801748367/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((47/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(200320689467417/25000000000000),(14892237771197/12500000000000),(611132945571/100000000000000),(-3671564141/50000000000000),(4932890709/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((47/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(50703825168573/6250000000000),(122103848899263/100000000000000),(846550122889/100000000000000),(-2647490627/50000000000000),(509556713/10000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((47/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(10152782084989/10000000000000),(227397836177/100000000000000),(1201793037/100000000000000),(-13603989/100000000000000),(1884093/20000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((47/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((47/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((47/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((47/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(53300253772465773/100000000000000),(118830449889621/100000000000000),(586372446501/100000000000000),(-7594421531/100000000000000),(4977415637/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((47/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(187616367507/100000000000000),(-104570503/25000000000000),(-226297/20000000000000),(529/1562500000000),(4431/25000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((47/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(761029399747/50000000000000),(225693446209/100000000000000),(534174427/50000000000000),(-2916429/20000000000000),(9801333/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((47/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((47/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((47/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (47/40) (1/40))

def c259 : Certificate := ⟨(763681121283/3125000000000),(-20527898443/25000000000000),(-51362257/25000000000000),(6665961/100000000000000),(211329/6250000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((47/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(187401372981/25000000000000),(27370531257/25000000000000),(68483009/25000000000000),(-8887949/100000000000000),(4715787/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((47/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((47/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(1123816787/20000000000000),(1641368043/100000000000000),(968517/781250000000),(116641/25000000000000),(19963/20000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((47/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((47/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(4209047831/6250000000000),(19659505161/100000000000000),(1482158743/100000000000000),(5312329/100000000000000),(1198629/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((47/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-104944264049301/100000000000000),(-1532727640471/10000000000000),(-19158833287/50000000000000),(77876453/6250000000000),(660226551/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((47/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-210676205705493/100000000000000),(-30884784323909/100000000000000),(-94056305289/100000000000000),(484671211/20000000000000),(1334396219/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((47/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(143509436991297/50000000000000),(5211056413673/12500000000000),(35184177411/50000000000000),(-1786274061/50000000000000),(364745433/20000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((47/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(789237275762431/100000000000000),(5779148228119/5000000000000),(167291880941/50000000000000),(-1838679553/20000000000000),(2495096891/50000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((47/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(798918098447053/100000000000000),(118417211261611/100000000000000),(550054073331/100000000000000),(-8244612531/100000000000000),(2580835557/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((47/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(101504830067783/100000000000000),(220605618099/100000000000000),(83979281/12500000000000),(-8654667/50000000000000),(9531389/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((47/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((47/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((47/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((47/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(13322059784620551/25000000000000),(23057846677361/20000000000000),(311922238677/100000000000000),(-9325894667/100000000000000),(2518175433/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((47/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(37531733687/20000000000000),(-20299999/5000000000000),(-220077/100000000000000),(17847/50000000000000),(17963/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((47/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(1499239065431/100000000000000),(218976554531/100000000000000),(27484603/5000000000000),(-17680393/100000000000000),(4973463/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((47/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((47/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(1873826235909/12500000000000),(542067688829/25000000000000),(2461783487/100000000000000),(-178295591/100000000000000),(98872541/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((47/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(3189491465377/25000000000000),(12591125847/800000000000),(-6278380389/20000000000000),(258085939/50000000000000),(102721551/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((47/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((47/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((47/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((47/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((47/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((47/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (47/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((47/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(427095538086893873/50000000000000),(6679443903453109/100000000000000),(-45749615777077/100000000000000),0,(55573/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((47/40)+(1/40)*x)) := (SharedCertificates.h297 (47/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(5853491261/50000000000000),(-91544077/100000000000000),(1342853/100000000000000),(-3851/25000000000000),(99/50000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((47/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(605216241283037/100000000000000),(47339178083/10000000000000),(4295815277/50000000000000),(-2615609/6250000000000),(9754437/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((47/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((47/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (47/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((47/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (47/40) (1/40))

def c307 : Certificate := ⟨(1077638604279251/50000000000000),(11091229182759/50000000000000),0,0,(253/25000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((47/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (47/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((47/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (47/40) (1/40))

def c311 : Certificate := ⟨(2019722791441239/100000000000000),(2817541634481/100000000000000),0,0,(253/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((47/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (47/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2475587254443/50000000000000),(-3453478957/50000000000000),(9635303/100000000000000),(-6721/50000000000000),(23/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((47/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(53355767872989/50000000000000),(118678516789/12500000000000),(-52978623/4000000000000),(923817/50000000000000),(221/6250000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((47/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((47/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (47/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((47/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (47/40) (1/40))

def c316 : Certificate := ⟨(12293725553737/50000000000000),(-57396989711/100000000000000),(214057241/100000000000000),(-199577/25000000000000),(381/12500000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((47/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(825097785051/50000000000000),(114793979421/50000000000000),(-856228967/100000000000000),(319323/10000000000000),(6299/50000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((47/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((47/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(5446290839/20000000000000),(1894325163/25000000000000),(498847403/100000000000000),(-3826209/100000000000000),(11263/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((47/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((47/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(162939352919/50000000000000),(11319060873/12500000000000),(5935378107/100000000000000),(-47950797/100000000000000),(29541/10000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((47/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-231022002178313/100000000000000),(-32140071766483/100000000000000),(24035021613/20000000000000),(-869963/200000000000),(192787/10000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((47/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-116466768618617/25000000000000),(-16336350303889/25000000000000),(169915577633/100000000000000),(-11173729/3125000000000),(6658389/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((47/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(39227348541483/6250000000000),(43121731265421/50000000000000),(-472880496969/100000000000000),(1079114437/50000000000000),(371837/4000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((47/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(3486125192187/200000000000),(121965761441737/50000000000000),(-714213277843/100000000000000),(1584430219/100000000000000),(12642147/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((47/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(1790233232096779/100000000000000),(257121774824929/100000000000000),(33522669581/20000000000000),(-19701081/500000000000),(498371/1000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((47/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(103327622594399/100000000000000),(14586038073/3125000000000),(-1213610531/100000000000000),(2560251/100000000000000),(23861/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((47/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((47/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((47/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((47/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(27119069256790469/50000000000000),(12126956345447/5000000000000),(-810547980193/100000000000000),(1884799731/100000000000000),(39906359/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((47/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(92186054629/50000000000000),(-412232533/50000000000000),(6442099/100000000000000),(-2971/6250000000000),(3/625000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((47/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(1650345385327/50000000000000),(459300992007/100000000000000),(-1695518349/100000000000000),(353323/5000000000000),(5669/3125000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((47/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((47/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((47/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (47/40) (1/40))

def c344 : Certificate := ⟨(11900947729279/50000000000000),(-5042622533/3125000000000),(65953233/5000000000000),(-5391327/50000000000000),(89037/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((47/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(1597472721921/100000000000000),(10757594737/5000000000000),(-1758752881/100000000000000),(1437687/10000000000000),(26133/20000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((47/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((47/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(6379797743/25000000000000),(3436992829/50000000000000),(406712183/100000000000000),(-888581/12500000000000),(383/390625000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((47/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((47/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((47/40)+(1/40)*x)) := (SharedCertificates.h144 (47/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(152707483717/50000000000000),(41079198879/50000000000000),(4838870581/100000000000000),(-43296151/50000000000000),(243449/20000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((47/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((47/40)+(1/40)*x)) := (SharedCertificates.h148 (47/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-223641302148147/100000000000000),(-15059647849759/50000000000000),(3851157763/1562500000000),(-2005135221/100000000000000),(1857673/10000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((47/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((47/40)+(1/40)*x)) := (SharedCertificates.h151 (47/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-225432485467323/50000000000000),(-15301211639757/25000000000000),(54439903201/12500000000000),(-1514845019/50000000000000),(50305317/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((47/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((47/40)+(1/40)*x)) := (SharedCertificates.h154 (47/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(303912276508103/50000000000000),(80885704218941/100000000000000),(-24809885773/3125000000000),(297413843/4000000000000),(73804007/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((47/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((47/40)+(1/40)*x)) := (SharedCertificates.h157 (47/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(843528094724311/50000000000000),(11425468129017/5000000000000),(-1696036128729/100000000000000),(12171171559/100000000000000),(90636713/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((47/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((47/40)+(1/40)*x)) := (SharedCertificates.h160 (47/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(1731246882876893/100000000000000),(240469705659367/100000000000000),(-976935806243/100000000000000),(633729813/100000000000000),(327442169/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((47/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((47/40)+(1/40)*x)) := (SharedCertificates.h41 (47/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(51610232317407/50000000000000),(218588887569/50000000000000),(-3110793579/100000000000000),(5411273/25000000000000),(179689/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((47/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((47/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((47/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((47/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((47/40)+(1/40)*x)) := (SharedCertificates.h167 (47/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(54182446509617261/100000000000000),(11362407541751/5000000000000),(-887311507671/50000000000000),(13180541663/100000000000000),(117036261/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((47/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(46140404523/25000000000000),(-774075169/100000000000000),(9291467/100000000000000),(-5461/5000000000000),(1767/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((47/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(798804315051/25000000000000),(430413627551/100000000000000),(-175180329/5000000000000),(14592067/50000000000000),(250301/25000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((47/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((47/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(39314290421561/100000000000000),(2707724236671/50000000000000),(-13348004087/50000000000000),(67126181/25000000000000),(2314417/25000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((47/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(33458970571541/100000000000000),(3896999326853/100000000000000),(-26408721563/25000000000000),(2476065429/100000000000000),(7588937/10000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((47/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((47/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(414582272460937/100000000000000),(10012227783203/25000000000000),(156839/10240000),(2961/10240000),(269531251/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((47/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(27889/1600),(167/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((47/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(4657463/64000),(83667/64000),(501/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((47/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(30170337413167703/100000000000000),(3456455887208581/100000000000000),(167062375366393/100000000000000),(2213291552673/50000000000000),(70637151977/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((47/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(82862845243/25000000000000),(-37972630581/100000000000000),(2514975767/100000000000000),(-63245929/50000000000000),(418173/5000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((47/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2631232058317/100000000000000),(277062090091/100000000000000),(-1422099699/12500000000000),(521297/160000000000),(166923817/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((47/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((47/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((47/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel3
