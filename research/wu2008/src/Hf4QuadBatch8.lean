import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel25
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(91/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((91/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (91/40) (1/40)

def c3 : Certificate := ⟨(199333333333333/50000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((91/40)+(1/40)*x)) := (SharedCertificates.h2 (91/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((91/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-61447619047619/20000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((91/40)+(1/40)*x)) := (SharedCertificates.h4 (91/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(8281/1600),(91/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((91/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(626551851851851/100000000000000),(1377037037037/10000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((91/40)+(1/40)*x)) := (SharedCertificates.h8 (91/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((91/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((91/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(753571/64000),(24843/64000),(273/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((91/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(458858452662037/4000000000000),(378180043402777/100000000000000),(4155824652777/100000000000000),(608912037/4000000000000),(1/25000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((91/40)+(1/40)*x)) := (SharedCertificates.h13 (91/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((91/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((91/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(68574961/2560000),(753571/640000),(24843/1280000),(91/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((91/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(1496675736111111/20000000000000),(164469861111111/50000000000000),(5422083333333/100000000000000),(19861111111/50000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((91/40)+(1/40)*x)) := (SharedCertificates.h18 (91/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((91/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(6094063916992187/100000000000000),(83709669189453/25000000000000),(753571/10240000),(8281/10240000),(445312501/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((91/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(39701697888849099/100000000000000),(1090705985957391/50000000000000),(47943120261863/100000000000000),(105369495081/20000000000000),(2901128481/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((91/40)+(1/40)*x)) := (SharedCertificates.h22 (91/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((91/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(554559816446289/4000000000000),(457054793774413/50000000000000),(5022580151367/20000000000000),(367954589843/100000000000000),(3045947271/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((91/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(15565819186495043/50000000000000),(102631774856011/5000000000000),(28195542542859/50000000000000),(826243004917/100000000000000),(6839682657/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((91/40)+(1/40)*x)) := (SharedCertificates.h26 (91/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((91/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(15770294780191343/50000000000000),(2426199196952509/100000000000000),(1999614722763/2500000000000),(1464919210813/100000000000000),(1012783967/6250000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((91/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1496926393421337/20000000000000),(287870460273333/50000000000000),(18980469908131/100000000000000),(173813826997/50000000000000),(384536389/10000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((91/40)+(1/40)*x)) := (SharedCertificates.h30 (91/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((91/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((91/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((91/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((91/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((91/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (91/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((91/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((91/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (91/40) (1/40))

def c43 : Certificate := ⟨(17161/1600),(131/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((91/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((91/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(8879491427/20000000000000),(-338911887/50000000000000),(388067/5000000000000),(-19749/25000000000000),(773/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((91/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-520175383822363/50000000000000),(146816651423/100000000000000),(-569412849/50000000000000),(1104487/12500000000000),(3608897/10000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((91/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((91/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (91/40) (1/40))

def c52 : Certificate := ⟨(71249999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((91/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (91/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((91/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (91/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((91/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (91/40) (1/40))

def c56 : Certificate := ⟨(22598870056497/100000000000000),(-1063976933/2500000000000),(80148921/100000000000000),(-7547/5000000000000),(9/3125000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((91/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(960451977401/10000000000000),(42559077319/25000000000000),(-320595687/100000000000000),(301879/50000000000000),(1387/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((91/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((91/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((91/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((91/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((91/40)+(1/40)*x)) := (SharedCertificates.h61 (91/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-139998084841501/100000000000000),(-644878222427/25000000000000),(389876959/12500000000000),(-1299613/50000000000000),(39571/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((91/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((91/40)+(1/40)*x)) := (SharedCertificates.h61 (91/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-73954710288989/50000000000000),(-2869385728121/100000000000000),(105683297/12500000000000),(4031999/100000000000000),(13823/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((91/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((91/40)+(1/40)*x)) := (SharedCertificates.h67 (91/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-85815296715967/12500000000000),(-6221963953817/50000000000000),(3622471187/20000000000000),(-8032601/25000000000000),(14721/12500000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((91/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((91/40)+(1/40)*x)) := (SharedCertificates.h67 (91/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-46140847582399/6250000000000),(-14280431517261/100000000000000),(2599090209/50000000000000),(21234537/100000000000000),(306409/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((91/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((91/40)+(1/40)*x)) := (SharedCertificates.h72 (91/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(234392216747973/25000000000000),(15246469989203/100000000000000),(-13776739339/25000000000000),(57804219/50000000000000),(363/156250000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((91/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((91/40)+(1/40)*x)) := (SharedCertificates.h72 (91/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(439409425398499/20000000000000),(20935245335019/50000000000000),(-16006083297/50000000000000),(-125065407/100000000000000),(161949/12500000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((91/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((91/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((91/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(120131507548913/100000000000000),(14926935141/4000000000000),(-412970717/100000000000000),(231951/100000000000000),(767/12500000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((91/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(570115629045697/5000000000000),(2789312880151/20000000000000),(-65461936859/100000000000000),(145296217/100000000000000),(294097/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((91/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(438507536477/50000000000000),(-536353793/50000000000000),(3173553/50000000000000),(-12549/50000000000000),(87/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((91/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(9634217231813/50000000000000),(42955327887/12500000000000),(-295225273/50000000000000),(1321/97656250000),(13237/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((91/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((91/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((91/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (91/40) (1/40))

def c87 : Certificate := ⟨(4739336492891/25000000000000),(-22461310393/25000000000000),(26612927/6250000000000),(-1009021/50000000000000),(2403/25000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((91/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(4028436018957/50000000000000),(29948413857/25000000000000),(-567742443/100000000000000),(1345361/50000000000000),(4197/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((91/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((91/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((91/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((91/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((91/40)+(1/40)*x)) := (SharedCertificates.h61 (91/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-29172749938229/25000000000000),(-1792930634321/100000000000000),(3818135197/50000000000000),(-8027533/25000000000000),(372589/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((91/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((91/40)+(1/40)*x)) := (SharedCertificates.h61 (91/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-122197853060651/100000000000000),(-61292303659/3125000000000),(3539162961/50000000000000),(-188047/781250000000),(239789/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((91/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((91/40)+(1/40)*x)) := (SharedCertificates.h67 (91/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-114765273461631/20000000000000),(-8689964914193/100000000000000),(19328227217/50000000000000),(-173963013/100000000000000),(1656349/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((91/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((91/40)+(1/40)*x)) := (SharedCertificates.h67 (91/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-610213498787809/100000000000000),(-1954620562889/20000000000000),(4463037661/12500000000000),(-122161991/100000000000000),(1195183/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((91/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((91/40)+(1/40)*x)) := (SharedCertificates.h72 (91/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(398403721612779/50000000000000),(11059930375933/100000000000000),(-64979422733/100000000000000),(177260883/50000000000000),(2886573/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((91/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((91/40)+(1/40)*x)) := (SharedCertificates.h72 (91/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(910169320070227/50000000000000),(28847886041547/100000000000000),(-11224596923/10000000000000),(383791807/100000000000000),(1851993/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((91/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((91/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((91/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(116762875946181/100000000000000),(25889055391/10000000000000),(-270866063/25000000000000),(4454781/100000000000000),(11021/20000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((91/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11272321246557937/100000000000000),(2061308675673/20000000000000),(-33778131309/50000000000000),(390794627/100000000000000),(4924357/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((91/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(177425745439/20000000000000),(-811122263/100000000000000),(6058287/100000000000000),(-10289/25000000000000),(441/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((91/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4037186752229/25000000000000),(24115271229/10000000000000),(-559738263/50000000000000),(664211/12500000000000),(103949/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((91/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((91/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-368462919327717/100000000000000),(-6031924440973/100000000000000),(570139887/3125000000000),(-75394693/100000000000000),(577263/4000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((91/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(43956043956043/100000000000000),(-483033450067/100000000000000),(530805989/10000000000000),(-58330329/100000000000000),(324059/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((91/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-161961722781411/100000000000000),(-108949525903/12500000000000),(17597530361/100000000000000),(-226519977/100000000000000),(13707061/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((91/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((91/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((91/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((91/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((91/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((91/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((91/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((91/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((91/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((91/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (91/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((91/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((91/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(197520689/5000000000000),(-86822281/50000000000000),(2385227/50000000000000),(-52423/50000000000000),(229/10000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((91/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(29327060339589/25000000000000),(-239824805537/50000000000000),(4412144003/100000000000000),(-7704311/20000000000000),(66816647/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((91/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((91/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (91/40) (1/40))

def c134 : Certificate := ⟨(36081/1600),(191/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((91/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((91/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(5089058524173/100000000000000),(-19423887497/50000000000000),(2965479/1000000000000),(-90549/4000000000000),(3483/20000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((91/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(57380725190839/50000000000000),(2648211849/781250000000),(118619157/20000000000000),(-2263731/50000000000000),(376713/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((91/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((91/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (91/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((91/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (91/40) (1/40))

def c140 : Certificate := ⟨(24110244553339/100000000000000),(-3940904591/20000000000000),(-918651/5000000000000),(2451/800000000000),(5539/12500000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((91/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1779510893321/50000000000000),(15763618363/20000000000000),(36746039/50000000000000),(-1225503/100000000000000),(2379/1250000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((91/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((91/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(126666360777/100000000000000),(5610306119/100000000000000),(33677057/50000000000000),(14309/50000000000000),(15729/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((91/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((91/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(1510980162571/100000000000000),(2085145543/3125000000000),(39721251/5000000000000),(115031/50000000000000),(23521/12500000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((91/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-498209274016703/100000000000000),(-2757741795819/25000000000000),(-10206915609/100000000000000),(86117639/50000000000000),(6662241/25000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((91/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-507128738432543/50000000000000),(-5713584819139/25000000000000),(-15000795191/50000000000000),(339224517/100000000000000),(11098393/20000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((91/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(83382858955181/6250000000000),(28732156045373/100000000000000),(8467933881/100000000000000),(-97551727/20000000000000),(36965597/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((91/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3784454701838737/100000000000000),(16966622510489/20000000000000),(808757371/800000000000),(-258539443/20000000000000),(41170033/20000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((91/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(125198500333193/3125000000000),(9476312428499/10000000000000),(223652874543/100000000000000),(-1187497097/100000000000000),(58378649/25000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((91/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(107244709934061/100000000000000),(163246489749/100000000000000),(21433827/10000000000000),(-605597/25000000000000),(396369/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((91/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((91/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((91/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((91/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(56260682179454237/100000000000000),(16748798724227/20000000000000),(86803480109/100000000000000),(-1318878079/100000000000000),(106641113/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((91/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(7109760929/4000000000000),(-264571879/100000000000000),(119577/100000000000000),(1099/25000000000000),(173/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((91/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(3560525624153/50000000000000),(157836108843/100000000000000),(75801857/50000000000000),(-1206497/50000000000000),(112911/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((91/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((91/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((91/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (91/40) (1/40))

def c175 : Certificate := ⟨(2813513455467/12500000000000),(-103036693/200000000000),(27777937/100000000000000),(415423/50000000000000),(29659/25000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((91/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(830630785421/25000000000000),(13738225733/20000000000000),(-37037251/100000000000000),(-276949/25000000000000),(96603/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((91/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((91/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(11039160027/10000000000000),(1141139323/25000000000000),(44723569/100000000000000),(-124497/100000000000000),(2923/20000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((91/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((91/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1317363630309/100000000000000),(27159856043/50000000000000),(263760903/50000000000000),(-1541307/100000000000000),(87591/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((91/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-465109470124283/100000000000000),(-192280966323/2000000000000),(2619783541/50000000000000),(77683939/50000000000000),(5410841/20000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((91/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-236439962362641/25000000000000),(-19872433950913/100000000000000),(4112781571/100000000000000),(163828687/50000000000000),(56143769/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((91/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1247748319685589/100000000000000),(12568082602071/50000000000000),(-27423009241/100000000000000),(-394952559/100000000000000),(18735823/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((91/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1765053012719863/50000000000000),(3690896620389/5000000000000),(-11498032737/50000000000000),(-76142351/6250000000000),(41681443/20000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((91/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(465403309751329/12500000000000),(81880660216063/100000000000000),(58380620653/100000000000000),(-704313219/50000000000000),(234221227/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((91/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(53377718941819/50000000000000),(70973407311/50000000000000),(-29350933/100000000000000),(-2340089/100000000000000),(401027/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((91/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((91/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((91/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((91/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(28004741221244813/50000000000000),(72937750373863/100000000000000),(-16239810243/50000000000000),(-241088507/20000000000000),(107710291/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((91/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(17854119631/10000000000000),(-232503367/100000000000000),(40631/10000000000000),(1589/50000000000000),(7/1000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((91/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(664749309517/10000000000000),(137534083373/100000000000000),(-8876749/12500000000000),(-1099851/50000000000000),(112871/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((91/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((91/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(16151637229977/100000000000000),(280452808591/100000000000000),(-71471559/10000000000000),(1930679/100000000000000),(19946343/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((91/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7099620760429/100000000000000),(9051629853/20000000000000),(-811502999/100000000000000),(1953253/20000000000000),(9182921/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((91/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((91/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((91/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((91/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((91/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((91/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (91/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((91/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((91/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((91/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (91/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((91/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(36554291919/100000000000000),(-91547517/100000000000000),(1807679/100000000000000),(-8481/100000000000000),(103/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((91/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(437709087689463/100000000000000),(-748011281221/50000000000000),(-5911195819/100000000000000),(-49803341/100000000000000),(640167/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((91/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((91/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((91/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((91/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (91/40) (1/40))

def c223 : Certificate := ⟨(29241/1600),(171/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((91/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3140512641/2560000),(15776631/640000),(222563/1280000),(311/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((91/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((91/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(103594066649/100000000000000),(-395397201/25000000000000),(3621959/20000000000000),(-46081/25000000000000),(9/500000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((91/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(31771335531619/25000000000000),(61346164899/10000000000000),(620679847/50000000000000),(-2179867/50000000000000),(448073/10000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((91/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((91/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (91/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((91/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (91/40) (1/40))

def c231 : Certificate := ⟨(23414524015761/100000000000000),(-672648349/2000000000000),(-9873493/50000000000000),(365137/100000000000000),(123587/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((91/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(3170951968477/50000000000000),(67264834899/50000000000000),(39493971/50000000000000),(-182569/12500000000000),(561293/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((91/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((91/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(80439491091/20000000000000),(341269697/2000000000000),(191000999/100000000000000),(2727/10000000000000),(149281/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((91/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((91/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(596919439117/12500000000000),(201515368747/100000000000000),(2221239513/100000000000000),(-205333/100000000000000),(445597/25000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((91/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-443781851357141/50000000000000),(-18814949590613/100000000000000),(-10642573089/100000000000000),(20754191/10000000000000),(19653457/12500000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((91/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-458005384938133/25000000000000),(-10013892522693/25000000000000),(-24402161691/50000000000000),(202950519/50000000000000),(8380697/2500000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((91/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1162723984785939/50000000000000),(731078508869/1562500000000),(-28018467927/100000000000000),(-121421681/20000000000000),(434884471/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((91/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(1361295362027159/20000000000000),(29470377150761/20000000000000),(5837695141/4000000000000),(-803390837/50000000000000),(77189607/6250000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((91/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(3761159787690713/50000000000000),(178259444930599/100000000000000),(2543324963/500000000000),(-1310752923/100000000000000),(1503222113/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((91/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(113086005329363/100000000000000),(143061412223/50000000000000),(348976883/100000000000000),(-1446917/50000000000000),(2394453/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((91/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((91/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((91/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((91/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(59226881651603797/100000000000000),(143773617320683/100000000000000),(49676545403/50000000000000),(-171621493/10000000000000),(65378841/5000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((91/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(1688422507/1000000000000),(-102466399/25000000000000),(355859/50000000000000),(963/25000000000000),(377/10000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((91/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(158760670949/1250000000000),(54029171789/20000000000000),(45438747/25000000000000),(-684871/25000000000000),(2850449/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((91/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((91/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((91/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (91/40) (1/40))

def c259 : Certificate := ⟨(5194740144467/25000000000000),(-79461417967/100000000000000),(143077907/100000000000000),(316229/50000000000000),(295281/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((91/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(5628052562841/100000000000000),(105948557289/100000000000000),(-190770543/100000000000000),(-421639/50000000000000),(44293/4000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((91/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((91/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(316749756501/100000000000000),(11925680987/100000000000000),(18155527/20000000000000),(-249579/50000000000000),(6421/5000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((91/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((91/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(1882671696217/50000000000000),(7054731053/5000000000000),(21101039/2000000000000),(-3037611/50000000000000),(1535747/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((91/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-787715443292443/100000000000000),(-14820867814023/100000000000000),(26909559447/100000000000000),(14816737/12500000000000),(155083087/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((91/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-324037551357919/20000000000000),(-15667147709737/50000000000000),(40730469591/100000000000000),(306215761/100000000000000),(82007609/25000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((91/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(259451902265619/12500000000000),(37310118386169/100000000000000),(-10126171977/10000000000000),(-190835409/100000000000000),(214024303/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((91/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(6026271906461449/100000000000000),(28886225651489/25000000000000),(-85219131617/50000000000000),(-1092147471/100000000000000),(30273983/2500000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((91/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(6587778691933791/100000000000000),(137021337144559/100000000000000),(146864447/6250000000000),(-1912016657/100000000000000),(720606017/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((91/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(111572854882183/100000000000000),(44764559113/20000000000000),(-290763451/100000000000000),(-1092857/50000000000000),(234307/10000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((91/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((91/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((91/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((91/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(14616106422026377/25000000000000),(2827307792193/2500000000000),(-96336505233/50000000000000),(-204593389/20000000000000),(636802209/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((91/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(171044184259/100000000000000),(-66172829/20000000000000),(601851/50000000000000),(-213/50000000000000),(3743/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((91/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(5634006162203/50000000000000),(13285651921/6250000000000),(-370038003/100000000000000),(-207113/12500000000000),(2727401/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((91/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((91/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(6557119043721/6250000000000),(438578356091/25000000000000),(-9462523079/100000000000000),(-11379647/20000000000000),(25288531/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((91/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(46116002065729/100000000000000),(26435752647/10000000000000),(-7064378569/100000000000000),(52620319/100000000000000),(2636803/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((91/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((91/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((91/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((91/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((91/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((91/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (91/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((91/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(211903070356261051/20000000000000),(2653477715070413/100000000000000),(-45749615777077/100000000000000),0,(137133/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((91/40)+(1/40)*x)) := (SharedCertificates.h297 (91/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9438277589/100000000000000),(-5909367/25000000000000),(23337/5000000000000),(-219/10000000000000),(29/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((91/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(641196761663081/100000000000000),(116371472467/10000000000000),(4275093709/50000000000000),(5761311/20000000000000),(3427301/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((91/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((91/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (91/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((91/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (91/40) (1/40))

def c307 : Certificate := ⟨(3131305376641327/100000000000000),(11091229182759/50000000000000),0,0,(1067/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((91/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (91/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((91/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (91/40) (1/40))

def c311 : Certificate := ⟨(1071847311679207/50000000000000),(2817541634481/100000000000000),0,0,(1067/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((91/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (91/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2332421766383/50000000000000),(-6131186191/100000000000000),(8058457/100000000000000),(-331/3125000000000),(19/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((91/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(73035248176703/50000000000000),(842790811621/100000000000000),(-1107712927/100000000000000),(181987/12500000000000),(3001/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((91/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((91/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (91/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((91/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (91/40) (1/40))

def c316 : Certificate := ⟨(22417981197477/100000000000000),(-2647236917/6250000000000),(135695499/100000000000000),(-54341/12500000000000),(727/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((91/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(1032807521009/10000000000000),(84711581343/50000000000000),(-271390999/50000000000000),(173891/10000000000000),(7149/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((91/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((91/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(266672843863/25000000000000),(34996303331/100000000000000),(87462107/50000000000000),(-296001/20000000000000),(259/2500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((91/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((91/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(12579959130391/100000000000000),(81822461277/20000000000000),(61123559/3125000000000),(-17704263/100000000000000),(25619/20000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((91/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-288926252354443/20000000000000),(-295695949809/1250000000000),(76816341363/100000000000000),(-48792781/20000000000000),(261767/25000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((91/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-3041063662049507/100000000000000),(-52329201532083/100000000000000),(127675612967/100000000000000),(-69667247/25000000000000),(346091/10000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((91/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(3662225613681459/100000000000000),(54671052107497/100000000000000),(-267936078037/100000000000000),(544081697/50000000000000),(2490433/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((91/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(11222716386338701/100000000000000),(37949089331901/20000000000000),(-262423106679/50000000000000),(625617117/50000000000000),(12554261/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((91/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(13162660148586811/100000000000000),(255116187779759/100000000000000),(-157218416103/100000000000000),(-1363612161/100000000000000),(7085593/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((91/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(7607677612227/6250000000000),(373842628703/100000000000000),(-455319891/50000000000000),(399563/20000000000000),(12329/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((91/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((91/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((91/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((91/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(15873873430064809/25000000000000),(181592713834019/100000000000000),(-72913564969/12500000000000),(300801959/20000000000000),(9439809/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((91/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(157491491349/100000000000000),(-450414757/100000000000000),(341871/12500000000000),(-15691/100000000000000),(33/25000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((91/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(20730069769209/100000000000000),(85624931271/25000000000000),(-1036692043/100000000000000),(1736277/50000000000000),(100681/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((91/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((91/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((91/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (91/40) (1/40))

def c344 : Certificate := ⟨(4645014182743/25000000000000),(-21821023999/25000000000000),(262379023/50000000000000),(-3154881/100000000000000),(9599/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((91/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(8559924358703/100000000000000),(116378794659/100000000000000),(-139935479/20000000000000),(2103253/50000000000000),(10821/25000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((91/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((91/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(732723050267/100000000000000),(1245242099/6250000000000),(7828263/50000000000000),(-181681/20000000000000),(1113/5000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((91/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((91/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((91/40)+(1/40)*x)) := (SharedCertificates.h144 (91/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(216680888137/2500000000000),(233970077483/100000000000000),(29815401/20000000000000),(-10564623/100000000000000),(264687/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((91/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((91/40)+(1/40)*x)) := (SharedCertificates.h148 (91/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1197647501413449/100000000000000),(-16262916766371/100000000000000),(98179245047/100000000000000),(-295457059/50000000000000),(1216531/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((91/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((91/40)+(1/40)*x)) := (SharedCertificates.h151 (91/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-39051508447527/1562500000000),(-35371963604649/100000000000000),(96883411021/50000000000000),(-525367411/50000000000000),(15239813/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((91/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((91/40)+(1/40)*x)) := (SharedCertificates.h154 (91/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1540816492361021/50000000000000),(1214667857063/3125000000000),(-138233977819/50000000000000),(189742277/10000000000000),(21002347/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((91/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((91/40)+(1/40)*x)) := (SharedCertificates.h157 (91/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(4625853014571599/50000000000000),(129111290508153/100000000000000),(-734652496063/100000000000000),(82303361/2000000000000),(27211993/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((91/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((91/40)+(1/40)*x)) := (SharedCertificates.h160 (91/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(2114359730521319/20000000000000),(82917719964129/50000000000000),(-689380524827/100000000000000),(476600903/20000000000000),(93855021/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((91/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((91/40)+(1/40)*x)) := (SharedCertificates.h41 (91/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(117852571767673/100000000000000),(126340731451/50000000000000),(-172962283/12500000000000),(7504607/100000000000000),(27207/25000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((91/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((91/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((91/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((91/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((91/40)+(1/40)*x)) := (SharedCertificates.h167 (91/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(481254588250359/781250000000),(6233905420571/5000000000000),(-744918505061/100000000000000),(4334209159/100000000000000),(32748259/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((91/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(8116805731/5000000000000),(-82141099/25000000000000),(2628091/100000000000000),(-4143/20000000000000),(137/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((91/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(17161847178091/100000000000000),(234475643453/100000000000000),(-693076641/50000000000000),(4150947/50000000000000),(121301/50000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((91/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((91/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(242961744398151/100000000000000),(1035125298907/25000000000000),(-348814283/6250000000000),(53775101/50000000000000),(3620057/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((91/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(5339818558201/5000000000000),(646414029241/100000000000000),(-4778325113/50000000000000),(152292947/100000000000000),(6450409/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((91/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((91/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(8772773331054687/100000000000000),(113146036376953/25000000000000),(190463/2048000),(9737/10240000),(484375001/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((91/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(44521/1600),(211/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((91/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(9393931/64000),(133563/64000),(633/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((91/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(10059915448067369/781250000000),(84738471234531297/100000000000000),(1198162198101409/50000000000000),(37978703113647/100000000000000),(185347264503/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((91/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(7765969843/100000000000000),(-255530079/50000000000000),(9589681/50000000000000),(-16879/3125000000000),(19063/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((91/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1424979663449/25000000000000),(-6805101271/100000000000000),(-30659719/6250000000000),(1351451/12500000000000),(2695939/10000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((91/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((91/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((91/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel25

namespace Hf4Quad.Panel26
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(93/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((93/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (93/40) (1/40)

def c3 : Certificate := ⟨(407428571428571/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((93/40)+(1/40)*x)) := (SharedCertificates.h2 (93/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((93/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-79/25),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((93/40)+(1/40)*x)) := (SharedCertificates.h4 (93/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(8649/1600),(93/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((93/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(327197619047619/50000000000000),(2814603174603/20000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((93/40)+(1/40)*x)) := (SharedCertificates.h8 (93/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((93/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((93/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(804357/64000),(25947/64000),(279/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((93/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(156730451/1280000),(5055821/1280000),(4247161458333/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((93/40)+(1/40)*x)) := (SharedCertificates.h13 (93/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((93/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((93/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(74805201/2560000),(804357/640000),(25947/1280000),(93/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((93/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(8163265982142857/100000000000000),(175554107142857/50000000000000),(1132607142857/20000000000000),(8119047619/20000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((93/40)+(1/40)*x)) := (SharedCertificates.h18 (93/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((93/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(106153620803833/1562500000000),(91314942626953/25000000000000),(804357/10240000),(8649/10240000),(227539063/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((93/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(22130277806689451/50000000000000),(297449970520019/12500000000000),(25587094238281/50000000000000),(110052018229/20000000000000),(2964749721/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((93/40)+(1/40)*x)) := (SharedCertificates.h22 (93/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((93/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(315913175512207/2000000000000),(203814951943359/20000000000000),(5478896557617/20000000000000),(196376220703/50000000000000),(397625733/12500000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((93/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(35469193568090119/100000000000000),(457667013781807/20000000000000),(61514383572821/100000000000000),(220481661551/25000000000000),(3571478543/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((93/40)+(1/40)*x)) := (SharedCertificates.h26 (93/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((93/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(36724906653294063/100000000000000),(2764240285731807/100000000000000),(89169041475217/100000000000000),(1598011495971/100000000000000),(17294174817/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((93/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1742975728465861/20000000000000),(655958607487151/100000000000000),(2115995508023/10000000000000),(9480266613/2500000000000),(128247973/3125000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((93/40)+(1/40)*x)) := (SharedCertificates.h30 (93/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((93/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((93/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((93/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((93/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((93/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (93/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((93/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((93/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (93/40) (1/40))

def c43 : Certificate := ⟨(17689/1600),(133/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((93/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((93/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(43072234829/100000000000000),(-32385139/5000000000000),(3652459/50000000000000),(-73233/100000000000000),(353/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((93/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-20801232403921/2000000000000),(35591271449/25000000000000),(-43497801/4000000000000),(8322459/100000000000000),(33957407/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((93/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((93/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (93/40) (1/40))

def c52 : Certificate := ⟨(28833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((93/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (93/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((93/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (93/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((93/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (93/40) (1/40))

def c56 : Certificate := ⟨(22514071294559/100000000000000),(-8448056771/20000000000000),(79250063/100000000000000),(-148687/100000000000000),(281/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((93/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(9943714821763/100000000000000),(84480567709/50000000000000),(-63400051/20000000000000),(594747/100000000000000),(1369/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((93/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((93/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((93/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((93/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((93/40)+(1/40)*x)) := (SharedCertificates.h61 (93/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-5805786214883/4000000000000),(-2567068057439/100000000000000),(3103390869/100000000000000),(-2608851/100000000000000),(38939/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((93/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((93/40)+(1/40)*x)) := (SharedCertificates.h61 (93/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-19205597264239/12500000000000),(-17912224253/625000000000),(434678749/50000000000000),(1966009/50000000000000),(13667/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((93/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((93/40)+(1/40)*x)) := (SharedCertificates.h67 (93/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-177834509024397/25000000000000),(-2474372384109/20000000000000),(8960583511/50000000000000),(-1975071/6250000000000),(116669/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((93/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((93/40)+(1/40)*x)) := (SharedCertificates.h67 (93/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-191698365812921/25000000000000),(-891211685577/6250000000000),(2661676303/50000000000000),(10246681/50000000000000),(301531/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((93/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((93/40)+(1/40)*x)) := (SharedCertificates.h72 (93/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(967842301027447/100000000000000),(3756855875379/25000000000000),(-27208886333/50000000000000),(22824489/20000000000000),(231029/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((93/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((93/40)+(1/40)*x)) := (SharedCertificates.h72 (93/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1140329534623673/50000000000000),(20870480697811/50000000000000),(-32747464183/100000000000000),(-60029199/50000000000000),(1271909/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((93/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((93/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((93/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(120876204288091/100000000000000),(371524297767/100000000000000),(-20578253/5000000000000),(236559/100000000000000),(1207/20000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((93/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2285989004172543/20000000000000),(2737290651651/20000000000000),(-64595370017/100000000000000),(71780447/50000000000000),(289333/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((93/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(437447423489/50000000000000),(-523808619/50000000000000),(6198833/100000000000000),(-6083/25000000000000),(21/12500000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((93/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(19953368673981/100000000000000),(341296942779/100000000000000),(-582417137/100000000000000),(265041/20000000000000),(1039/4000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((93/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((93/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((93/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (93/40) (1/40))

def c87 : Certificate := ⟨(4694835680751/25000000000000),(-88165928277/100000000000000),(82784909/20000000000000),(-485827/25000000000000),(917/10000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((93/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(8294209702659/100000000000000),(23510914207/20000000000000),(-110379879/20000000000000),(647769/25000000000000),(813/4000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((93/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((93/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((93/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((93/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((93/40)+(1/40)*x)) := (SharedCertificates.h61 (93/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-120246570712727/100000000000000),(-1762766666131/100000000000000),(7446755217/100000000000000),(-1553429/5000000000000),(90017/25000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((93/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((93/40)+(1/40)*x)) := (SharedCertificates.h61 (93/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-31523109643099/25000000000000),(-966663449367/50000000000000),(6935668327/100000000000000),(-11742469/50000000000000),(463303/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((93/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((93/40)+(1/40)*x)) := (SharedCertificates.h67 (93/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-295526525230261/50000000000000),(-8537401584941/100000000000000),(9407851447/25000000000000),(-167767147/100000000000000),(40101/2500000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((93/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((93/40)+(1/40)*x)) := (SharedCertificates.h67 (93/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-629617858645289/100000000000000),(-4815869920561/50000000000000),(34980097759/100000000000000),(-14906201/12500000000000),(461517/20000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((93/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((93/40)+(1/40)*x)) := (SharedCertificates.h72 (93/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(818670193257763/100000000000000),(10804208685347/100000000000000),(-31447903557/50000000000000),(340136507/100000000000000),(348327/12500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((93/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((93/40)+(1/40)*x)) := (SharedCertificates.h72 (93/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(375517696552463/20000000000000),(7100868958813/25000000000000),(-109967082563/100000000000000),(187921723/50000000000000),(1427031/20000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((93/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((93/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((93/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(58638179275617/50000000000000),(254609587343/100000000000000),(-211431881/20000000000000),(1078601/25000000000000),(53239/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((93/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11292667201342001/100000000000000),(10040941472659/100000000000000),(-13052215721/20000000000000),(374405501/100000000000000),(4742283/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((93/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(885530390801/100000000000000),(-787374557/100000000000000),(2908819/50000000000000),(-39083/100000000000000),(843/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((93/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(16626616629039/100000000000000),(118368878283/50000000000000),(-1088202377/100000000000000),(2556327/50000000000000),(49917/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((93/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((93/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-380454387810067/100000000000000),(-5959839931843/100000000000000),(17800604749/100000000000000),(-14515507/20000000000000),(14002793/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((93/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(10752688172043/25000000000000),(-462481211701/100000000000000),(2486458127/50000000000000),(-26736109/50000000000000),(290611/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((93/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-163636295832287/100000000000000),(-803841950983/100000000000000),(16299635927/100000000000000),(-103240523/50000000000000),(12755093/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((93/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((93/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((93/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((93/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((93/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((93/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((93/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((93/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((93/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((93/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (93/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((93/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((93/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(3621398877/100000000000000),(-38939773/25000000000000),(65423/1562500000000),(-18009/20000000000000),(1921/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((93/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(29091571973107/25000000000000),(-462452886817/100000000000000),(4188628879/100000000000000),(-9015463/25000000000000),(24267313/20000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((93/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((93/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (93/40) (1/40))

def c134 : Certificate := ⟨(36849/1600),(193/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((93/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((93/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(15664160401/312500000000),(-37688205477/100000000000000),(56673993/20000000000000),(-1065301/50000000000000),(3229/20000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((93/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(115441729323289/100000000000000),(341290255693/100000000000000),(566739909/100000000000000),(-4261221/100000000000000),(71397/10000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((93/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((93/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (93/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((93/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (93/40) (1/40))

def c140 : Certificate := ⟨(12035382213877/50000000000000),(-19774415439/100000000000000),(-16592093/100000000000000),(143751/50000000000000),(327/781250000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((93/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(185847114449/5000000000000),(15819532351/20000000000000),(66368369/100000000000000),(-115001/10000000000000),(180339/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((93/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((93/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(34539149949/25000000000000),(2940014439/50000000000000),(16874537/25000000000000),(19501/100000000000000),(15471/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((93/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((93/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(823804397693/50000000000000),(8738084337/12500000000000),(397737363/50000000000000),(30289/25000000000000),(23133/12500000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((93/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-65038834973641/12500000000000),(-11069771109253/100000000000000),(-920561787/10000000000000),(20207819/12500000000000),(25251833/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((93/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-530041744302781/50000000000000),(-5742588969157/25000000000000),(-5605312529/20000000000000),(319367073/100000000000000),(13165273/25000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((93/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(55664803590833/4000000000000),(28760303652029/100000000000000),(5637516389/100000000000000),(-456105501/100000000000000),(70058031/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((93/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3954515119047633/100000000000000),(5326392980197/6250000000000),(93568653939/100000000000000),(-1216920561/100000000000000),(3051017/1562500000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((93/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2098381746498489/50000000000000),(95643729329641/100000000000000),(10835467063/5000000000000),(-112778709/10000000000000),(111258261/50000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((93/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(26893010294439/25000000000000),(41018838097/25000000000000),(100117443/50000000000000),(-2280519/100000000000000),(376149/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((93/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((93/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((93/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((93/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(28214253493939431/50000000000000),(84075696379331/100000000000000),(79125277967/100000000000000),(-620741147/50000000000000),(202582847/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((93/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(177215392251/100000000000000),(-264042207/100000000000000),(72457/50000000000000),(4053/100000000000000),(163/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((93/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(7437310885961/100000000000000),(31682836629/20000000000000),(137584193/100000000000000),(-2262121/100000000000000),(430087/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((93/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((93/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((93/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (93/40) (1/40))

def c175 : Certificate := ⟨(22405188569987/100000000000000),(-5139754203/10000000000000),(32556301/100000000000000),(381419/50000000000000),(891/800000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((93/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(3459748573349/100000000000000),(68530056039/100000000000000),(-21704201/50000000000000),(-1017119/100000000000000),(182897/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((93/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((93/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(119698601907/100000000000000),(592741909/12500000000000),(21980021/50000000000000),(-32469/25000000000000),(7143/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((93/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((93/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(71405034077/5000000000000),(1128220923/2000000000000),(259041653/50000000000000),(-801613/50000000000000),(34247/20000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((93/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-96863078315181/20000000000000),(-9591277486899/100000000000000),(1226627853/20000000000000),(71328611/50000000000000),(25611019/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((93/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-985485695388277/100000000000000),(-1240759461637/6250000000000),(6003869493/100000000000000),(303021429/100000000000000),(10642187/20000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((93/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(129790787345261/10000000000000),(12510941575673/50000000000000),(-29681422859/100000000000000),(-358351517/100000000000000),(17733467/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((93/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(3677640351151611/100000000000000),(14742342015863/20000000000000),(-15010807613/50000000000000),(-44991063/4000000000000),(9872597/5000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((93/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(19436051105901/500000000000),(10262202062973/12500000000000),(12545093931/25000000000000),(-1325757601/100000000000000),(22271431/10000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((93/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(21407839149721/20000000000000),(2836040947/2000000000000),(-21428381/50000000000000),(-1082057/50000000000000),(4751/1250000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((93/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((93/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((93/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((93/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(28077609287732249/50000000000000),(7279375355819/10000000000000),(-19711955723/50000000000000),(-1110548889/100000000000000),(102162111/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((93/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(178077839489/100000000000000),(-230841491/100000000000000),(212129/50000000000000),(2809/100000000000000),(661/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((93/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(6922259978273/100000000000000),(137224367709/100000000000000),(-83663433/100000000000000),(-2019221/100000000000000),(428943/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((93/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((93/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(16709699571991/100000000000000),(277617357211/100000000000000),(-140594859/20000000000000),(1973477/100000000000000),(4717647/25000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((93/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1437393511569/20000000000000),(42126093877/100000000000000),(-755323287/100000000000000),(8970563/100000000000000),(265511/3125000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((93/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((93/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((93/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((93/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((93/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((93/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (93/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((93/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((93/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((93/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (93/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((93/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(9094590333/25000000000000),(-10551929/12500000000000),(1759133/100000000000000),(-771/10000000000000),(3/3125000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((93/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(434692997322609/100000000000000),(-60810766763/4000000000000),(-6213237751/100000000000000),(-50916729/100000000000000),(605119/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((93/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((93/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((93/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((93/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (93/40) (1/40))

def c223 : Certificate := ⟨(29929/1600),(173/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((93/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3268516161/2560000),(16225497/640000),(226307/1280000),(313/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((93/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((93/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(100501881269/100000000000000),(-755653243/50000000000000),(17044809/100000000000000),(-42719/25000000000000),(411/25000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((93/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(128317196538527/100000000000000),(123675173311/20000000000000),(608007177/50000000000000),(-2046699/50000000000000),(532557/12500000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((93/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((93/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (93/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((93/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (93/40) (1/40))

def c231 : Certificate := ⟨(233471830709/1000000000000),(-33707109311/100000000000000),(-8809881/50000000000000),(344261/100000000000000),(233681/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((93/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1652816929099/25000000000000),(134828437239/100000000000000),(14095809/20000000000000),(-172131/12500000000000),(213411/20000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((93/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((93/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(218544304089/50000000000000),(17827737887/100000000000000),(191106191/100000000000000),(797/10000000000000),(147639/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((93/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((93/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(2593634551023/50000000000000),(42079387241/20000000000000),(17754523/800000000000),(-433837/100000000000000),(881233/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((93/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-462617268023967/50000000000000),(-150840619159/800000000000),(-9433010581/100000000000000),(4895679/2500000000000),(37363867/25000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((93/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-478081173193391/25000000000000),(-20123000668689/50000000000000),(-1160796921/2500000000000),(192626881/50000000000000),(12777971/4000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((93/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(604727291441613/25000000000000),(23334909972627/50000000000000),(-15773073097/50000000000000),(-113865613/20000000000000),(82686597/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((93/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(7101751662981061/100000000000000),(36979175816681/25000000000000),(34136602511/25000000000000),(-381622619/25000000000000),(73502539/6250000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((93/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1576172546440473/20000000000000),(90139279584497/50000000000000),(25046797353/5000000000000),(-633311431/50000000000000),(1441805511/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((93/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(11365962404097/10000000000000),(57496922473/20000000000000),(332064281/100000000000000),(-1373063/50000000000000),(2281749/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((93/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((93/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((93/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((93/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(59514812741843227/100000000000000),(72075389125957/50000000000000),(89310838623/100000000000000),(-65299913/4000000000000),(1247953429/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((93/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(33605079271/20000000000000),(-406974173/100000000000000),(45849/6250000000000),(1721/50000000000000),(713/20000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((93/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(1655231355247/12500000000000),(270840687657/100000000000000),(165825183/100000000000000),(-102927/4000000000000),(2730921/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((93/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((93/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((93/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (93/40) (1/40))

def c259 : Certificate := ⟨(5155153738091/25000000000000),(-78881836331/100000000000000),(73317607/50000000000000),(554617/100000000000000),(552903/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((93/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(5839180063513/100000000000000),(105175781773/100000000000000),(-9775681/5000000000000),(-73949/10000000000000),(1050337/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((93/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((93/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(340960238141/100000000000000),(12282806561/100000000000000),(43893333/50000000000000),(-497627/100000000000000),(63027/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((93/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((93/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(4051704293191/100000000000000),(36310508289/25000000000000),(25467103/2500000000000),(-6044999/100000000000000),(150719/10000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((93/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-326899449033/40000000000),(-14711867092711/100000000000000),(2757622741/10000000000000),(1039331/1000000000000),(73552593/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((93/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-420672759105703/25000000000000),(-31167818934519/100000000000000),(42478550311/100000000000000),(276936729/100000000000000),(62348477/20000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((93/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(2149828964923183/100000000000000),(18451473730383/50000000000000),(-102283451727/100000000000000),(-75237503/50000000000000),(40600489/10000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((93/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(782083931376009/12500000000000),(28712624958317/25000000000000),(-88326030433/50000000000000),(-490438243/50000000000000),(1150190389/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((93/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1372363138140439/20000000000000),(137008232063/100000000000),(-8794832391/100000000000000),(-90211841/5000000000000),(43016483/3125000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((93/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(112019320365167/100000000000000),(222634370107/100000000000000),(-151620287/50000000000000),(-1976607/100000000000000),(278341/12500000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((93/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((93/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((93/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((93/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(58689831669146159/100000000000000),(28077451951639/25000000000000),(-49616500699/25000000000000),(-113729333/12500000000000),(1211804851/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((93/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(170387266679/100000000000000),(-16302791/5000000000000),(293/24414062500),(-379/50000000000000),(1767/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((93/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(5845830099969/50000000000000),(659597601/312500000000),(-189679009/50000000000000),(-1453253/100000000000000),(1301017/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((93/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((93/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(108384226485859/100000000000000),(214472611033/12500000000000),(-9803748943/100000000000000),(-56893989/100000000000000),(24049829/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((93/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(46616871606821/100000000000000),(236713590577/100000000000000),(-6761973639/100000000000000),(2411943/5000000000000),(48963/400000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((93/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((93/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((93/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((93/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((93/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((93/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (93/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((93/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1064639308748337777/100000000000000),(2470479251962109/100000000000000),(-45749615777077/100000000000000),0,(137771/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((93/40)+(1/40)*x)) := (SharedCertificates.h297 (93/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4696426253/50000000000000),(-21795971/100000000000000),(227103/50000000000000),(-1991/100000000000000),(27/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((93/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(64355862761461/10000000000000),(1198271315083/100000000000000),(4365202877/50000000000000),(31205311/100000000000000),(1606173/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((93/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((93/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (93/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((93/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (93/40) (1/40))

def c307 : Certificate := ⟨(793917573343091/25000000000000),(11091229182759/50000000000000),0,0,(107/10000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((93/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (93/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((93/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (93/40) (1/40))

def c311 : Certificate := ⟨(2149329706627377/100000000000000),(2817541634481/100000000000000),0,0,(1069/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((93/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (93/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(930522661941/20000000000000),(-1219815803/20000000000000),(7995241/100000000000000),(-10481/100000000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((93/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(14775165874179/10000000000000),(167675473977/20000000000000),(-109902317/10000000000000),(1440699/100000000000000),(369/12500000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((93/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((93/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (93/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((93/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (93/40) (1/40))

def c316 : Certificate := ⟨(558345223561/2500000000000),(-41818181207/100000000000000),(133120199/100000000000000),(-423763/100000000000000),(1409/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((93/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(10664764230237/100000000000000),(20909090603/12500000000000),(-665601/125000000000),(33901/2000000000000),(1743/25000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((93/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((93/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(227474392173/20000000000000),(35678483447/100000000000000),(83113/50000000000),(-283969/20000000000000),(5019/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((93/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((93/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(2681173490857/20000000000000),(208363361471/50000000000000),(1852008609/100000000000000),(-2118749/12500000000000),(123847/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((93/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1491637288076163/100000000000000),(-23351314193097/100000000000000),(3014820433/4000000000000),(-119004263/50000000000000),(509933/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((93/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-24571981128203/781250000000),(-12955456972583/25000000000000),(12601501391/10000000000000),(-10994619/4000000000000),(841523/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((93/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1885252307663267/50000000000000),(53612238828759/100000000000000),(-130751014491/50000000000000),(1056697583/100000000000000),(969197/20000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((93/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(11600117869263629/100000000000000),(18766100574451/10000000000000),(-25869598763/5000000000000),(154189037/12500000000000),(12191029/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((93/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2734450576824393/20000000000000),(254471235180113/100000000000000),(-41296888499/25000000000000),(-323317127/25000000000000),(13817433/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((93/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(122466900421339/100000000000000),(74044786619/20000000000000),(-2246839/250000000000),(394051/20000000000000),(11991/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((93/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((93/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((93/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((93/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(7982044737797769/12500000000000),(35855488146829/20000000000000),(-287174918289/50000000000000),(1482212391/100000000000000),(1830149/10000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((93/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(156601477573/100000000000000),(-87932081/20000000000000),(330361/12500000000000),(-1501/10000000000000),(1/800000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((93/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(5352737508513/25000000000000),(338394231887/100000000000000),(-1016153083/100000000000000),(3374171/100000000000000),(48847/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((93/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((93/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((93/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (93/40) (1/40))

def c344 : Certificate := ⟨(18407562631973/100000000000000),(-42611162219/50000000000000),(506275009/100000000000000),(-3007597/100000000000000),(9043/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((93/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(8789916490701/100000000000000),(28407441479/25000000000000),(-337516673/50000000000000),(250633/6250000000000),(41383/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((93/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((93/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(386313159567/50000000000000),(3995184613/20000000000000),(5223751/50000000000000),(-51819/6250000000000),(2637/12500000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((93/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((93/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((93/40)+(1/40)*x)) := (SharedCertificates.h144 (93/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(9135689413133/100000000000000),(234443475913/100000000000000),(88567151/100000000000000),(-1923903/20000000000000),(125293/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((93/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((93/40)+(1/40)*x)) := (SharedCertificates.h148 (93/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-307446322306969/25000000000000),(-3175435795999/20000000000000),(94717182041/100000000000000),(-70422381/12500000000000),(5814447/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((93/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((93/40)+(1/40)*x)) := (SharedCertificates.h151 (93/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-2569273717334337/100000000000000),(-865233184383/2500000000000),(187595157561/100000000000000),(-251717297/25000000000000),(3636091/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((93/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((93/40)+(1/40)*x)) := (SharedCertificates.h154 (93/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(3158280834748667/100000000000000),(37785869192627/100000000000000),(-13269071193/5000000000000),(1799153593/100000000000000),(399827/2000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((93/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((93/40)+(1/40)*x)) := (SharedCertificates.h157 (93/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(594188910197017/6250000000000),(31555336919653/25000000000000),(-355247636461/50000000000000),(1969405047/50000000000000),(25964437/50000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((93/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((93/40)+(1/40)*x)) := (SharedCertificates.h160 (93/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(5450365501671211/50000000000000),(163106371288757/100000000000000),(-675189996841/100000000000000),(2346817579/100000000000000),(17890151/20000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((93/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((93/40)+(1/40)*x)) := (SharedCertificates.h41 (93/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(14794057412567/12500000000000),(247235454897/100000000000000),(-133961919/10000000000000),(449447/6250000000000),(51931/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((93/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((93/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((93/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((93/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((93/40)+(1/40)*x)) := (SharedCertificates.h167 (93/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(15461749531015859/25000000000000),(121749670061719/100000000000000),(-719491764403/100000000000000),(4143109617/100000000000000),(62403681/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((93/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(6467573401/4000000000000),(-318295533/100000000000000),(2507583/100000000000000),(-19471/100000000000000),(1/390625000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((93/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(2203164934021/12500000000000),(28628633409/12500000000000),(-1337525633/100000000000000),(7911199/100000000000000),(229597/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((93/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((93/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(251221280306169/100000000000000),(1029865504201/25000000000000),(-617500887/12500000000000),(106144261/100000000000000),(3489611/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((93/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(21610432714509/20000000000000),(15249009973/2500000000000),(-2170862051/25000000000000),(27804771/20000000000000),(2974327/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((93/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((93/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(2428977473876953/25000000000000),(122735137939453/25000000000000),(1011933/10240000),(10137/10240000),(247070313/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((93/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(45369/1600),(213/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((93/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(9663597/64000),(136107/64000),(639/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((93/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(91690075896972271/6250000000000),(47395742119476707/50000000000000),(2633220413540221/100000000000000),(20508572729553/50000000000000),(19683923179/5000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((93/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(170411027/2500000000000),(-440437911/100000000000000),(16223519/100000000000000),(-448299/100000000000000),(15509/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((93/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2842215040177/50000000000000),(-4321418401/50000000000000),(-429583319/100000000000000),(1192581/12500000000000),(24873593/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((93/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((93/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((93/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel26

namespace Hf4Quad.Panel27
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(19/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((19/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (19/8) (1/40)

def c3 : Certificate := ⟨(104047619047619/25000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((19/8)+(1/40)*x)) := (SharedCertificates.h2 (19/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((19/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-64952380952381/20000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((19/8)+(1/40)*x)) := (SharedCertificates.h4 (19/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(361/64),(19/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((19/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(136568783068783/20000000000000),(14375661375661/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((19/8)+(1/40)*x)) := (SharedCertificates.h8 (19/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((19/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((19/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(6859/512),(1083/2560),(57/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((19/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(652582447193287/5000000000000),(103039333767361/25000000000000),(271156141493/6250000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((19/8)+(1/40)*x)) := (SharedCertificates.h13 (19/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((19/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((19/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(130321/4096),(6859/5120),(1083/51200),(19/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((19/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(277764408172123/3125000000000),(93562748015873/25000000000000),(1477306547619/25000000000000),(2591765873/6250000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((19/8)+(1/40)*x)) := (SharedCertificates.h18 (19/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((19/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(7556454467773437/100000000000000),(99427032470703/25000000000000),(6859/81920),(361/409600),(464843751/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((19/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(3076806344632749/6250000000000),(1295497408266419/50000000000000),(13636814823857/25000000000000),(574181676793/100000000000000),(3028370957/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((19/8)+(1/40)*x)) := (SharedCertificates.h22 (19/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((19/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(2243322420120239/12500000000000),(566734085083007/50000000000000),(2982810974121/10000000000000),(209320068359/50000000000000),(1659497073/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((19/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(805981828655263/2000000000000),(2545205774700827/100000000000000),(6697909933423/10000000000000),(940057534513/100000000000000),(3726405069/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((19/8)+(1/40)*x)) := (SharedCertificates.h26 (19/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((19/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(42623125982284541/100000000000000),(3140651388168331/100000000000000),(24794616222381/25000000000000),(347994613647/20000000000000),(18431589369/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((19/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(10114535451351649/100000000000000),(372640779786639/50000000000000),(11767603572209/50000000000000),(206449185477/50000000000000),(546730677/12500000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((19/8)+(1/40)*x)) := (SharedCertificates.h30 (19/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((19/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((19/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((19/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((19/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((19/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (19/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((19/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((19/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (19/8) (1/40))

def c43 : Certificate := ⟨(729/64),(27/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((19/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((19/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(2612842119/6250000000000),(-123868071/20000000000000),(6881559/100000000000000),(-67967/100000000000000),(323/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((19/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-51989058723329/5000000000000),(138112920527/100000000000000),(-1039102971/100000000000000),(1568131/20000000000000),(31988961/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((19/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((19/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (19/8) (1/40))

def c52 : Certificate := ⟨(145833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((19/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (19/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((19/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (19/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((19/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (19/8) (1/40))

def c56 : Certificate := ⟨(2803738317757/12500000000000),(-20962529479/50000000000000),(19591149/25000000000000),(-36619/25000000000000),(277/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((19/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(411214953271/4000000000000),(167700235827/100000000000000),(-62691677/20000000000000),(585903/100000000000000),(677/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((19/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((19/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((19/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((19/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((19/8)+(1/40)*x)) := (SharedCertificates.h61 (19/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-150266398812113/100000000000000),(-319335729437/12500000000000),(3087711569/100000000000000),(-2617393/100000000000000),(9591/25000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((19/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((19/8)+(1/40)*x)) := (SharedCertificates.h61 (19/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-79686590593141/50000000000000),(-357803957609/12500000000000),(446327069/50000000000000),(3833841/100000000000000),(54099/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((19/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((19/8)+(1/40)*x)) := (SharedCertificates.h67 (19/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-23000322719931/3125000000000),(-6150277192001/50000000000000),(8866559543/50000000000000),(-15541667/50000000000000),(57889/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((19/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((19/8)+(1/40)*x)) := (SharedCertificates.h67 (19/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-159058156256841/20000000000000),(-142378505361/1000000000000),(2722072629/50000000000000),(9887301/50000000000000),(59399/20000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((19/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((19/8)+(1/40)*x)) := (SharedCertificates.h72 (19/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(498840193485357/50000000000000),(1481111598539/10000000000000),(-13434363807/25000000000000),(56326333/50000000000000),(114991/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((19/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((19/8)+(1/40)*x)) := (SharedCertificates.h72 (19/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(2364009051526527/100000000000000),(1040213760777/2500000000000),(-6690631241/20000000000000),(-11519631/10000000000000),(1249443/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((19/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((19/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((19/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(3040440213119/2500000000000),(369880893973/100000000000000),(-410132467/100000000000000),(240931/100000000000000),(743/12500000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((19/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11457060690930751/100000000000000),(13429787598893/100000000000000),(-63739184891/100000000000000),(141835781/100000000000000),(1139733/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((19/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(872824214671/100000000000000),(-1023110913/100000000000000),(3027533/50000000000000),(-4719/20000000000000),(163/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((19/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(20633643438737/100000000000000),(67796613789/20000000000000),(-897729/156250000000),(649219/50000000000000),(6377/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((19/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((19/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((19/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (19/8) (1/40))

def c87 : Certificate := ⟨(1860465116279/10000000000000),(-86533261223/100000000000000),(100620071/25000000000000),(-936001/50000000000000),(547/6250000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((19/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(266472868217/3125000000000),(115377681629/100000000000000),(-536640381/100000000000000),(2496001/100000000000000),(19689/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((19/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((19/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((19/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((19/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((19/8)+(1/40)*x)) := (SharedCertificates.h61 (19/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-61871281773919/50000000000000),(-866674213167/50000000000000),(3631682579/50000000000000),(-30068103/100000000000000),(348067/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((19/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((19/8)+(1/40)*x)) := (SharedCertificates.h61 (19/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-64965768213267/50000000000000),(-1905863748387/100000000000000),(1699119347/25000000000000),(-22914427/100000000000000),(111929/25000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((19/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((19/8)+(1/40)*x)) := (SharedCertificates.h67 (19/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-24319146325791/4000000000000),(-8388865221893/100000000000000),(36642694937/100000000000000),(-80923927/50000000000000),(1553663/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((19/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((19/8)+(1/40)*x)) := (SharedCertificates.h67 (19/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-32437118309913/5000000000000),(-9493238987161/100000000000000),(6854635667/20000000000000),(-116400673/100000000000000),(557107/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((19/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((19/8)+(1/40)*x)) := (SharedCertificates.h72 (19/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(168005944142321/20000000000000),(422266066811/4000000000000),(-7612048309/12500000000000),(163225001/50000000000000),(538151/20000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((19/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((19/8)+(1/40)*x)) := (SharedCertificates.h72 (19/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(1933958557020189/100000000000000),(13984042987587/50000000000000),(-107735747739/100000000000000),(91985991/25000000000000),(3437613/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((19/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((19/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((19/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(29445345832581/25000000000000),(250432177179/100000000000000),(-1031680733/100000000000000),(83587/2000000000000),(1029/2000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((19/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11312491003587147/100000000000000),(978432692233/10000000000000),(-63061774981/100000000000000),(89706653/25000000000000),(1827409/20000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((19/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(883978603547/100000000000000),(-382282543/50000000000000),(1397261/25000000000000),(-2321/6250000000000),(403/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((19/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4273944961381/25000000000000),(232445523937/100000000000000),(-211621077/20000000000000),(4921209/100000000000000),(95927/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((19/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((19/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-392303440544557/100000000000000),(-5889497725911/100000000000000),(2171647091/12500000000000),(-436907/625000000000),(13585951/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((19/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(21052631578947/50000000000000),(-443213296399/100000000000000),(4665403119/100000000000000),(-49109507/100000000000000),(130611/25000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((19/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-82590198009379/50000000000000),(-741047505449/100000000000000),(15115521841/100000000000000),(-18854449/10000000000000),(11886173/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((19/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((19/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((19/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((19/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((19/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((19/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((19/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((19/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((19/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((19/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (19/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((19/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((19/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(3325934833/100000000000000),(-70019681/50000000000000),(1842623/50000000000000),(-15517/20000000000000),(81/5000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((19/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(115457852953787/100000000000000),(-446121664281/100000000000000),(3979223837/100000000000000),(-33813593/100000000000000),(11049683/10000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((19/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((19/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (19/8) (1/40))

def c134 : Certificate := ⟨(1505/64),(39/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((19/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((19/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(2469135802469/50000000000000),(-36579789667/100000000000000),(67740351/25000000000000),(-1003561/50000000000000),(7491/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((19/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(11612654320987/10000000000000),(68701417463/20000000000000),(541922787/100000000000000),(-802851/20000000000000),(338557/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((19/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((19/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (19/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((19/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (19/8) (1/40))

def c140 : Certificate := ⟨(6007787873169/25000000000000),(-3967481041/20000000000000),(-3730079/25000000000000),(67493/25000000000000),(7913/20000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((19/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(775078805859/20000000000000),(39674810409/50000000000000),(59681261/100000000000000),(-1079891/100000000000000),(85509/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((19/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((19/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(75093394411/50000000000000),(3075110467/50000000000000),(67589391/100000000000000),(11013/100000000000000),(1521/10000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((19/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((19/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(179060080617/10000000000000),(73087615323/100000000000000),(19897359/2500000000000),(19941/100000000000000),(181939/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((19/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-54248577126457/10000000000000),(-1110469364649/10000000000000),(-8265469099/100000000000000),(30368267/20000000000000),(23947089/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((19/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1106133789391963/100000000000000),(-11539352433039/50000000000000),(-26166367227/100000000000000),(60185229/20000000000000),(5001451/10000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((19/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(90572478653029/6250000000000),(28777500296889/100000000000000),(2990216257/100000000000000),(-213343749/50000000000000),(4152537/6250000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((19/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(4125324377638213/100000000000000),(21395561520303/25000000000000),(21620230209/25000000000000),(-1146523217/100000000000000),(18537189/10000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((19/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(2194454439999917/50000000000000),(24124314717693/25000000000000),(105055371829/50000000000000),(-134056307/12500000000000),(212202161/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((19/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(26975243711853/25000000000000),(16484946257/10000000000000),(186951913/100000000000000),(-2148769/100000000000000),(178623/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((19/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((19/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((19/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((19/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(28298482548491773/50000000000000),(42188796377603/50000000000000),(14378964179/20000000000000),(-1169549747/100000000000000),(192574091/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((19/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(17668791927/10000000000000),(-32926901/12500000000000),(84133/50000000000000),(1867/50000000000000),(617/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((19/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(7754671778727/100000000000000),(39734486349/25000000000000),(124436887/100000000000000),(-2122101/100000000000000),(204981/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((19/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((19/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((19/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (19/8) (1/40))

def c175 : Certificate := ⟨(557563242127/2500000000000),(-12814604811/25000000000000),(3694223/10000000000000),(699961/100000000000000),(52319/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((19/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1798313543279/50000000000000),(6834455899/10000000000000),(-12314077/25000000000000),(-933283/100000000000000),(86631/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((19/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((19/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(129357263997/100000000000000),(4916197841/100000000000000),(674479/1562500000000),(-67231/50000000000000),(2791/20000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((19/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((19/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(1542982171173/100000000000000),(29231961091/50000000000000),(50830231/10000000000000),(-1655619/100000000000000),(83631/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((19/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-503472296803411/100000000000000),(-9565080984979/100000000000000),(869170219/12500000000000),(8181517/6250000000000),(24262173/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((19/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-256290901309097/25000000000000),(-3964918546329/20000000000000),(7752632181/100000000000000),(5603797/2000000000000),(3154183/6250000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((19/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(1347830116417363/100000000000000),(24898994994239/100000000000000),(-31728918043/100000000000000),(-324605529/100000000000000),(16796637/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((19/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(3824934863933753/100000000000000),(73578479486743/100000000000000),(-36507077293/100000000000000),(-207630077/20000000000000),(46801259/25000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((19/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(4051595727604783/100000000000000),(20570685928629/25000000000000),(42460560977/100000000000000),(-1248404167/100000000000000),(211914917/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((19/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(107322611437113/100000000000000),(141605315821/100000000000000),(-1383649/2500000000000),(-500257/25000000000000),(360479/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((19/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((19/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((19/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((19/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(56300639682435693/100000000000000),(72623089675417/100000000000000),(-22910084287/50000000000000),(-1022664959/100000000000000),(24241613/12500000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((19/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(177617875327/100000000000000),(-5727803/2500000000000),(440089/100000000000000),(309/12500000000000),(623/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((19/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(7196358248211/100000000000000),(136866164281/100000000000000),(-47635783/50000000000000),(-1852399/100000000000000),(407727/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((19/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((19/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(8631069131789/50000000000000),(137414644999/50000000000000),(-691037613/100000000000000),(998121/50000000000000),(8938187/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((19/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7268268742559/100000000000000),(39209503761/100000000000000),(-28147793/4000000000000),(2061959/25000000000000),(7875083/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((19/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((19/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((19/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((19/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((19/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((19/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (19/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((19/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((19/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((19/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (19/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((19/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(9054126701/25000000000000),(-4841779/6250000000000),(1715077/100000000000000),(-6983/100000000000000),(91/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((19/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(215813598162117/50000000000000),(-1545737943757/100000000000000),(-3261211313/50000000000000),(-2087153/4000000000000),(288939/12500000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((19/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((19/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((19/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((19/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (19/8) (1/40))

def c223 : Certificate := ⟨(1225/64),(7/32),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((19/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(5440225/4096),(26691/1024),(9203/51200),(63/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((19/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((19/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(6096631611/6250000000000),(-1445127493/100000000000000),(4014243/25000000000000),(-39647/25000000000000),(1501/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((19/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(506088984771/390625000000),(623191826529/100000000000000),(298052597/25000000000000),(-3846573/100000000000000),(4051111/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((19/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((19/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (19/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((19/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (19/8) (1/40))

def c231 : Certificate := ⟨(5819925271717/25000000000000),(-6754707441/20000000000000),(-3903371/25000000000000),(6497/2000000000000),(220921/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((19/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1720298913131/25000000000000),(67547074409/50000000000000),(12490787/20000000000000),(-1299403/100000000000000),(507141/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((19/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((19/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(473508536083/100000000000000),(1859218539/10000000000000),(38219889/20000000000000),(-5043/50000000000000),(145807/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((19/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((19/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(5616936335397/100000000000000),(219268130721/100000000000000),(2216068127/100000000000000),(-64689/10000000000000),(870139/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((19/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-240745219743611/25000000000000),(-1889050441311/10000000000000),(-1036416563/12500000000000),(184929639/100000000000000),(142069229/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((19/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1992999381085347/100000000000000),(-20213592529593/50000000000000),(-44179030209/100000000000000),(91518061/25000000000000),(152208207/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((19/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(157007383715979/6250000000000),(23268474022187/50000000000000),(-4356843577/12500000000000),(-534114567/100000000000000),(393046441/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((19/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(7398119199348689/100000000000000),(148444879322347/100000000000000),(127615818779/100000000000000),(-90736983/6250000000000),(559937063/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((19/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(164868270971569/2000000000000),(182267273745349/100000000000000),(246730572789/50000000000000),(-122621483/10000000000000),(691430207/50000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((19/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(114235899841131/100000000000000),(144390241513/50000000000000),(63201463/20000000000000),(-652223/25000000000000),(2174371/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((19/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((19/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((19/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((19/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(11960691728886559/20000000000000),(72244376587729/50000000000000),(39877072729/50000000000000),(-777244977/50000000000000),(238212101/20000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((19/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(16721440911/10000000000000),(-404000071/100000000000000),(75309/10000000000000),(613/20000000000000),(3369/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((19/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(13784175255749/100000000000000),(54294749641/20000000000000),(75429273/50000000000000),(-483739/20000000000000),(1308041/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((19/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((19/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((19/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (19/8) (1/40))

def c259 : Certificate := ⟨(20463442109303/100000000000000),(-78288933677/100000000000000),(18718137/12500000000000),(120833/25000000000000),(64707/12500000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((19/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(6048743854261/100000000000000),(52192622451/50000000000000),(-19966013/10000000000000),(-161111/25000000000000),(99623/10000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((19/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((19/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(5716765971/1562500000000),(12627992171/100000000000000),(84808933/100000000000000),(-494793/100000000000000),(61777/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((19/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((19/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(869242964369/20000000000000),(2984888027/2000000000000),(982544929/100000000000000),(-5999573/100000000000000),(1477041/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((19/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-846561248194611/100000000000000),(-730018503387/5000000000000),(28158961301/100000000000000),(45279451/50000000000000),(1744131/1250000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((19/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-1744854600665807/100000000000000),(-15497346295953/50000000000000),(44057713077/100000000000000),(249922527/100000000000000),(296242369/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((19/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(2223224598466921/100000000000000),(36492158975881/100000000000000),(-103074318643/100000000000000),(-113875361/100000000000000),(385077223/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((19/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(1621414552060059/25000000000000),(114132542812271/100000000000000),(-182224301621/100000000000000),(-878336339/100000000000000),(273099679/25000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((19/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(356789137576633/5000000000000),(68475908946797/50000000000000),(-4827794389/25000000000000),(-340540127/20000000000000),(1314564103/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((19/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(56231680365333/50000000000000),(8855939279/4000000000000),(-314511327/100000000000000),(-1783681/100000000000000),(1058007/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((19/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((19/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((19/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((19/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(58913650358136001/100000000000000),(111505453999707/100000000000000),(-2545089719/1250000000000),(-32229087/4000000000000),(576454963/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((19/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(169739948877/100000000000000),(-64253123/20000000000000),(1194683/100000000000000),(-1051/100000000000000),(3339/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((19/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(484490959777/4000000000000),(26192141167/12500000000000),(-3875079/1000000000000),(-1266981/100000000000000),(7757/312500000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((19/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((19/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(55888058923027/50000000000000),(1675882522599/100000000000000),(-2029137297/20000000000000),(-57136427/100000000000000),(22873557/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((19/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(23531814283379/50000000000000),(42045625973/20000000000000),(-3242397839/50000000000000),(44203563/100000000000000),(11371671/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((19/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((19/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((19/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((19/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((19/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((19/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (19/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((19/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1069397268789153691/100000000000000),(571870197213451/25000000000000),(-45749615777077/100000000000000),0,(69181/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((19/8)+(1/40)*x)) := (SharedCertificates.h297 (19/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9351061847/100000000000000),(-625071/3125000000000),(442831/100000000000000),(-1803/100000000000000),(1/4000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((19/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(20187198335473/3125000000000),(1233577530957/100000000000000),(446257099/5000000000000),(33678297/100000000000000),(3002581/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((19/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((19/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (19/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((19/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (19/8) (1/40))

def c307 : Certificate := ⟨(1610017605051701/50000000000000),(11091229182759/50000000000000),0,0,(67/6250000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((19/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (19/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((19/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (19/8) (1/40))

def c311 : Certificate := ⟨(2154964789896339/100000000000000),(2817541634481/100000000000000),0,0,(67/6250000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((19/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (19/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(1160111762253/25000000000000),(-758402923/12500000000000),(7932683/100000000000000),(-2593/25000000000000),(19/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((19/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(14942402888439/10000000000000),(41699925269/5000000000000),(-272606029/25000000000000),(712841/50000000000000),(2969/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((19/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((19/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (19/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((19/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (19/8) (1/40))

def c316 : Certificate := ⟨(2225070169217/10000000000000),(-20645371367/50000000000000),(130609659/100000000000000),(-413141/100000000000000),(1369/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((19/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(10997193231317/100000000000000),(165162970933/100000000000000),(-522438639/100000000000000),(20657/1250000000000),(6817/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((19/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((19/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1209382589669/100000000000000),(908164553/2500000000000),(2466889/1562500000000),(-34057/2500000000000),(9729/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((19/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((19/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(3561648698861/25000000000000),(423934272149/100000000000000),(109530391/6250000000000),(-811483/5000000000000),(59891/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((19/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1538040326825843/100000000000000),(-11526332480159/50000000000000),(36979943241/50000000000000),(-14514257/6250000000000),(995881/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((19/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1624177685742689/50000000000000),(-12830262767457/25000000000000),(124377181173/100000000000000),(-271082039/100000000000000),(409963/12500000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((19/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(969172869253733/25000000000000),(26289394208353/50000000000000),(-51050717227/20000000000000),(1026289211/100000000000000),(4721833/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((19/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(11973380145592179/100000000000000),(23200771157233/12500000000000),(-510043946209/100000000000000),(1215839347/100000000000000),(11859907/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((19/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(14180524394744683/100000000000000),(253795238383839/100000000000000),(-43185852349/25000000000000),(-306456293/25000000000000),(13486583/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((19/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(123203769052303/100000000000000),(183326261993/50000000000000),(-443498191/50000000000000),(48571/2500000000000),(23363/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((19/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((19/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((19/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((19/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(64212627198647689/100000000000000),(44249435200473/25000000000000),(-565521915491/100000000000000),(1460431911/100000000000000),(555101/3125000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((19/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(77866304777/50000000000000),(-8585327/2000000000000),(2554783/100000000000000),(-2873/20000000000000),(59/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((19/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(22083700688377/100000000000000),(167184864089/50000000000000),(-159391/16000000000),(655881/20000000000000),(47387/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((19/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((19/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((19/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (19/8) (1/40))

def c344 : Certificate := ⟨(145912954439/800000000000),(-83232752187/100000000000000),(244324949/50000000000000),(-2868807/100000000000000),(3411/20000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((19/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(9014507593499/100000000000000),(55488501457/50000000000000),(-325766599/50000000000000),(1912537/50000000000000),(19799/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((19/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((19/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(203153367883/25000000000000),(20008060709/100000000000000),(1423483/25000000000000),(-756481/100000000000000),(4003/20000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((19/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((19/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((19/8)+(1/40)*x)) := (SharedCertificates.h144 (19/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(9604855452189/100000000000000),(58671461013/25000000000000),(4185103/12500000000000),(-547217/6250000000000),(237511/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((19/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((19/8)+(1/40)*x)) := (SharedCertificates.h148 (19/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-630582616332889/50000000000000),(-15504965454013/100000000000000),(18283106869/20000000000000),(-537424131/100000000000000),(1112541/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((19/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((19/8)+(1/40)*x)) := (SharedCertificates.h151 (19/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-1318874980922473/50000000000000),(-8467715120287/25000000000000),(181679919933/100000000000000),(-482618573/50000000000000),(13892791/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((19/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((19/8)+(1/40)*x)) := (SharedCertificates.h154 (19/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(646561050577817/20000000000000),(9186389744953/25000000000000),(-127432890097/50000000000000),(53345283/3125000000000),(9522927/50000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((19/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((19/8)+(1/40)*x)) := (SharedCertificates.h157 (19/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(9756654448178671/100000000000000),(123425954643911/100000000000000),(-687368432399/100000000000000),(11786297/312500000000),(1239807/2500000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((19/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((19/8)+(1/40)*x)) := (SharedCertificates.h160 (19/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(5612130842689499/50000000000000),(40108405637419/25000000000000),(-661222451893/100000000000000),(144296709/6250000000000),(42663603/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((19/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((19/8)+(1/40)*x)) := (SharedCertificates.h41 (19/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(11884162865853/10000000000000),(241962066537/100000000000000),(-81085779/6250000000000),(6893667/100000000000000),(99211/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((19/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((19/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((19/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((19/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((19/8)+(1/40)*x)) := (SharedCertificates.h167 (19/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(31043826137092033/50000000000000),(118920686641079/100000000000000),(-695180901011/100000000000000),(247634147/6250000000000),(29757327/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((19/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(80531310443/50000000000000),(-6169883/2000000000000),(119713/5000000000000),(-18319/100000000000000),(3/1250000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((19/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(9039045022787/50000000000000),(11188620329/5000000000000),(-20174571/1562500000000),(7543387/100000000000000),(217543/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((19/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((19/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(259441291217289/100000000000000),(2050485569061/50000000000000),(-1076638161/25000000000000),(5251927/5000000000000),(3361667/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((19/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(109238438407277/100000000000000),(576846390711/100000000000000),(-3942676299/50000000000000),(127230463/100000000000000),(34343/625000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((19/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((19/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(10738119506835937/100000000000000),(132918243408203/25000000000000),(42959/409600),(2109/2048000),(503906251/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((19/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1849/64),(43/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((19/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(79507/512),(5547/2560),(129/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((19/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(1667491538339853209/100000000000000),(105829282999038617/100000000000000),(2888904414176939/100000000000000),(44242731857299/100000000000000),(26105692121/6250000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((19/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(599703193/10000000000000),(-190304291/50000000000000),(2753199/20000000000000),(-373393/100000000000000),(12669/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((19/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(566550009453/10000000000000),(-2050252577/20000000000000),(-93934857/25000000000000),(4215679/50000000000000),(287209/1250000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((19/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((19/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((19/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel27
