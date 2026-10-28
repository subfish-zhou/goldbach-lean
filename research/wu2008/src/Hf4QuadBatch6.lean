import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel19
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(79/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((79/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (79/40) (1/40)

def c3 : Certificate := ⟨(173047619047619/50000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((79/40)+(1/40)*x)) := (SharedCertificates.h2 (79/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((79/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-254666666666667/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((79/40)+(1/40)*x)) := (SharedCertificates.h4 (79/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(6241/1600),(79/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((79/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(94440529100529/20000000000000),(11954497354497/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((79/40)+(1/40)*x)) := (SharedCertificates.h8 (79/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((79/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((79/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(493039/64000),(18723/64000),(237/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((79/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(938179318214699/12500000000000),(285016501736111/100000000000000),(901950954861/25000000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((79/40)+(1/40)*x)) := (SharedCertificates.h13 (79/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((79/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((79/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(38950081/2560000),(493039/640000),(18723/1280000),(79/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((79/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(2125252435515873/50000000000000),(6725482390873/3125000000000),(4086369047619/100000000000000),(4310515873/12500000000000),(21825397/20000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((79/40)+(1/40)*x)) := (SharedCertificates.h18 (79/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((79/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(3004937889648437/100000000000000),(47546485595703/25000000000000),(493039/10240000),(6241/10240000),(386718751/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((79/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(9788306940540001/50000000000000),(61951309750253/5000000000000),(784193794307/2500000000000),(49632518627/12500000000000),(50388021/2000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((79/40)+(1/40)*x)) := (SharedCertificates.h22 (79/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((79/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(5934752332055663/100000000000000),(14085646357727/3125000000000),(1426394567871/10000000000000),(120370849609/50000000000000),(459423829/20000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((79/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(6663251031016993/50000000000000),(1012139397116501/100000000000000),(32029727756849/100000000000000),(135146530619/25000000000000),(64477339/1250000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((79/40)+(1/40)*x)) := (SharedCertificates.h26 (79/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((79/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(5860567927904967/50000000000000),(1038581658109737/100000000000000),(39439809801633/100000000000000),(832063497923/100000000000000),(10612780773/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((79/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(1390722071780623/50000000000000),(49291415202351/20000000000000),(2924727959/31250000000),(24681248599/12500000000000),(100737189/4000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((79/40)+(1/40)*x)) := (SharedCertificates.h30 (79/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((79/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((79/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((79/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((79/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((79/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (79/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((79/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((79/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (79/40) (1/40))

def c43 : Certificate := ⟨(14161/1600),(119/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((79/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((79/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(26901516909/50000000000000),(-90425267/10000000000000),(5699071/50000000000000),(-127711/100000000000000),(1377/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((79/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-521146693966191/50000000000000),(44624873051/25000000000000),(-1526573791/100000000000000),(653307/5000000000000),(53169237/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((79/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((79/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (79/40) (1/40))

def c52 : Certificate := ⟨(66249999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((79/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (79/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((79/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (79/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((79/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (79/40) (1/40))

def c56 : Certificate := ⟨(23121387283237/100000000000000),(-44549879159/100000000000000),(85837917/100000000000000),(-165391/100000000000000),(321/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((79/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(7514450867051/100000000000000),(178199516633/100000000000000),(-34335167/10000000000000),(661563/100000000000000),(1489/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((79/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((79/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((79/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((79/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((79/40)+(1/40)*x)) := (SharedCertificates.h61 (79/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-54295165224357/50000000000000),(-531096362867/20000000000000),(1605615613/50000000000000),(-9829/390625000000),(43471/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((79/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((79/40)+(1/40)*x)) := (SharedCertificates.h61 (79/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-113362279166651/100000000000000),(-1443922776527/50000000000000),(86127591/12500000000000),(4670683/100000000000000),(14739/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((79/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((79/40)+(1/40)*x)) := (SharedCertificates.h67 (79/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-267265056731659/50000000000000),(-1289298293303/10000000000000),(9664748743/50000000000000),(-355651/1000000000000),(61829/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((79/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((79/40)+(1/40)*x)) := (SharedCertificates.h67 (79/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-566178563439363/100000000000000),(-89970831941/625000000000),(33962557/781250000000),(26195157/100000000000000),(337187/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((79/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((79/40)+(1/40)*x)) := (SharedCertificates.h72 (79/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(46654508191933/6250000000000),(3324058309879/20000000000000),(-29716843531/50000000000000),(31215057/25000000000000),(237613/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((79/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((79/40)+(1/40)*x)) := (SharedCertificates.h72 (79/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(211277655641477/12500000000000),(21290082618273/50000000000000),(-13463785887/50000000000000),(-79191533/50000000000000),(289333/20000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((79/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((79/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((79/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(23118714290487/20000000000000),(383180463511/100000000000000),(-52594331/12500000000000),(198849/100000000000000),(27/400000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((79/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11225271678618089/100000000000000),(15581933877433/100000000000000),(-14176480973/20000000000000),(155885263/100000000000000),(1293517/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((79/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(178169407143/20000000000000),(-618297713/50000000000000),(367091/5000000000000),(-30371/100000000000000),(211/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((79/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(15057285859281/100000000000000),(71684588241/20000000000000),(-12846697/2000000000000),(191857/12500000000000),(29519/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((79/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((79/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((79/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (79/40) (1/40))

def c87 : Certificate := ⟨(20100502512563/100000000000000),(-20201510063/20000000000000),(507575629/100000000000000),(-318829/12500000000000),(2577/20000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((79/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(3266331658291/50000000000000),(16834591719/12500000000000),(-676767507/100000000000000),(3400841/100000000000000),(12777/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((79/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((79/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((79/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((79/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((79/40)+(1/40)*x)) := (SharedCertificates.h61 (79/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-94017827832617/100000000000000),(-199105000351/10000000000000),(8917007053/100000000000000),(-1967019/5000000000000),(18437/4000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((79/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((79/40)+(1/40)*x)) := (SharedCertificates.h61 (79/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-97599154582017/100000000000000),(-133885187837/6250000000000),(500754009/6250000000000),(-27895233/100000000000000),(297321/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((79/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((79/40)+(1/40)*x)) := (SharedCertificates.h67 (79/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-231831128164707/50000000000000),(-2424688753259/25000000000000),(45672650863/100000000000000),(-43582503/20000000000000),(2019029/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((79/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((79/40)+(1/40)*x)) := (SharedCertificates.h67 (79/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-487575926292809/100000000000000),(-1335675444501/12500000000000),(1617332601/4000000000000),(-140914321/100000000000000),(2979837/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((79/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((79/40)+(1/40)*x)) := (SharedCertificates.h72 (79/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(327038977281847/50000000000000),(2557272854707/20000000000000),(-39755106477/50000000000000),(114517693/25000000000000),(89729/2500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((79/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((79/40)+(1/40)*x)) := (SharedCertificates.h72 (79/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(364329179420371/25000000000000),(792861899889/2500000000000),(-25384420819/20000000000000),(215640961/50000000000000),(9377211/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((79/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((79/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((79/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(56746041766621/50000000000000),(286949422667/100000000000000),(-630289337/50000000000000),(1355779/25000000000000),(13661/20000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((79/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1392274115203667/12500000000000),(1211243794169/10000000000000),(-41821808647/50000000000000),(509128559/100000000000000),(3115457/25000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((79/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(224452926753/25000000000000),(-976342273/100000000000000),(121937/1562500000000),(-28429/50000000000000),(47/4000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((79/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(13083960099587/100000000000000),(270507879139/100000000000000),(-267086963/20000000000000),(84471/1250000000000),(26807/20000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((79/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((79/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-29331434591107/10000000000000),(-3252536186989/50000000000000),(10653601941/50000000000000),(-47943491/50000000000000),(3426101/20000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((79/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(10126582278481/20000000000000),(-320461464509/50000000000000),(2028237117/25000000000000),(-102695551/100000000000000),(329153/25000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((79/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-29702718573273/20000000000000),(-282757726817/20000000000000),(14342258161/50000000000000),(-51455689/12500000000000),(10893/50000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((79/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((79/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((79/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((79/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((79/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((79/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((79/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((79/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((79/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((79/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (79/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((79/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((79/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1391008511/20000000000000),(-176077027/50000000000000),(2228823/20000000000000),(-28213/10000000000000),(1793/25000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((79/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(24754640973057/20000000000000),(-604668064631/100000000000000),(244964233/4000000000000),(-29149601/50000000000000),(250610439/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((79/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((79/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (79/40) (1/40))

def c134 : Certificate := ⟨(31641/1600),(179/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((79/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((79/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(2801120448179/50000000000000),(-735588353/1562500000000),(197805271/50000000000000),(-3324459/100000000000000),(28177/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((79/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(110787815126039/100000000000000),(322511357469/100000000000000),(791221069/100000000000000),(-664893/10000000000000),(1062211/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((79/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((79/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (79/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((79/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (79/40) (1/40))

def c140 : Certificate := ⟨(380366686271/1562500000000),(-19112165931/100000000000000),(-3985383/12500000000000),(227931/50000000000000),(7957/12500000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((79/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(2626128314621/100000000000000),(1911216593/2500000000000),(25506451/20000000000000),(-1823449/100000000000000),(4193/1562500000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((79/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((79/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(4310343703/6250000000000),(501910001/12500000000000),(65142303/100000000000000),(99221/100000000000000),(17137/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((79/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((79/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(823963745969/100000000000000),(598337761/1250000000000),(96496379/12500000000000),(1078113/100000000000000),(205339/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((79/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-73527265140341/20000000000000),(-5350462981069/50000000000000),(-17796598233/100000000000000),(51189471/20000000000000),(37573699/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((79/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-148994105947593/20000000000000),(-21967698946567/100000000000000),(-22412981353/50000000000000),(496738493/100000000000000),(38769073/50000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((79/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(495747759556027/50000000000000),(28286315555001/100000000000000),(6035728173/20000000000000),(-737683469/100000000000000),(26048923/25000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((79/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(55669453498353/2000000000000),(81771916923157/100000000000000),(157590384433/100000000000000),(-473232009/25000000000000),(288365147/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((79/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(2903629858443551/100000000000000),(44410911581713/50000000000000),(137156322837/50000000000000),(-1666030673/100000000000000),(318220731/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((79/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(10532122212849/10000000000000),(19614075931/12500000000000),(320206813/100000000000000),(-3547677/100000000000000),(553841/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((79/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((79/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((79/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((79/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(27635380747930461/50000000000000),(81012914285283/100000000000000),(3611065809/2500000000000),(-1930925677/100000000000000),(148208863/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((79/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(7237099493/4000000000000),(-66298449/25000000000000),(-84123/100000000000000),(7137/100000000000000),(199/20000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((79/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(52534645441/1000000000000),(76501423301/50000000000000),(32289299/12500000000000),(-451157/12500000000000),(616921/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((79/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((79/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((79/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (79/40) (1/40))

def c175 : Certificate := ⟨(23128689779161/100000000000000),(-25878454401/50000000000000),(-2788827/25000000000000),(1376133/100000000000000),(176659/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((79/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(49901605889/2000000000000),(13801842347/20000000000000),(14873743/100000000000000),(-366969/20000000000000),(13683/5000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((79/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((79/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(62254256757/100000000000000),(1721835243/50000000000000),(6045617/12500000000000),(-35517/50000000000000),(2071/12500000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((79/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((79/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(371972246849/50000000000000),(102665697/250000000000),(22927773/4000000000000),(-228589/25000000000000),(99293/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((79/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-349292679210537/100000000000000),(-241493790401/2500000000000),(-1019786097/50000000000000),(514487/200000000000),(38316883/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((79/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-707337615254939/100000000000000),(-4951160492359/25000000000000),(-5466804173/50000000000000),(523739751/100000000000000),(4934009/6250000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((79/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(942957271909791/100000000000000),(3198284585777/12500000000000),(-4159323071/50000000000000),(-345429969/50000000000000),(53112659/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((79/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(660840462562251/25000000000000),(36874398924887/50000000000000),(129714899/390625000000),(-49076539/2500000000000),(146832399/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((79/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(2751742310445643/100000000000000),(39894091059579/50000000000000),(119847775299/100000000000000),(-41075603/2000000000000),(40335247/12500000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((79/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(105052414845657/100000000000000),(35365523489/25000000000000),(39056211/50000000000000),(-935181/25000000000000),(35243/6250000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((79/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((79/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((79/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((79/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(1378297922998717/2500000000000),(36550147947591/50000000000000),(23454496833/100000000000000),(-1962039333/100000000000000),(150743867/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((79/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(90691568139/50000000000000),(-12024941/5000000000000),(60429/25000000000000),(1559/25000000000000),(203/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((79/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(199647860199/4000000000000),(3452609983/2500000000000),(16072709/50000000000000),(-456123/12500000000000),(312509/50000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((79/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((79/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(507205812321/4000000000000),(298366574179/100000000000000),(-773327251/100000000000000),(557543/50000000000000),(7014479/25000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((79/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(20063521057/312500000000),(136331493/195312500000),(-637562117/50000000000000),(16705413/100000000000000),(7468373/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((79/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((79/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((79/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((79/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((79/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((79/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (79/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((79/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((79/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((79/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (79/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((79/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(7586010543/20000000000000),(-34838751/25000000000000),(2211441/100000000000000),(-14369/100000000000000),(39/25000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((79/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(454893936896847/100000000000000),(-1374951671293/100000000000000),(-4199821847/100000000000000),(-46178989/100000000000000),(1861709/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((79/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((79/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((79/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((79/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (79/40) (1/40))

def c223 : Certificate := ⟨(25281/1600),(159/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((79/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2445203601/2560000),(13238499/640000),(200603/1280000),(299/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((79/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((79/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(125540412243/100000000000000),(-421984579/20000000000000),(13297833/50000000000000),(-297991/100000000000000),(3207/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((79/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(119910885971721/100000000000000),(290756919349/50000000000000),(358450817/25000000000000),(-6511433/100000000000000),(3097971/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((79/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((79/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (79/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((79/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (79/40) (1/40))

def c231 : Certificate := ⟨(2976822087161/12500000000000),(-32979630619/100000000000000),(-35644007/100000000000000),(531257/100000000000000),(353501/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((79/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(948338642169/20000000000000),(5276740899/4000000000000),(5703041/4000000000000),(-2125031/100000000000000),(1554767/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((79/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((79/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(224836545057/100000000000000),(781896453/6250000000000),(187546001/100000000000000),(174643/100000000000000),(78481/50000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((79/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((79/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(2676716422299/100000000000000),(74172256343/50000000000000),(1099559127/50000000000000),(77911/5000000000000),(469233/25000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((79/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-663710127837431/100000000000000),(-18458028020059/100000000000000),(-9828428907/50000000000000),(75158473/25000000000000),(217721667/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((79/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1359145197107959/100000000000000),(-9671991487161/25000000000000),(-66149204253/100000000000000),(571120103/100000000000000),(114328521/25000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((79/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1761105390638531/100000000000000),(47161202235759/100000000000000),(-609615477/50000000000000),(-226149183/25000000000000),(300914073/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((79/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(2531142043065491/50000000000000),(143073912333873/100000000000000),(214372289291/100000000000000),(-561491903/25000000000000),(423037477/25000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((79/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(5458853833038769/100000000000000),(165438881313823/100000000000000),(140487942017/25000000000000),(-1685854843/100000000000000),(492681949/25000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((79/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(109708222966747/100000000000000),(138173694099/50000000000000),(472698051/100000000000000),(-4075419/100000000000000),(51039/1562500000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((79/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((79/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((79/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((79/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(57519117841421187/100000000000000),(140563324170863/100000000000000),(17212919701/10000000000000),(-2378947513/100000000000000),(1767380383/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((79/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(86927619679/50000000000000),(-53107713/12500000000000),(517991/100000000000000),(1799/25000000000000),(5407/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((79/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(37072278897/390625000000),(52886316737/20000000000000),(9449141/3125000000000),(-254293/6250000000000),(1880373/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((79/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((79/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((79/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (79/40) (1/40))

def c259 : Certificate := ⟨(21751772095871/100000000000000),(-82541165647/100000000000000),(109701157/100000000000000),(256049/20000000000000),(179123/20000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((79/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(4330970538837/100000000000000),(110054887527/100000000000000),(-14626821/10000000000000),(-341399/20000000000000),(1550801/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((79/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((79/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(93786529041/50000000000000),(953288951/10000000000000),(27112779/25000000000000),(-46981/10000000000000),(141299/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((79/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((79/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(446925845843/20000000000000),(113156074211/100000000000000),(635792659/50000000000000),(-2900723/50000000000000),(845729/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((79/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-606239094303611/100000000000000),(-15400324178859/100000000000000),(20653886623/100000000000000),(119961913/50000000000000),(217164573/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((79/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-619463893721781/50000000000000),(-32149547764013/100000000000000),(12893769081/50000000000000),(543954491/100000000000000),(113501771/25000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((79/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1613766059980599/100000000000000),(19807621836427/50000000000000),(-11095800163/12500000000000),(-537081117/100000000000000),(599618281/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((79/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(115435269960059/2500000000000),(11904938485797/10000000000000),(-116187982051/100000000000000),(-124924297/6250000000000),(67270119/4000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((79/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(4947476468450619/100000000000000),(136032991994763/100000000000000),(84885969923/100000000000000),(-21305629/781250000000),(966381949/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((79/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(27212378533939/25000000000000),(57410666141/25000000000000),(-23010663/12500000000000),(-19419/500000000000),(3242901/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((79/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((79/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((79/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((79/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(57081680627124771/100000000000000),(23431622923171/20000000000000),(-28123429313/20000000000000),(-974268307/50000000000000),(349955237/20000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((79/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(10949222117/6250000000000),(-35956621/10000000000000),(29239/2500000000000),(2693/100000000000000),(5411/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((79/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(8667363003471/100000000000000),(110261708753/50000000000000),(-141277657/50000000000000),(-1679287/50000000000000),(3682501/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((79/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((79/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(82599033328447/100000000000000),(978184504771/50000000000000),(-3670173851/50000000000000),(-62811007/100000000000000),(6955731/20000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((79/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(1672891814247/4000000000000),(2882315271/625000000000),(-4777116149/50000000000000),(89136607/100000000000000),(10576567/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((79/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((79/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((79/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((79/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((79/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((79/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (79/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((79/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(127635709316070167/12500000000000),(3751468493720239/100000000000000),(-45749615777077/100000000000000),0,(66157/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((79/40)+(1/40)*x)) := (SharedCertificates.h297 (79/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9793497499/100000000000000),(-8995327/25000000000000),(570991/100000000000000),(-371/10000000000000),(21/50000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((79/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(628419660065129/100000000000000),(60559217459/6250000000000),(1940932373/25000000000000),(14886737/100000000000000),(2469303/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((79/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((79/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (79/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((79/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (79/40) (1/40))

def c307 : Certificate := ⟨(1432557938127551/50000000000000),(11091229182759/50000000000000),0,0,(263/25000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((79/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (79/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((79/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (79/40) (1/40))

def c311 : Certificate := ⟨(2109884123744639/100000000000000),(2817541634481/100000000000000),0,0,(263/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((79/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (79/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4739596780439/100000000000000),(-3164631439/50000000000000),(1056513/12500000000000),(-11287/100000000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((79/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(135794939826833/100000000000000),(435009183473/50000000000000),(-116182353/10000000000000),(775749/50000000000000),(627/20000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((79/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((79/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (79/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((79/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (79/40) (1/40))

def c316 : Certificate := ⟨(22946572082671/100000000000000),(-45810396923/100000000000000),(76315427/50000000000000),(-101707/20000000000000),(1759/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((79/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(128339244833/1562500000000),(18324158769/10000000000000),(-610523419/100000000000000),(1017069/50000000000000),(1657/20000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((79/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((79/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(134930118773/20000000000000),(15050935671/50000000000000),(235481527/100000000000000),(-190331/10000000000000),(6301/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((79/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((79/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(7984979417269/100000000000000),(176902506673/50000000000000),(1342507141/50000000000000),(-4609989/20000000000000),(157979/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((79/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-287315942629373/25000000000000),(-1600633121867/6250000000000),(17258677149/20000000000000),(-283750151/100000000000000),(612083/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((79/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-2394236479837531/100000000000000),(-55517115965261/100000000000000),(2762451259/2000000000000),(-15088073/5000000000000),(511397/12500000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((79/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(2965623311549779/100000000000000),(30800379244719/50000000000000),(-310819597563/100000000000000),(1301698211/100000000000000),(5869711/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((79/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(8867985000786201/100000000000000),(2536220387549/1250000000000),(-571807032457/100000000000000),(678724843/50000000000000),(2998643/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((79/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2520294672615607/25000000000000),(2017454631927/781250000000),(-3987172857/4000000000000),(-926719333/50000000000000),(8242927/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((79/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(117102073932489/100000000000000),(198292523361/50000000000000),(-985565311/100000000000000),(1082483/50000000000000),(7293/25000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((79/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((79/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((79/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((79/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(61229729415834387/100000000000000),(6133144488809/3125000000000),(-159948573893/25000000000000),(163336171/10000000000000),(11415699/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((79/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(163319356387/100000000000000),(-261745063/50000000000000),(423061/12500000000000),(-5169/25000000000000),(181/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((79/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(8232258076743/50000000000000),(92243111691/25000000000000),(-234685969/20000000000000),(1037577/25000000000000),(23969/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((79/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((79/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((79/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (79/40) (1/40))

def c344 : Certificate := ⟨(4927226641427/25000000000000),(-4055409633/4000000000000),(656929151/100000000000000),(-851319/20000000000000),(1743/6250000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((79/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(7054791245721/100000000000000),(135180321099/100000000000000),(-875905537/100000000000000),(5675459/100000000000000),(14287/25000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((79/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((79/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(497700795207/100000000000000),(19073378917/100000000000000),(59150577/100000000000000),(-1567321/100000000000000),(15669/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((79/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((79/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((79/40)+(1/40)*x)) := (SharedCertificates.h144 (79/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(5902186038223/100000000000000),(44968757161/20000000000000),(164653223/25000000000000),(-9234497/50000000000000),(11733/3125000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((79/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((79/40)+(1/40)*x)) := (SharedCertificates.h148 (79/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-98725438749701/10000000000000),(-3780280820021/20000000000000),(122925485921/100000000000000),(-796611337/100000000000000),(2010663/25000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((79/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((79/40)+(1/40)*x)) := (SharedCertificates.h151 (79/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-127811892806501/6250000000000),(-1620740726423/4000000000000),(237022123869/100000000000000),(-684814747/50000000000000),(509879/2500000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((79/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((79/40)+(1/40)*x)) := (SharedCertificates.h154 (79/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(2571824834007331/100000000000000),(928430046349/2000000000000),(-178681547759/50000000000000),(8273987/312500000000),(28575887/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((79/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((79/40)+(1/40)*x)) := (SharedCertificates.h157 (79/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(7588967681251877/100000000000000),(4646589947009/3125000000000),(-45234302723/5000000000000),(84410777/1562500000000),(72944291/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((79/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((79/40)+(1/40)*x)) := (SharedCertificates.h160 (79/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(2119575615810539/25000000000000),(91718290522387/50000000000000),(-389145500881/50000000000000),(101287667/4000000000000),(126870687/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((79/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((79/40)+(1/40)*x)) := (SharedCertificates.h41 (79/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(114607283286649/100000000000000),(57886804223/20000000000000),(-1692660497/100000000000000),(9783597/100000000000000),(72817/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((79/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((79/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((79/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((79/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((79/40)+(1/40)*x)) := (SharedCertificates.h167 (79/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(11997829459400329/20000000000000),(144613362083159/100000000000000),(-184947346111/20000000000000),(1146928333/20000000000000),(8874723/10000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((79/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(166696818517/100000000000000),(-401849143/100000000000000),(3538363/100000000000000),(-1533/5000000000000),(419/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((79/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(14133060470473/100000000000000),(33964119851/12500000000000),(-1734531551/100000000000000),(11239843/100000000000000),(342587/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((79/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((79/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(3845623740169/2000000000000),(216133374761/5000000000000),(-1211347869/12500000000000),(61417089/50000000000000),(447291/10000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((79/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(97357563042253/100000000000000),(956318186917/100000000000000),(-4253004763/25000000000000),(69384133/25000000000000),(10915153/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((79/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((79/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(4526425428710937/100000000000000),(66805821533203/25000000000000),(642823/10240000),(1501/2048000),(425781251/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((79/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(39601/1600),(199/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((79/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(7880599/64000),(118803/64000),(597/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((79/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(557358495423030959/100000000000000),(20653378763141387/50000000000000),(655626585771087/50000000000000),(4648218079663/20000000000000),(126394372889/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((79/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(17941773709/100000000000000),(-1329694447/100000000000000),(56335659/100000000000000),(-179501/10000000000000),(36091/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((79/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2844018828017/50000000000000),(2222706947/20000000000000),(-3372887/312500000000),(2377313/10000000000000),(44774519/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((79/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((79/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((79/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel19

namespace Hf4Quad.Panel20
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(81/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((81/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (81/40) (1/40)

def c3 : Certificate := ⟨(177428571428571/50000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((81/40)+(1/40)*x)) := (SharedCertificates.h2 (81/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((81/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-263428571428571/100000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((81/40)+(1/40)*x)) := (SharedCertificates.h4 (81/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(6561/1600),(81/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((81/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(99282857142857/20000000000000),(6128571428571/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((81/40)+(1/40)*x)) := (SharedCertificates.h8 (81/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((81/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((81/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(531441/64000),(19683/64000),(243/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((81/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(103552263/1280000),(3835269/1280000),(47349/1280000),(608912037/4000000000000),(1/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((81/40)+(1/40)*x)) := (SharedCertificates.h13 (81/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((81/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((81/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(43046721/2560000),(531441/640000),(19683/1280000),(81/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((81/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(2348779419642857/50000000000000),(115989107142857/50000000000000),(2147946428571/50000000000000),(35357142857/100000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((81/40)+(1/40)*x)) := (SharedCertificates.h18 (81/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((81/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1702531445800781/50000000000000),(52547266845703/25000000000000),(531441/10240000),(6561/10240000),(49560547/12500000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((81/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(22183354171582027/100000000000000),(342335712524413/25000000000000),(4226366821289/12500000000000),(13044342041/3125000000000),(258302229/10000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((81/40)+(1/40)*x)) := (SharedCertificates.h22 (81/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((81/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(6895252355493163/100000000000000),(510759433740233/100000000000000),(1576418005371/10000000000000),(259492675781/100000000000000),(2414599613/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((81/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(3096661481133649/20000000000000),(573455829839563/50000000000000),(7079701602957/20000000000000),(291345744977/50000000000000),(2710994911/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((81/40)+(1/40)*x)) := (SharedCertificates.h26 (81/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((81/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(2792577203974731/20000000000000),(12066691622113/1000000000000),(11172862613067/25000000000000),(919577169799/100000000000000),(11437246103/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((81/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(82835375395679/2500000000000),(143172253770309/50000000000000),(10605352131133/100000000000000),(218217122039/100000000000000),(2714076657/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((81/40)+(1/40)*x)) := (SharedCertificates.h30 (81/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((81/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((81/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((81/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((81/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((81/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (81/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((81/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((81/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (81/40) (1/40))

def c43 : Certificate := ⟨(14641/1600),(121/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((81/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((81/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(6504890051/12500000000000),(-860150751/100000000000000),(426521/4000000000000),(-117499/100000000000000),(249/20000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((81/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-208388478535669/20000000000000),(8627312483/5000000000000),(-1450865551/100000000000000),(12198517/100000000000000),(49696073/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((81/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((81/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (81/40) (1/40))

def c52 : Certificate := ⟨(26833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((81/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (81/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((81/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (81/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((81/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (81/40) (1/40))

def c56 : Certificate := ⟨(23032629558541/100000000000000),(-2763031377/6250000000000),(8485317/10000000000000),(-81433/50000000000000),(79/25000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((81/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(3934740882917/50000000000000),(88417004063/50000000000000),(-84853171/25000000000000),(651463/100000000000000),(23/1562500000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((81/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((81/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((81/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((81/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((81/40)+(1/40)*x)) := (SharedCertificates.h61 (81/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-28472117329361/25000000000000),(-660666788517/25000000000000),(3196081821/100000000000000),(-2533319/100000000000000),(8559/20000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((81/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((81/40)+(1/40)*x)) := (SharedCertificates.h61 (81/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-14891897131/12500000000),(-2885033868673/100000000000000),(89588789/12500000000000),(1139881/25000000000000),(58343/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((81/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((81/40)+(1/40)*x)) := (SharedCertificates.h67 (81/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-560239044642867/100000000000000),(-3204022322929/25000000000000),(19117928143/100000000000000),(-34960163/100000000000000),(122709/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((81/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((81/40)+(1/40)*x)) := (SharedCertificates.h67 (81/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-297475816535817/50000000000000),(-7188816768227/50000000000000),(4501687747/100000000000000),(25303087/100000000000000),(331799/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((81/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((81/40)+(1/40)*x)) := (SharedCertificates.h72 (81/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(389737987566233/50000000000000),(4096012196137/25000000000000),(-29344638337/50000000000000),(123278973/100000000000000),(59243/25000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((81/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((81/40)+(1/40)*x)) := (SharedCertificates.h72 (81/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(221909076286169/12500000000000),(21235289194041/50000000000000),(-3482485979/12500000000000),(-152418223/100000000000000),(1420163/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((81/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((81/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((81/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(23271650192859/20000000000000),(190749928151/50000000000000),(-419542743/100000000000000),(41013/20000000000000),(1661/25000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((81/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5628076630134863/50000000000000),(3825066937339/25000000000000),(-17488110349/25000000000000),(38525803/25000000000000),(636653/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((81/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(888402971137/100000000000000),(-1207588687/100000000000000),(1790629/25000000000000),(-7351/25000000000000),(41/20000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((81/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(15771574615591/100000000000000),(355871889053/100000000000000),(-633223787/100000000000000),(300461/20000000000000),(29009/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((81/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((81/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((81/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (81/40) (1/40))

def c87 : Certificate := ⟨(9950248756219/50000000000000),(-99007450311/100000000000000),(492574379/100000000000000),(-2450619/100000000000000),(2451/20000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((81/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(3399668325041/50000000000000),(132009933747/100000000000000),(-8209573/1250000000000),(3267491/100000000000000),(12357/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((81/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((81/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((81/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((81/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((81/40)+(1/40)*x)) := (SharedCertificates.h61 (81/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-97964571834017/100000000000000),(-1955848670143/100000000000000),(8684993049/100000000000000),(-38006933/100000000000000),(55557/12500000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((81/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((81/40)+(1/40)*x)) := (SharedCertificates.h61 (81/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-20370330827591/20000000000000),(-2110446774281/100000000000000),(980840873/12500000000000),(-13609839/50000000000000),(14329/2500000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((81/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((81/40)+(1/40)*x)) := (SharedCertificates.h67 (81/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-482878802354257/100000000000000),(-4759323022221/50000000000000),(44390061667/100000000000000),(-209683969/100000000000000),(195227/10000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((81/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((81/40)+(1/40)*x)) := (SharedCertificates.h67 (81/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-508786120889691/100000000000000),(-657834258653/6250000000000),(39597663217/100000000000000),(-34411251/25000000000000),(1434607/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((81/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((81/40)+(1/40)*x)) := (SharedCertificates.h72 (81/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(339668133535213/50000000000000),(1559217621101/12500000000000),(-19205251609/25000000000000),(438502807/100000000000000),(1729311/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((81/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((81/40)+(1/40)*x)) := (SharedCertificates.h72 (81/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(190030177010707/12500000000000),(7802983020421/25000000000000),(-31089401699/25000000000000),(211764459/50000000000000),(9004201/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((81/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((81/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((81/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(4562439323559/4000000000000),(70492866777/25000000000000),(-245715379/20000000000000),(209813/4000000000000),(65839/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((81/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11162087250548061/100000000000000),(5891941103749/50000000000000),(-40328325929/50000000000000),(486725521/100000000000000),(5984483/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((81/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(55993111859/6250000000000),(-189159241/20000000000000),(3736067/50000000000000),(-53789/100000000000000),(1119/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((81/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(1361968762617/10000000000000),(265246127081/100000000000000),(-161964237/12500000000000),(1621249/25000000000000),(8019/6250000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((81/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((81/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-76560005260043/25000000000000),(-6420978397937/100000000000000),(20743707591/100000000000000),(-45988837/50000000000000),(16673211/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((81/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(24691358024691/50000000000000),(-38103947569/6250000000000),(1881676423/25000000000000),(-92922293/100000000000000),(290383/25000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((81/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-37807410004959/25000000000000),(-1303820937007/100000000000000),(26340360997/100000000000000),(-185305357/50000000000000),(20083383/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((81/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((81/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((81/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((81/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((81/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((81/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((81/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((81/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((81/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((81/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (81/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((81/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((81/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(393321873/6250000000000),(-155386419/50000000000000),(4795877/50000000000000),(-118417/50000000000000),(5859/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((81/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(383087210127/312500000000),(-4646835843/800000000000),(2893358769/50000000000000),(-54248129/100000000000000),(224156811/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((81/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((81/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (81/40) (1/40))

def c134 : Certificate := ⟨(32361/1600),(181/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((81/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((81/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(2754820936639/50000000000000),(-22767115179/50000000000000),(376315953/100000000000000),(-62201/2000000000000),(25919/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((81/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(55717975206609/50000000000000),(40699775743/12500000000000),(752631899/100000000000000),(-1244023/20000000000000),(500253/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((81/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((81/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (81/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((81/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (81/40) (1/40))

def c140 : Certificate := ⟨(24305119642453/100000000000000),(-4808587669/25000000000000),(-7309849/25000000000000),(42577/10000000000000),(59777/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((81/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(347440178773/12500000000000),(38468701351/50000000000000),(116957579/100000000000000),(-1703083/100000000000000),(252769/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((81/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((81/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(4828587113/6250000000000),(4276983191/100000000000000),(65695361/100000000000000),(85293/100000000000000),(16931/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((81/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((81/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(922793954061/100000000000000),(25483579649/50000000000000),(388965191/50000000000000),(113789/12500000000000),(101407/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((81/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-389107350970051/100000000000000),(-2153821952293/20000000000000),(-16312146233/100000000000000),(47819867/20000000000000),(35392009/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((81/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-394540661329077/50000000000000),(-22141171559779/100000000000000),(-41942085603/100000000000000),(232495223/50000000000000),(2925839/4000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((81/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(1048183066155977/100000000000000),(7099595689253/25000000000000),(80953581/312500000000),(-343744333/50000000000000),(12269263/12500000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((81/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(589526394928913/20000000000000),(82380056798319/100000000000000),(2290631323/1562500000000),(-886026333/50000000000000),(10876647/4000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((81/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(1541178813264801/50000000000000),(22474869616981/25000000000000),(1653825921/625000000000),(-392216757/25000000000000),(301460081/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((81/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(3301134382943/3125000000000),(31630357719/20000000000000),(299610519/100000000000000),(-3320873/100000000000000),(522469/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((81/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((81/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((81/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((81/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(11086669979981511/20000000000000),(40784008162181/50000000000000),(26646298529/20000000000000),(-903898133/50000000000000),(279878901/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((81/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(22549602401/12500000000000),(-265446897/100000000000000),(-42981/100000000000000),(823/12500000000000),(467/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((81/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2780237557437/50000000000000),(76996888483/50000000000000),(59347923/25000000000000),(-3368289/100000000000000),(73031/12500000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((81/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((81/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((81/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (81/40) (1/40))

def c175 : Certificate := ⟨(11512571061583/50000000000000),(-25892733503/50000000000000),(-3234121/100000000000000),(1265789/100000000000000),(164921/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((81/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1316571917889/50000000000000),(69047289341/100000000000000),(26951/625000000000),(-42193/2500000000000),(128807/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((81/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((81/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(34667232299/50000000000000),(1818114443/50000000000000),(11975593/25000000000000),(-41463/50000000000000),(127/781250000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((81/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((81/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(414181111407/50000000000000),(43347505221/100000000000000),(141819593/25000000000000),(-1054869/100000000000000),(48713/25000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((81/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-368618325040113/100000000000000),(-4832453571959/50000000000000),(-558799147/100000000000000),(118316301/50000000000000),(36070653/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((81/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-373493262360591/50000000000000),(-19842252883629/100000000000000),(-3955685299/50000000000000),(6052639/1250000000000),(74407639/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((81/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(994091147144741/100000000000000),(25544957390537/100000000000000),(-6140442591/50000000000000),(-630733401/100000000000000),(24996967/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((81/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(697744219332489/25000000000000),(73858682269613/100000000000000),(21885362071/100000000000000),(-226608709/12500000000000),(138345341/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((81/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1455890949386853/50000000000000),(80243452246649/100000000000000),(107915853001/100000000000000),(-15401539/800000000000),(61040863/20000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((81/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(52667811068077/50000000000000),(8858175473/6250000000000),(14131673/25000000000000),(-1729183/50000000000000),(132871/25000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((81/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((81/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((81/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((81/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(55278195946244541/100000000000000),(18292798124793/25000000000000),(6073206729/50000000000000),(-904702481/50000000000000),(142194477/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((81/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(90451577053/50000000000000),(-29932461/12500000000000),(13861/5000000000000),(5607/100000000000000),(951/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((81/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(5267505295569/100000000000000),(138190392227/100000000000000),(11144503/100000000000000),(-671087/20000000000000),(590723/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((81/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((81/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(3318448645397/25000000000000),(295287648953/100000000000000),(-765904877/100000000000000),(1347789/100000000000000),(5296009/20000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((81/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(6554960287203/100000000000000),(32447812783/50000000000000),(-589702597/50000000000000),(3806533/25000000000000),(13738711/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((81/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((81/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((81/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((81/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((81/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((81/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (81/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((81/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((81/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((81/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (81/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((81/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(18830037959/50000000000000),(-26135379/20000000000000),(2128781/100000000000000),(-33/250000000000),(71/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((81/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(28257929034761/6250000000000),(-348076443351/25000000000000),(-2238734243/50000000000000),(-46402203/100000000000000),(3440853/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((81/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((81/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((81/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((81/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (81/40) (1/40))

def c223 : Certificate := ⟨(25921/1600),(161/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((81/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2552726001/2560000),(13643301/640000),(204203/1280000),(301/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((81/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((81/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(121424614287/100000000000000),(-1003509209/50000000000000),(24880393/100000000000000),(-54833/20000000000000),(2901/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((81/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(30269899419123/25000000000000),(587172713277/100000000000000),(698035467/50000000000000),(-6073629/100000000000000),(146367/2500000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((81/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((81/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (81/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((81/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (81/40) (1/40))

def c231 : Certificate := ⟨(23748479040969/100000000000000),(-33115968933/100000000000000),(-16279307/50000000000000),(248871/50000000000000),(10381/3125000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((81/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(2503041918061/50000000000000),(132463875729/100000000000000),(26046891/20000000000000),(-1990971/100000000000000),(183601/12500000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((81/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((81/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(125304376871/50000000000000),(13262505343/100000000000000),(7540243/4000000000000),(145687/100000000000000),(39017/25000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((81/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((81/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(1491106838139/50000000000000),(157158267707/100000000000000),(110370527/5000000000000),(1209687/100000000000000),(1865719/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((81/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-350351222470137/50000000000000),(-9266562385803/50000000000000),(-4477564269/25000000000000),(140932909/50000000000000),(8227557/4000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((81/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-1436781225949627/100000000000000),(-2434115411471/6250000000000),(-62824501261/100000000000000),(268835983/50000000000000),(433120161/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((81/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(185541580419427/10000000000000),(23572857163683/50000000000000),(-6465144047/100000000000000),(-844942309/100000000000000),(142156231/25000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((81/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(2674635849297361/50000000000000),(7195248959247/5000000000000),(201289958317/100000000000000),(-1058461439/50000000000000),(800740309/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((81/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(2895983039817649/50000000000000),(8383339127531/5000000000000),(552077081161/100000000000000),(-200921703/12500000000000),(234880079/12500000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((81/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(55131388212993/50000000000000),(278190256801/100000000000000),(89794997/20000000000000),(-767251/20000000000000),(773421/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((81/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((81/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((81/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((81/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(11560182850028453/20000000000000),(141223840459137/100000000000000),(79131062013/50000000000000),(-280693891/12500000000000),(83822639/5000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((81/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(86503822039/50000000000000),(-84541237/20000000000000),(111817/20000000000000),(407/6250000000000),(5079/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((81/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(10020544060173/100000000000000),(13279667577/5000000000000),(55755941/20000000000000),(-3799971/100000000000000),(223899/6250000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((81/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((81/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((81/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (81/40) (1/40))

def c259 : Certificate := ⟨(10793569267593/50000000000000),(-5130471677/6250000000000),(584873/500000000000),(573229/50000000000000),(833441/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((81/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(1137620488271/25000000000000),(109450062441/100000000000000),(-31193227/20000000000000),(-382153/25000000000000),(45707/3125000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((81/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((81/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(207068860053/100000000000000),(4980505339/50000000000000),(5279937/5000000000000),(-480529/100000000000000),(34857/25000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((81/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((81/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(2465981058421/100000000000000),(29543076539/25000000000000),(618207813/50000000000000),(-5916369/100000000000000),(834397/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((81/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-636955259408731/100000000000000),(-15314932314467/100000000000000),(22017015337/100000000000000),(21486771/10000000000000),(51205257/25000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((81/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-651559740496067/50000000000000),(-32040068643721/100000000000000),(7225907407/25000000000000),(99101839/20000000000000),(429055769/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((81/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1692637335127671/100000000000000),(3925403141277/10000000000000),(-91767157573/100000000000000),(-232220613/50000000000000),(282751097/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((81/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(2427514603602173/50000000000000),(59280702899271/50000000000000),(-63808334417/50000000000000),(-1813712979/100000000000000),(1588407909/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((81/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(5219860506519781/100000000000000),(17042557663631/12500000000000),(3450393691/5000000000000),(-1283860707/50000000000000),(1836497801/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((81/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(109308032766221/100000000000000),(5721528389/2500000000000),(-20633353/10000000000000),(-3537753/100000000000000),(766169/25000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((81/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((81/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((81/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((81/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(28657709594793241/50000000000000),(116573039406517/100000000000000),(-15173132677/10000000000000),(-175921017/10000000000000),(103480533/6250000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((81/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(174473119823/100000000000000),(-354858469/100000000000000),(9469/800000000000),(251/12500000000000),(203/4000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((81/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(9107253476133/100000000000000),(219354339349/100000000000000),(-30163191/10000000000000),(-300629/10000000000000),(3495263/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((81/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((81/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(86481911259553/100000000000000),(192626136013/10000000000000),(-7711716763/100000000000000),(-30521931/50000000000000),(16451607/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((81/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(42707116671383/100000000000000),(423991823873/100000000000000),(-4521361077/50000000000000),(81493427/100000000000000),(973971/5000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((81/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((81/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((81/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((81/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((81/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((81/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (81/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((81/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1028405613052893511/100000000000000),(713694006122387/20000000000000),(-45749615777077/100000000000000),0,(26647/20000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((81/40)+(1/40)*x)) := (SharedCertificates.h297 (81/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9723789789/100000000000000),(-3374063/10000000000000),(34353/6250000000000),(-3409/100000000000000),(1/2500000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((81/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(315194366997203/50000000000000),(500095306613/50000000000000),(393002911/5000000000000),(429233/2500000000000),(934889/20000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((81/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((81/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (81/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((81/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (81/40) (1/40))

def c307 : Certificate := ⟨(2909480792986139/100000000000000),(11091229182759/50000000000000),0,0,(211/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((81/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (81/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((81/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (81/40) (1/40))

def c311 : Certificate := ⟨(1057759603506801/50000000000000),(2817541634481/100000000000000),0,0,(527/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((81/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (81/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(590871496631/12500000000000),(-6295589421/100000000000000),(8384743/100000000000000),(-349/3125000000000),(1/5000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((81/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(137530341645669/100000000000000),(865389624861/100000000000000),(-72035251/6250000000000),(1535011/100000000000000),(3117/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((81/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((81/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (81/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((81/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (81/40) (1/40))

def c316 : Certificate := ⟨(2285555777089/10000000000000),(-45205922157/100000000000000),(74809931/50000000000000),(-247601/50000000000000),(1703/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((81/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(4288884458219/50000000000000),(180823688623/100000000000000),(-11969589/2000000000000),(990403/50000000000000),(4041/50000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((81/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((81/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(367890597919/50000000000000),(3877659539/12500000000000),(44859939/20000000000000),(-228071/12500000000000),(12187/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((81/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((81/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(2175786782159/25000000000000),(364272515553/100000000000000),(2549735887/100000000000000),(-22050813/100000000000000),(152409/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((81/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-150017639056521/12500000000000),(-12634166300473/50000000000000),(5288277369/6250000000000),(-55320297/20000000000000),(596129/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((81/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-626180156974989/25000000000000),(-13742057855551/25000000000000),(17040446533/12500000000000),(-11915971/4000000000000),(3976843/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((81/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(385948985670627/12500000000000),(12074588804387/20000000000000),(-151563206317/50000000000000),(1262922423/100000000000000),(2854889/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((81/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(4635751929634601/50000000000000),(200626622217143/100000000000000),(-140928731081/25000000000000),(83743253/6250000000000),(14547947/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((81/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(5298616857256693/50000000000000),(257813599669741/100000000000000),(-55263461457/50000000000000),(-1763065453/100000000000000),(16072713/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((81/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(58945659514357/50000000000000),(196334326779/50000000000000),(-194531841/20000000000000),(534261/25000000000000),(28351/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((81/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((81/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((81/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((81/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(6161970451063917/10000000000000),(96860481163647/50000000000000),(-157514389869/25000000000000),(806085003/50000000000000),(1105227/5000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((81/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(40571437657/25000000000000),(-510196407/100000000000000),(815831/25000000000000),(-9861/50000000000000),(17/10000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((81/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(17197800279401/100000000000000),(11385250931/3125000000000),(-574451549/50000000000000),(4026007/100000000000000),(58141/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((81/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((81/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((81/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (81/40) (1/40))

def c344 : Certificate := ⟨(19508730183539/100000000000000),(-6175483429/6250000000000),(316018747/50000000000000),(-2021457/50000000000000),(13077/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((81/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(7321693088613/100000000000000),(131743646483/100000000000000),(-42135833/5000000000000),(5390551/100000000000000),(54501/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((81/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((81/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(268035948419/50000000000000),(9645865459/50000000000000),(12540407/25000000000000),(-1431093/100000000000000),(1181/4000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((81/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((81/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((81/40)+(1/40)*x)) := (SharedCertificates.h144 (81/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(3177181842007/50000000000000),(56815831757/25000000000000),(552798049/100000000000000),(-16828371/100000000000000),(353229/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((81/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((81/40)+(1/40)*x)) := (SharedCertificates.h148 (81/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1024571785399143/100000000000000),(-4604774878471/25000000000000),(118266662289/100000000000000),(-756753637/100000000000000),(1533577/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((81/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((81/40)+(1/40)*x)) := (SharedCertificates.h151 (81/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-132818129150693/6250000000000),(-19793309591127/50000000000000),(228988030619/100000000000000),(-130896189/10000000000000),(3879937/20000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((81/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((81/40)+(1/40)*x)) := (SharedCertificates.h154 (81/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1331629633298391/50000000000000),(22511610995367/50000000000000),(-341924480889/100000000000000),(500050023/20000000000000),(27104077/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((81/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((81/40)+(1/40)*x)) := (SharedCertificates.h157 (81/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(7882773412697911/100000000000000),(145135965813027/100000000000000),(-87301564921/10000000000000),(2578410783/50000000000000),(69364709/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((81/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((81/40)+(1/40)*x)) := (SharedCertificates.h160 (81/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(4421041347670351/50000000000000),(180353755038959/100000000000000),(-763135608099/100000000000000),(125930323/5000000000000),(120449391/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((81/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((81/40)+(1/40)*x)) := (SharedCertificates.h41 (81/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(7198716129629/6250000000000),(70694755971/25000000000000),(-408817923/25000000000000),(9350009/100000000000000),(138527/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((81/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((81/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((81/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((81/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((81/40)+(1/40)*x)) := (SharedCertificates.h167 (81/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(6027472040659901/10000000000000),(70491072194289/50000000000000),(-111392483253/12500000000000),(2733440279/50000000000000),(84213613/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((81/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(82953516271/50000000000000),(-3104443/800000000000),(1680267/50000000000000),(-14323/50000000000000),(97/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((81/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(14669637014749/100000000000000),(264907385901/100000000000000),(-1668826887/100000000000000),(266697/2500000000000),(64541/20000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((81/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((81/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(200888734515053/100000000000000),(4285364287323/100000000000000),(-8964299693/100000000000000),(119375629/100000000000000),(34601/800000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((81/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(19840862668153/20000000000000),(6964723973/781250000000),(-15432798227/100000000000000),(2494793/1000000000000),(4973911/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((81/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((81/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(2543287715332031/50000000000000),(73306680908203/25000000000000),(137781/2048000),(7857/10240000),(108886719/25000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((81/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(40401/1600),(201/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((81/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(8120601/64000),(121203/64000),(603/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((81/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(129081404777581289/20000000000000),(731856793721219/1562500000000),(728431410323089/50000000000000),(3164819893753/12500000000000),(135099337247/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((81/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(7747049249/50000000000000),(-1124446269/100000000000000),(46629453/100000000000000),(-1453647/100000000000000),(14279/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((81/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(570613127269/10000000000000),(110451969/1562500000000),(-946011383/100000000000000),(10370667/50000000000000),(41027021/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((81/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((81/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((81/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel20

namespace Hf4Quad.Panel21
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(83/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((83/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (83/40) (1/40)

def c3 : Certificate := ⟨(363619047619047/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((83/40)+(1/40)*x)) := (SharedCertificates.h2 (83/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((83/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-68047619047619/25000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((83/40)+(1/40)*x)) := (SharedCertificates.h4 (83/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(6889/1600),(83/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((83/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(32576951058201/6250000000000),(3139947089947/25000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((83/40)+(1/40)*x)) := (SharedCertificates.h8 (83/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((83/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((83/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(571787/64000),(20667/64000),(249/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((83/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(8704199673032407/100000000000000),(314609626736111/100000000000000),(758095486111/20000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((83/40)+(1/40)*x)) := (SharedCertificates.h13 (83/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((83/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((83/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(47458321/2560000),(571787/640000),(20667/1280000),(83/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((83/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(5178983442460317/100000000000000),(249589563492063/100000000000000),(281915922619/6250000000000),(3623015873/10000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((83/40)+(1/40)*x)) := (SharedCertificates.h18 (83/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((83/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(3846719377929687/100000000000000),(57932520751953/25000000000000),(571787/10240000),(6889/10240000),(406250001/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((83/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(25060664391771553/100000000000000),(37741964445439/2500000000000),(9094449263961/25000000000000),(109571677879/25000000000000),(2646643527/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((83/40)+(1/40)*x)) := (SharedCertificates.h22 (83/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((83/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(79819427092041/1000000000000),(144251976672363/25000000000000),(3475951245117/20000000000000),(279192871093/100000000000000),(253500977/10000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((83/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(448086836744209/2500000000000),(323918195236777/25000000000000),(19513144291371/50000000000000),(156732082661/25000000000000),(2846185573/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((83/40)+(1/40)*x)) := (SharedCertificates.h26 (83/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((83/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(16562531121598507/100000000000000),(279367994822143/20000000000000),(2019527673413/4000000000000),(1013819113157/100000000000000),(1537917787/12500000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((83/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(122822341402727/3125000000000),(16573617153139/5000000000000),(11980928062509/100000000000000),(60145221197/25000000000000),(2919602659/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((83/40)+(1/40)*x)) := (SharedCertificates.h30 (83/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((83/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((83/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((83/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((83/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((83/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (83/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((83/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((83/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (83/40) (1/40))

def c43 : Certificate := ⟨(15129/1600),(123/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((83/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((83/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(50360550063/100000000000000),(-818870733/100000000000000),(2496557/25000000000000),(-27063/25000000000000),(1127/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((83/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-520801503890809/50000000000000),(166885860879/100000000000000),(-690043709/50000000000000),(356689/3125000000000),(23245511/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((83/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((83/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (83/40) (1/40))

def c52 : Certificate := ⟨(135833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((83/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (83/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((83/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (83/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((83/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (83/40) (1/40))

def c56 : Certificate := ⟨(717017208413/3125000000000),(-8774206757/20000000000000),(83883429/100000000000000),(-160389/100000000000000),(31/10000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((83/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1644359464627/20000000000000),(175484135137/100000000000000),(-8388343/2500000000000),(128311/20000000000000),(727/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((83/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((83/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((83/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((83/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((83/40)+(1/40)*x)) := (SharedCertificates.h61 (83/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-119161039597253/100000000000000),(-2629913291021/100000000000000),(3180834007/100000000000000),(-2549037/100000000000000),(21057/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((83/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((83/40)+(1/40)*x)) := (SharedCertificates.h61 (83/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-124902341687717/100000000000000),(-1441056376119/50000000000000),(18593467/2500000000000),(2225137/50000000000000),(57713/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((83/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((83/40)+(1/40)*x)) := (SharedCertificates.h67 (83/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-4576523671913/781250000000),(-637001736139/5000000000000),(18909947923/100000000000000),(-1074021/3125000000000),(121673/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((83/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((83/40)+(1/40)*x)) := (SharedCertificates.h67 (83/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-77961086589431/12500000000000),(-7179663317737/50000000000000),(2325449049/50000000000000),(24438301/100000000000000),(163217/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((83/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((83/40)+(1/40)*x)) := (SharedCertificates.h72 (83/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(2030025746717/250000000000),(1615076474809/10000000000000),(-57954307471/100000000000000),(121713207/100000000000000),(236121/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((83/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((83/40)+(1/40)*x)) := (SharedCertificates.h72 (83/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1860101119860373/100000000000000),(21178666582983/50000000000000),(-28756929653/100000000000000),(-146624193/100000000000000),(696983/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((83/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((83/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((83/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(117119574158497/100000000000000),(94956042531/25000000000000),(-104573607/25000000000000),(210987/100000000000000),(817/12500000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((83/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(11286475215273991/100000000000000),(7511150056407/50000000000000),(-539321511/781250000000),(19040859/12500000000000),(313229/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((83/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(886016210487/100000000000000),(-589643851/50000000000000),(1397781/20000000000000),(-14237/50000000000000),(99/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((83/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(16480797453413/100000000000000),(353356894429/100000000000000),(-31215259/5000000000000),(1470681/100000000000000),(89/312500000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((83/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((83/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((83/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (83/40) (1/40))

def c87 : Certificate := ⟨(19704433497537/100000000000000),(-19413234973/20000000000000),(14942453/3125000000000),(-2355461/100000000000000),(729/6250000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((83/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(882594417077/12500000000000),(64710783243/50000000000000),(-637544663/100000000000000),(3140613/100000000000000),(2391/10000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((83/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((83/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((83/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((83/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((83/40)+(1/40)*x)) := (SharedCertificates.h61 (83/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-50920915334019/50000000000000),(-1921559612753/100000000000000),(1692162879/20000000000000),(-36728151/100000000000000),(428779/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((83/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((83/40)+(1/40)*x)) := (SharedCertificates.h61 (83/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-4241655088257/4000000000000),(-2079383846297/100000000000000),(768539729/10000000000000),(-13279703/50000000000000),(69089/12500000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((83/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((83/40)+(1/40)*x)) := (SharedCertificates.h67 (83/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-125435048940811/25000000000000),(-9343570271421/100000000000000),(43155663503/100000000000000),(-788457/390625000000),(1888389/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((83/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((83/40)+(1/40)*x)) := (SharedCertificates.h67 (83/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-529679521211421/100000000000000),(-10368596311637/100000000000000),(38781465053/100000000000000),(-840189/625000000000),(691041/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((83/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((83/40)+(1/40)*x)) := (SharedCertificates.h72 (83/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(351989967641891/50000000000000),(3042910932479/25000000000000),(-74246181503/100000000000000),(209966701/50000000000000),(3334109/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((83/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((83/40)+(1/40)*x)) := (SharedCertificates.h72 (83/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1582171222387871/100000000000000),(3071955265047/10000000000000),(-121839970723/100000000000000),(51958471/12500000000000),(2162837/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((83/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((83/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((83/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(114620053332467/100000000000000),(17319963331/6250000000000),(-239524169/20000000000000),(5074487/100000000000000),(12699/20000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((83/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5592668119498043/50000000000000),(2866752551327/25000000000000),(-77800592127/100000000000000),(232740757/50000000000000),(2300399/20000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((83/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(55876728839/6250000000000),(-229135363/25000000000000),(715811/10000000000000),(-50919/100000000000000),(133/12500000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((83/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(14145048379237/100000000000000),(130070021533/50000000000000),(-1257586919/100000000000000),(1556553/25000000000000),(24571/20000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((83/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((83/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-79749932837861/25000000000000),(-6339092347127/100000000000000),(20203020907/100000000000000),(-88282827/100000000000000),(8105049/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((83/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(48192771084337/100000000000000),(-580635796197/100000000000000),(3497806001/50000000000000),(-42142241/50000000000000),(1027861/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((83/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-38433702572463/25000000000000),(-1202757633677/100000000000000),(12113725723/50000000000000),(-167221473/50000000000000),(9271841/50000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((83/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((83/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((83/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((83/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((83/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((83/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((83/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((83/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((83/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((83/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (83/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((83/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((83/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(5708155391/100000000000000),(-275091827/100000000000000),(4142949/50000000000000),(-199661/100000000000000),(4813/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((83/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(24289783774787/20000000000000),(-279171654041/50000000000000),(2736283423/50000000000000),(-50550603/100000000000000),(100561313/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((83/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((83/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (83/40) (1/40))

def c134 : Certificate := ⟨(33089/1600),(183/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((83/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((83/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(2710027100271/50000000000000),(-22032740653/50000000000000),(71651189/20000000000000),(-58253/2000000000000),(5969/25000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((83/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(112090108401083/100000000000000),(8213392601/2500000000000),(716511879/100000000000000),(-5825301/100000000000000),(235857/25000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((83/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((83/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (83/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((83/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (83/40) (1/40))

def c140 : Certificate := ⟨(12133268666409/50000000000000),(-19346312287/100000000000000),(-5353833/20000000000000),(39801/10000000000000),(439/781250000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((83/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1466925334363/50000000000000),(15477049829/20000000000000),(53538329/50000000000000),(-398011/25000000000000),(59587/25000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((83/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((83/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(86074797463/100000000000000),(4540735299/100000000000000),(33083853/50000000000000),(36153/50000000000000),(1671/10000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((83/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((83/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(513923478757/50000000000000),(54089168409/100000000000000),(782917897/100000000000000),(754037/100000000000000),(200111/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((83/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-102677234531701/25000000000000),(-10831552582943/100000000000000),(-14924804857/100000000000000),(111777849/50000000000000),(33373003/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((83/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-833527774171031/100000000000000),(-22303479473519/100000000000000),(-7848226617/20000000000000),(87144423/20000000000000),(6907713/10000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((83/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(34533688977593/3125000000000),(14246971297203/50000000000000),(21921120241/100000000000000),(-160283011/25000000000000),(92562037/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((83/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(622592908368491/20000000000000),(82945648727739/100000000000000),(68153506471/50000000000000),(-1660575311/100000000000000),(51336403/20000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((83/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(815800666054599/25000000000000),(45469732637503/50000000000000),(255470489959/100000000000000),(-147960943/10000000000000),(285887183/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((83/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(21190755226983/20000000000000),(159311233589/100000000000000),(140160511/50000000000000),(-1555891/50000000000000),(246703/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((83/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((83/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((83/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((83/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(13899251157223357/25000000000000),(82079712323627/100000000000000),(61365044959/50000000000000),(-847094383/50000000000000),(132273879/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((83/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(89932902561/50000000000000),(-1037273/390625000000),(-201/4000000000000),(3037/50000000000000),(879/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((83/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2934692872379/50000000000000),(77451915713/50000000000000),(27232213/12500000000000),(-393257/12500000000000),(553917/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((83/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((83/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((83/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (83/40) (1/40))

def c175 : Certificate := ⟨(229215681707/1000000000000),(-51783628877/100000000000000),(2025791/50000000000000),(1164169/100000000000000),(154121/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((83/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(554248487813/20000000000000),(69044838501/100000000000000),(-5402111/100000000000000),(-1552227/100000000000000),(6069/2500000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((83/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((83/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(479986541/625000000000),(3826799733/100000000000000),(23686243/50000000000000),(-23373/25000000000000),(3187/20000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((83/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((83/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(917317649687/100000000000000),(45603447101/100000000000000),(560568101/100000000000000),(-589671/50000000000000),(191007/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((83/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-387948520373091/100000000000000),(-9664380247571/100000000000000),(100408439/12500000000000),(108824719/50000000000000),(16995637/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((83/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-98337359622063/12500000000000),(-4967059154133/25000000000000),(-1023389351/20000000000000),(44775369/10000000000000),(2808151/4000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((83/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(261281751473401/25000000000000),(3186061356097/12500000000000),(-7948554637/50000000000000),(-287723693/50000000000000),(94212941/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((83/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1469383782073851/50000000000000),(36962517277439/50000000000000),(11429264433/100000000000000),(-837180593/50000000000000),(260965377/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((83/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(122907412354581/4000000000000),(80652498924577/100000000000000),(96726579171/100000000000000),(-451519161/25000000000000),(72239553/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((83/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(10561928272469/10000000000000),(28383295347/20000000000000),(4571033/12500000000000),(-1598973/50000000000000),(100291/20000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((83/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((83/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((83/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((83/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(2216982909201463/4000000000000),(73198639709259/100000000000000),(858955191/50000000000000),(-834330613/50000000000000),(33566597/12500000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((83/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(90212693643/50000000000000),(-238285877/100000000000000),(309109/100000000000000),(5031/100000000000000),(223/25000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((83/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(2771952184299/50000000000000),(34548952101/25000000000000),(-8166263/100000000000000),(-96413/3125000000000),(139709/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((83/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((83/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(1732664681327/12500000000000),(292241002217/100000000000000),(-757234307/100000000000000),(191497/12500000000000),(6251171/25000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((83/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(835019123531/12500000000000),(6035526627/10000000000000),(-1092104079/100000000000000),(6948091/50000000000000),(790739/6250000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((83/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((83/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((83/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((83/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((83/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((83/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (83/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((83/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((83/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((83/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (83/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((83/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(37407133867/100000000000000),(-61157879/50000000000000),(2052869/100000000000000),(-6059/50000000000000),(27/20000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((83/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(449323971254003/100000000000000),(-705386918561/50000000000000),(-4756956647/100000000000000),(-9358243/20000000000000),(1627053/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((83/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((83/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((83/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((83/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (83/40) (1/40))

def c223 : Certificate := ⟨(26569/1600),(163/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((83/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2663515681/2560000),(14055327/640000),(207827/1280000),(303/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((83/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((83/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(117507950147/100000000000000),(-1910698377/100000000000000),(23301199/100000000000000),(-63147/25000000000000),(2629/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((83/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(7641217477019/6250000000000),(296342884543/50000000000000),(1360858001/100000000000000),(-1134219/20000000000000),(553873/10000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((83/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((83/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (83/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((83/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (83/40) (1/40))

def c231 : Certificate := ⟨(2960265098343/12500000000000),(-33240357291/100000000000000),(-7416599/25000000000000),(233413/50000000000000),(156261/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((83/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(2635758426511/50000000000000),(132961429159/100000000000000),(59332791/50000000000000),(-933653/50000000000000),(694607/50000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((83/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((83/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(69472224829/25000000000000),(3504542073/25000000000000),(2957787/1562500000000),(3709/3125000000000),(30999/20000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((83/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((83/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(3305368871471/100000000000000),(166001109191/100000000000000),(1106842797/50000000000000),(885463/100000000000000),(1852379/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((83/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-368919058172983/50000000000000),(-18601454440123/100000000000000),(-16271846889/100000000000000),(26454813/10000000000000),(194547239/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((83/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-757459989748679/50000000000000),(-9797704768653/25000000000000),(-29846227837/50000000000000),(50686027/10000000000000),(410683623/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((83/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(1949674726384469/100000000000000),(5888742542313/12500000000000),(-11366810543/100000000000000),(-15795587/2000000000000),(537879633/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((83/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(5637870127453567/100000000000000),(28937044888299/20000000000000),(188951300577/100000000000000),(-998960617/50000000000000),(303485749/20000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((83/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1225899048702703/20000000000000),(169856097988663/100000000000000),(135662891901/25000000000000),(-1536017557/100000000000000),(448411463/25000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((83/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(1385261532567/1250000000000),(27994102661/10000000000000),(106657383/25000000000000),(-903981/25000000000000),(2933423/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((83/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((83/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((83/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((83/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(726049715869643/1250000000000),(70915223800919/50000000000000),(9072765091/6250000000000),(-2122391983/100000000000000),(1592055431/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((83/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(86082259429/50000000000000),(-420394263/100000000000000),(477/80000000000),(1177/20000000000000),(597/12500000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((83/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(10552815994419/100000000000000),(133331943749/50000000000000),(64183821/25000000000000),(-1776133/50000000000000),(341617/10000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((83/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((83/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((83/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (83/40) (1/40))

def c259 : Certificate := ⟨(1071172012961/5000000000000),(-8160639251/10000000000000),(61740279/50000000000000),(256059/25000000000000),(38823/5000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((83/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(4768746321039/100000000000000),(21761704669/20000000000000),(-32928149/20000000000000),(-27313/2000000000000),(1380951/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((83/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((83/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(28426176843/12500000000000),(10377604907/100000000000000),(25672587/25000000000000),(-61067/12500000000000),(68713/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((83/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((83/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(2707223820729/100000000000000),(123046613927/100000000000000),(1200655471/100000000000000),(-5998927/100000000000000),(1644563/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((83/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-667495384309107/100000000000000),(-15224379797163/100000000000000),(23236388523/100000000000000),(38394357/20000000000000),(96693941/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((83/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-683540065736633/50000000000000),(-31918690459141/100000000000000),(634820791/2000000000000),(451001001/100000000000000),(50738341/12500000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((83/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(221346843765591/12500000000000),(38881660406831/100000000000000),(-2948516313/3125000000000),(-398510501/100000000000000),(533903209/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((83/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(509162739284141/10000000000000),(29507467779959/25000000000000),(-137981070873/100000000000000),(-821898841/50000000000000),(1501843853/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((83/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(5492797225045227/100000000000000),(136586288946519/100000000000000),(27027308233/50000000000000),(-604674513/25000000000000),(1746755393/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((83/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(54882451028411/50000000000000),(227994651597/100000000000000),(-113295571/50000000000000),(-804959/25000000000000),(22651/781250000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((83/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((83/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((83/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((83/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(287739723138013/500000000000),(23189143120299/20000000000000),(-161757211707/100000000000000),(-1585534807/100000000000000),(1568311261/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((83/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(34753630437/20000000000000),(-350102387/100000000000000),(596903/50000000000000),(699/50000000000000),(2383/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((83/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(954473224123/10000000000000),(109056528121/50000000000000),(-318688807/100000000000000),(-2684809/100000000000000),(415099/12500000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((83/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((83/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(45151550928553/50000000000000),(473672015731/25000000000000),(-4036754989/50000000000000),(-29807583/50000000000000),(31172153/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((83/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(870391343201/2000000000000),(97192636617/25000000000000),(-8574830671/100000000000000),(18645253/25000000000000),(17971937/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((83/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((83/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((83/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((83/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((83/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((83/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (83/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((83/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1035359554651009077/100000000000000),(338547156750363/10000000000000),(-45749615777077/100000000000000),0,(13411/10000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((83/40)+(1/40)*x)) := (SharedCertificates.h297 (83/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9658480433/100000000000000),(-31581793/100000000000000),(4141/781250000000),(-3129/100000000000000),(9/25000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((83/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(126484139647919/20000000000000),(257961759883/25000000000000),(1992584271/25000000000000),(2438993/12500000000000),(4289449/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((83/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((83/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (83/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((83/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (83/40) (1/40))

def c307 : Certificate := ⟨(2953845709717177/100000000000000),(11091229182759/50000000000000),0,0,(1057/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((83/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (83/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((83/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (83/40) (1/40))

def c311 : Certificate := ⟨(530288572570641/25000000000000),(2817541634481/100000000000000),0,0,(1057/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((83/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (83/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(58930178051/1250000000000),(-313109199/5000000000000),(1663619/20000000000000),(-11049/100000000000000),(19/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((83/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(34814130721763/25000000000000),(860797724043/100000000000000),(-571701331/50000000000000),(1518787/100000000000000),(767/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((83/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((83/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (83/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((83/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (83/40) (1/40))

def c316 : Certificate := ⟨(5691435117613/25000000000000),(-22306666563/50000000000000),(146687551/100000000000000),(-241153/50000000000000),(1649/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((83/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(8937038118189/100000000000000),(178453332501/100000000000000),(-586750207/100000000000000),(1929219/100000000000000),(7879/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((83/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((83/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(798706503259/100000000000000),(31896884697/100000000000000),(213579739/100000000000000),(-1749321/100000000000000),(1179/10000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((83/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((83/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(944171662981/10000000000000),(93552676533/25000000000000),(2420312179/100000000000000),(-4219593/20000000000000),(18387/12500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((83/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1250341526732243/100000000000000),(-155832338367/625000000000),(16594745077/20000000000000),(-269670597/100000000000000),(1160561/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((83/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-2614114171944527/100000000000000),(-5442649649923/10000000000000),(134547752773/100000000000000),(-147019441/50000000000000),(1932347/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((83/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(3207135295503101/100000000000000),(29587721209569/50000000000000),(-147830911097/50000000000000),(122549149/10000000000000),(5552573/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((83/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1934102585591891/20000000000000),(24798471348037/12500000000000),(-555728451067/100000000000000),(1322244849/100000000000000),(7056387/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((83/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(11112404877290713/100000000000000),(257350685699453/100000000000000),(-120843377129/100000000000000),(-335272689/20000000000000),(31333579/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((83/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(118672782739637/100000000000000),(388803549699/100000000000000),(-38396827/4000000000000),(2109117/100000000000000),(6887/25000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((83/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((83/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((83/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((83/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(31002319529903677/50000000000000),(47804998204803/25000000000000),(-124089719191/20000000000000),(795390189/50000000000000),(5350263/25000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((83/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(161278255169/100000000000000),(-12434403/2500000000000),(1573859/50000000000000),(-18823/100000000000000),(161/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((83/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(17921892693409/100000000000000),(22486265459/6250000000000),(-1125107777/100000000000000),(1953211/50000000000000),(22587/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((83/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((83/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((83/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (83/40) (1/40))

def c344 : Certificate := ⟨(4828402732251/25000000000000),(-96327285363/100000000000000),(608387679/100000000000000),(-3842479/100000000000000),(767/3125000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((83/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(379092604733/5000000000000),(64218190241/50000000000000),(-405591787/50000000000000),(1024661/20000000000000),(51993/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((83/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((83/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(574844811853/100000000000000),(19475712807/100000000000000),(1048839/2500000000000),(-1306827/100000000000000),(5569/20000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((83/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((83/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((83/40)+(1/40)*x)) := (SharedCertificates.h144 (83/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(3405484987709/50000000000000),(45855738893/20000000000000),(228189649/50000000000000),(-15334463/100000000000000),(166339/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((83/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((83/40)+(1/40)*x)) := (SharedCertificates.h148 (83/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1060942895582653/100000000000000),(-17954961932669/100000000000000),(2276790603/2000000000000),(-89918763/12500000000000),(1828263/25000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((83/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((83/40)+(1/40)*x)) := (SharedCertificates.h151 (83/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-55083942691417/2500000000000),(-7737228369283/20000000000000),(55327009199/25000000000000),(-4888913/390625000000),(18461917/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((83/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((83/40)+(1/40)*x)) := (SharedCertificates.h154 (83/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(2751957733933279/100000000000000),(43684967540859/100000000000000),(-163670116251/50000000000000),(236275179/10000000000000),(12860901/50000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((83/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((83/40)+(1/40)*x)) := (SharedCertificates.h157 (83/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(4084797032243689/50000000000000),(70852422019253/50000000000000),(-105347155369/12500000000000),(1231203139/25000000000000),(65993933/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((83/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((83/40)+(1/40)*x)) := (SharedCertificates.h160 (83/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(919975777680011/10000000000000),(44332841177759/25000000000000),(-374039332861/50000000000000),(249952269/10000000000000),(114423989/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((83/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((83/40)+(1/40)*x)) := (SharedCertificates.h41 (83/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(115738549001173/100000000000000),(276348473771/100000000000000),(-395103397/25000000000000),(8939783/100000000000000),(131831/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((83/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((83/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((83/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((83/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((83/40)+(1/40)*x)) := (SharedCertificates.h167 (83/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(60553163356677961/100000000000000),(137482161813287/100000000000000),(-429552112161/50000000000000),(5214072103/100000000000000),(39981203/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((83/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(82572069283/50000000000000),(-46868677/12500000000000),(1597149/50000000000000),(-26793/100000000000000),(181/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((83/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(3038572146131/20000000000000),(258357916601/100000000000000),(-1606443307/100000000000000),(2533083/25000000000000),(30441/10000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((83/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((83/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(41884910964957/20000000000000),(6642073899/156250000000),(-8257296621/100000000000000),(3635237/3125000000000),(32337/781250000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((83/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(1009274963011/1000000000000),(33305829163/4000000000000),(-7005648157/50000000000000),(44974457/20000000000000),(4533311/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((83/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((83/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(5700560041992187/100000000000000),(80267950439453/25000000000000),(737123/10240000),(8217/10240000),(445312501/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((83/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(41209/1600),(203/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((83/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(8365427/64000),(123627/64000),(609/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((83/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(745119045162540233/100000000000000),(52978841494919001/100000000000000),(807679946895843/50000000000000),(5507608258081/20000000000000),(11538738347/4000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((83/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(13420674273/100000000000000),(-59639109/6250000000000),(96879/250000000000),(-591299/50000000000000),(11357/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((83/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5716645566657/100000000000000),(3522967719/100000000000000),(-51848249/6250000000000),(4534127/25000000000000),(9408649/25000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((83/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((83/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((83/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel21
