import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel22
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(17/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((17/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (17/8) (1/40)

def c3 : Certificate := ⟨(46547619047619/12500000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((17/8)+(1/40)*x)) := (SharedCertificates.h2 (17/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((17/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-280952380952381/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((17/8)+(1/40)*x)) := (SharedCertificates.h4 (17/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(289/64),(17/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((17/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(546653439153439/100000000000000),(12862433862433/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((17/8)+(1/40)*x)) := (SharedCertificates.h8 (17/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((17/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((17/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(4913/512),(867/2560),(51/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((17/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(9348702618634259/100000000000000),(82488552517361/25000000000000),(3881814236111/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((17/8)+(1/40)*x)) := (SharedCertificates.h13 (17/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((17/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((17/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(83521/4096),(4913/5120),(867/51200),(17/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((17/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(113929935515873/2000000000000),(8377201140873/3125000000000),(295665922619/6250000000000),(37103174603/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((17/8)+(1/40)*x)) := (SharedCertificates.h18 (17/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((17/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1083264923095703/25000000000000),(63721466064453/25000000000000),(4913/81920),(289/409600),(208007813/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((17/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(28229081477412467/100000000000000),(1660534204553671/100000000000000),(39071393048321/100000000000000),(459663447627/100000000000000),(1355132383/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((17/8)+(1/40)*x)) := (SharedCertificates.h22 (17/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((17/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(368310073852539/4000000000000),(32497947692871/5000000000000),(3823287963867/20000000000000),(9370803833/3125000000000),(1329174807/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((17/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(2584503891253597/12500000000000),(182435568794371/12500000000000),(10731504046727/25000000000000),(673349273519/100000000000000),(2984665547/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((17/8)+(1/40)*x)) := (SharedCertificates.h26 (17/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((17/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(9783236336708067/50000000000000),(805678286552427/50000000000000),(28435704231261/50000000000000),(1115125656127/100000000000000),(6606047369/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((17/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(4643155023294781/100000000000000),(95594368126657/25000000000000),(13495675500233/100000000000000),(264621088239/100000000000000),(627050211/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((17/8)+(1/40)*x)) := (SharedCertificates.h30 (17/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((17/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((17/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((17/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((17/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((17/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (17/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((17/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((17/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (17/8) (1/40))

def c43 : Certificate := ⟨(625/64),(5/32),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((17/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((17/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(48761904761/100000000000000),(-780190477/100000000000000),(1872457/20000000000000),(-19973/20000000000000),(41/4000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((17/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-1041274666647347/100000000000000),(40374861541/25000000000000),(-656912617/50000000000000),(213979/2000000000000),(43608829/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((17/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((17/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (17/8) (1/40))

def c52 : Certificate := ⟨(68749999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((17/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (17/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((17/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (17/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((17/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (17/8) (1/40))

def c56 : Certificate := ⟨(11428571428571/50000000000000),(-21768707483/50000000000000),(82928409/100000000000000),(-157959/100000000000000),(19/6250000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((17/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(8571428571427/100000000000000),(174149659863/100000000000000),(-331713639/100000000000000),(126367/20000000000000),(719/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((17/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((17/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((17/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((17/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((17/8)+(1/40)*x)) := (SharedCertificates.h61 (17/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-124408163265283/100000000000000),(-2617220602513/100000000000000),(25323967/800000000000),(-32043/1250000000000),(1659/4000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((17/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((17/8)+(1/40)*x)) := (SharedCertificates.h61 (17/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-130663556851287/100000000000000),(-359885603219/12500000000000),(48132327/6250000000000),(434291/10000000000000),(28559/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((17/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((17/8)+(1/40)*x)) := (SharedCertificates.h67 (17/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-152799933361071/25000000000000),(-6332402514791/50000000000000),(9352738593/50000000000000),(-16895153/50000000000000),(12077/10000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((17/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((17/8)+(1/40)*x)) := (SharedCertificates.h67 (17/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-32619427429041/5000000000000),(-3585108291027/25000000000000),(4794999341/100000000000000),(11799937/50000000000000),(321343/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((17/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((17/8)+(1/40)*x)) := (SharedCertificates.h72 (17/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(42204049077503/5000000000000),(15920401861781/100000000000000),(-11445737187/20000000000000),(120163149/100000000000000),(47077/20000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((17/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((17/8)+(1/40)*x)) := (SharedCertificates.h72 (17/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(486174899209199/25000000000000),(21120284317819/50000000000000),(-29619708163/100000000000000),(-35249067/25000000000000),(1368793/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((17/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((17/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((17/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(29469387755101/25000000000000),(378153547131/100000000000000),(-417011433/100000000000000),(54157/25000000000000),(3217/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((17/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5658122448979489/50000000000000),(2949597667621/20000000000000),(-34062251891/50000000000000),(15055731/10000000000000),(616743/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((17/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(883685364727/100000000000000),(-23033403/2000000000000),(1705191/25000000000000),(-1379/5000000000000),(3/1562500000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((17/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(17185025725151/100000000000000),(175438599123/50000000000000),(-615573677/100000000000000),(1439939/100000000000000),(13989/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((17/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((17/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((17/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (17/8) (1/40))

def c87 : Certificate := ⟨(19512195121951/100000000000000),(-4759071981/5000000000000),(92859941/20000000000000),(-2264877/100000000000000),(5553/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((17/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(7317073170731/100000000000000),(63454293079/50000000000000),(-24762651/4000000000000),(603967/20000000000000),(4627/20000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((17/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((17/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((17/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((17/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((17/8)+(1/40)*x)) := (SharedCertificates.h61 (17/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-13206424747173/12500000000000),(-944076067761/50000000000000),(8244150883/100000000000000),(-17750737/50000000000000),(413769/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((17/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((17/8)+(1/40)*x)) := (SharedCertificates.h61 (17/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-5508480724307/5000000000000),(-2048958374973/100000000000000),(1881995849/25000000000000),(-25914409/100000000000000),(266579/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((17/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((17/8)+(1/40)*x)) := (SharedCertificates.h67 (17/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-260128156627517/50000000000000),(-1834667902943/20000000000000),(41967186127/100000000000000),(-388747/200000000000),(913431/50000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((17/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((17/8)+(1/40)*x)) := (SharedCertificates.h67 (17/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-550262657067389/100000000000000),(-10215070927101/100000000000000),(37984384863/100000000000000),(-13127277/10000000000000),(1331963/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((17/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((17/8)+(1/40)*x)) := (SharedCertificates.h72 (17/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(29121182467117/4000000000000),(2969906693543/25000000000000),(-17944981299/25000000000000),(40230383/10000000000000),(100461/3125000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((17/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((17/8)+(1/40)*x)) := (SharedCertificates.h72 (17/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(1643126277318561/100000000000000),(30237149107207/100000000000000),(-3730304227/3125000000000),(407734361/100000000000000),(8316071/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((17/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((17/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((17/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(2879238548483/2500000000000),(136194580267/50000000000000),(-1167669723/100000000000000),(49103/1000000000000),(15313/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((17/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(10945276113231/97656250000),(5580655971909/50000000000000),(-18767172749/25000000000000),(445328329/100000000000000),(11057319/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((17/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(871311337/97656250000),(-888509119/100000000000000),(343037/5000000000000),(-9647/20000000000000),(203/20000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((17/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(7330173714177/50000000000000),(255183414341/100000000000000),(-1220973211/100000000000000),(149511/2500000000000),(7359/6250000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((17/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((17/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-331597803146763/100000000000000),(-50074604177/800000000000),(1968388947/10000000000000),(-84787997/100000000000000),(315427/2000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((17/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(47058823529411/100000000000000),(-276816608997/50000000000000),(814166497/12500000000000),(-19156859/25000000000000),(182447/20000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((17/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-156046025010239/100000000000000),(-110972936323/10000000000000),(11159323189/50000000000000),(-302472541/100000000000000),(17160923/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((17/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((17/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((17/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((17/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((17/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((17/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((17/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((17/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((17/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((17/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (17/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((17/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((17/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(51895829/1000000000000),(-122107833/50000000000000),(7182813/100000000000000),(-10563/6250000000000),(3971/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((17/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(120353725301953/100000000000000),(-537045515483/100000000000000),(1294922531/25000000000000),(-47153317/100000000000000),(90451687/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((17/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((17/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (17/8) (1/40))

def c134 : Certificate := ⟨(1353/64),(37/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((17/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((17/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(5333333333333/100000000000000),(-42666666667/100000000000000),(341333333/100000000000000),(-2730667/100000000000000),(22023/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((17/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(14093749999999/12500000000000),(165666666663/50000000000000),(682666659/100000000000000),(-5461341/100000000000000),(890529/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((17/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((17/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (17/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((17/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (17/8) (1/40))

def c140 : Certificate := ⟨(12113870381587/50000000000000),(-9724358699/50000000000000),(-978361/4000000000000),(372373/100000000000000),(423/800000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((17/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1544518473651/50000000000000),(77794869591/100000000000000),(97836099/100000000000000),(-1489493/100000000000000),(224981/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((17/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((17/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(95421492617/100000000000000),(4806224529/100000000000000),(66564803/100000000000000),(301/500000000000),(16479/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((17/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((17/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(569581350539/50000000000000),(57229296193/100000000000000),(787000507/100000000000000),(12171/2000000000000),(197293/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((17/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-216214991732777/50000000000000),(-10888627698499/100000000000000),(-2725421431/20000000000000),(209199087/100000000000000),(787539/2500000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((17/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-878288267205023/100000000000000),(-22455325559851/100000000000000),(-917723011/2500000000000),(102176773/25000000000000),(65301739/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((17/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(72634285977093/6250000000000),(28574108277249/100000000000000),(3640914357/20000000000000),(-598274721/100000000000000),(87377831/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((17/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(1639693996775481/50000000000000),(10433921225183/12500000000000),(126656441/100000000000),(-389410171/25000000000000),(121275141/50000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((17/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(3446091808199449/100000000000000),(45971963601827/50000000000000),(77138303/31250000000),(-698748831/50000000000000),(271394187/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((17/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(106273495387221/100000000000000),(160395963711/100000000000000),(262237001/100000000000000),(-1459393/50000000000000),(466441/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((17/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((17/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((17/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((17/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(697020520441141/1250000000000),(82550730515149/100000000000000),(22576787407/20000000000000),(-1589239823/100000000000000),(50063027/20000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((17/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(179334748883/100000000000000),(-26549101/10000000000000),(29993/100000000000000),(1401/25000000000000),(33/4000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((17/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(386252505657/6250000000000),(19467293377/12500000000000),(199605227/100000000000000),(-2940849/100000000000000),(525569/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((17/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((17/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((17/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (17/8) (1/40))

def c175 : Certificate := ⟨(22818026240731/100000000000000),(-51753834759/100000000000000),(10751841/100000000000000),(26763/2500000000000),(144163/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((17/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(2909298345691/100000000000000),(6900511301/10000000000000),(-14335789/100000000000000),(-1427361/100000000000000),(114489/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((17/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((17/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(42320084321/50000000000000),(2007564611/50000000000000),(23391457/50000000000000),(-51419/50000000000000),(1561/10000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((17/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((17/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(1010757153651/100000000000000),(47831114399/100000000000000),(553155837/100000000000000),(-1289071/100000000000000),(37423/20000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((17/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-40727236245559/10000000000000),(-1207328349683/12500000000000),(513991107/25000000000000),(100076729/50000000000000),(641239/2000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((17/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-413226152448429/50000000000000),(-19883468666407/100000000000000),(-633181393/25000000000000),(414100749/100000000000000),(33149591/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((17/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(219207179971349/20000000000000),(3177275592113/12500000000000),(-9597547437/50000000000000),(-524587359/100000000000000),(88854227/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((17/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(3086650217278261/100000000000000),(73951180881741/100000000000000),(885857241/50000000000000),(-386631187/25000000000000),(615909/250000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((17/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(1617181495196319/50000000000000),(16203636513167/20000000000000),(5389106939/6250000000000),(-847794097/50000000000000),(273822479/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((17/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(13237904607503/12500000000000),(71012677621/50000000000000),(2263917/12500000000000),(-73939/2500000000000),(236783/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((17/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((17/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((17/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((17/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(27785481898927883/50000000000000),(73186017374273/100000000000000),(-3949610369/50000000000000),(-1538783003/100000000000000),(50759509/20000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((17/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(179950091137/100000000000000),(-11849561/5000000000000),(84423/25000000000000),(563/12500000000000),(419/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((17/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(363764946807/6250000000000),(69063568527/50000000000000),(-25920549/100000000000000),(-2836293/100000000000000),(529141/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((17/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((17/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(14442783111283/100000000000000),(144615547977/50000000000000),(-149515629/20000000000000),(83851/5000000000000),(11807441/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((17/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(3398301908537/50000000000000),(5614870613/10000000000000),(-506187247/50000000000000),(12699473/100000000000000),(364371/3125000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((17/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((17/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((17/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((17/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((17/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((17/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (17/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((17/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((17/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((17/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (17/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((17/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(9292654737/25000000000000),(-114245591/100000000000000),(991609/50000000000000),(-1389/12500000000000),(1/800000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((17/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(111620755141699/25000000000000),(-715182499813/50000000000000),(-2519590241/50000000000000),(-47318629/100000000000000),(760617/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((17/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((17/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((17/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((17/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (17/8) (1/40))

def c223 : Certificate := ⟨(1089/64),(33/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((17/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(4444209/4096),(115797/5120),(8459/51200),(61/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((17/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((17/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(113777777777/100000000000000),(-364088889/20000000000000),(21845333/100000000000000),(-233017/100000000000000),(1193/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((17/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(30862562499789/25000000000000),(299031333023/50000000000000),(82997421/6250000000000),(-5301263/100000000000000),(5244997/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((17/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((17/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (17/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((17/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (17/8) (1/40))

def c231 : Certificate := ⟨(23615525082391/100000000000000),(-8338384433/25000000000000),(-26952251/100000000000000),(54789/12500000000000),(36787/12500000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((17/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(2768949835217/50000000000000),(66707075463/50000000000000),(107809001/100000000000000),(-1753249/100000000000000),(1315203/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((17/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((17/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(306683327597/100000000000000),(115442841/781250000000),(37986813/20000000000000),(46739/50000000000000),(123/80000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((17/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((17/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(3646232301187/100000000000000),(17486525003/10000000000000),(88723297/4000000000000),(583477/100000000000000),(28703/1562500000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((17/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-77510402917417/10000000000000),(-1866343267767/10000000000000),(-7366599503/50000000000000),(248571001/100000000000000),(92093561/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((17/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-796768195599339/50000000000000),(-7884724579069/20000000000000),(-56737722211/100000000000000),(478487803/100000000000000),(19489311/5000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((17/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(510960731640163/25000000000000),(47055204378101/100000000000000),(-15950280161/100000000000000),(-147752479/20000000000000),(12732263/2500000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((17/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(592798062464989/10000000000000),(18177188020901/12500000000000),(88648944283/50000000000000),(-1888207211/100000000000000),(1439175289/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((17/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(1294273178581491/20000000000000),(172008539475227/100000000000000),(533633459769/100000000000000),(-22988793/1562500000000),(1713731781/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((17/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(22276496533693/20000000000000),(563209971/200000000000),(405552067/100000000000000),(-170651/5000000000000),(696039/25000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((17/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((17/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((17/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((17/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(58368202077118667/100000000000000),(142386101504823/100000000000000),(16597003351/12500000000000),(-1004347349/50000000000000),(1513372653/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((17/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(171326161233/100000000000000),(-417940991/100000000000000),(629811/100000000000000),(531/10000000000000),(281/6250000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((17/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(11087142763659/100000000000000),(267649136931/100000000000000),(236116901/100000000000000),(-3324007/100000000000000),(163031/5000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((17/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((17/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((17/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (17/8) (1/40))

def c259 : Certificate := ⟨(4252145872013/20000000000000),(-2534394907/3125000000000),(25857161/20000000000000),(912633/100000000000000),(724061/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((17/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(4985694186579/100000000000000),(54067091349/50000000000000),(-6895243/4000000000000),(-608423/50000000000000),(1305001/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((17/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((17/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(12428573261/5000000000000),(269561983/2500000000000),(24935307/25000000000000),(-494143/100000000000000),(1057/781250000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((17/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((17/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(1479035778229/50000000000000),(63888503753/50000000000000),(1164487039/100000000000000),(-6052929/100000000000000),(1618803/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((17/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-139569941143887/20000000000000),(-118197002503/781250000000),(24324479729/100000000000000),(171059609/100000000000000),(36551159/20000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((17/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-1430787024451233/100000000000000),(-31786481689741/100000000000000),(34322551579/100000000000000),(6408127/1562500000000),(192171153/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((17/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(1848157596332523/100000000000000),(38499713713967/100000000000000),(-96561142547/100000000000000),(-338719611/100000000000000),(126129879/25000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((17/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(2663561190873559/50000000000000),(117458859933151/100000000000000),(-36842223797/25000000000000),(-1487846879/100000000000000),(2220693/156250000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((17/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(5766166957705379/100000000000000),(136774051433167/100000000000000),(39965601103/100000000000000),(-1139679517/50000000000000),(207841501/12500000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((17/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(55109979919189/50000000000000),(56762711179/25000000000000),(-122510461/50000000000000),(-585567/20000000000000),(1372649/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((17/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((17/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((17/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((17/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(57779176673870877/100000000000000),(115280312659809/100000000000000),(-42696328741/25000000000000),(-1426271803/100000000000000),(1486827057/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((17/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(86536366349/50000000000000),(-172656309/50000000000000),(150067/12500000000000),(107/12500000000000),(7/156250000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((17/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(9979662725629/100000000000000),(216807286357/100000000000000),(-33390359/10000000000000),(-298947/12500000000000),(1578751/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((17/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((17/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(1469682960711/1562500000000),(232710432471/12500000000000),(-8427690431/100000000000000),(-58501559/100000000000000),(1846659/6250000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((17/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(44263392699059/100000000000000),(88835134387/25000000000000),(-8146448881/100000000000000),(17077607/25000000000000),(1037449/6250000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((17/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((17/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((17/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((17/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((17/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((17/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (17/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((17/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(208389499864581607/20000000000000),(1601236552197663/50000000000000),(-45749615777077/100000000000000),0,(16867/12500000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((17/8)+(1/40)*x)) := (SharedCertificates.h297 (17/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9597412543/100000000000000),(-5899617/20000000000000),(8001/1562500000000),(-287/10000000000000),(7/20000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((17/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(158629108681909/25000000000000),(265993046711/25000000000000),(8094436121/100000000000000),(680463/3125000000000),(2055711/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((17/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((17/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (17/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((17/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (17/8) (1/40))

def c307 : Certificate := ⟨(1499105313224107/50000000000000),(11091229182759/50000000000000),0,0,(53/5000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((17/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (17/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((17/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (17/8) (1/40))

def c311 : Certificate := ⟨(2126789373551527/100000000000000),(2817541634481/100000000000000),0,0,(1059/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((17/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (17/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(940384612069/20000000000000),(-6229043717/100000000000000),(1031519/12500000000000),(-10933/100000000000000),(19/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((17/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(70486778421341/50000000000000),(85624227459/10000000000000),(-1134338131/100000000000000),(300547/20000000000000),(763/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((17/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((17/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (17/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((17/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (17/8) (1/40))

def c316 : Certificate := ⟨(2267709672117/10000000000000),(-44032320253/100000000000000),(143831367/100000000000000),(-7341/1562500000000),(1597/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((17/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(4645806557659/50000000000000),(11008080063/6250000000000),(-575325469/100000000000000),(1879293/100000000000000),(7687/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((17/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((17/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(863340742847/100000000000000),(8182625687/25000000000000),(101650601/50000000000000),(-8387/500000000000),(11409/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((17/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((17/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(10199652350779/100000000000000),(383642457917/100000000000000),(2296472541/100000000000000),(-20189067/100000000000000),(71007/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((17/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1299878123908979/100000000000000),(-12302244096917/50000000000000),(20343992627/25000000000000),(-262947661/100000000000000),(282649/25000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((17/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-2722431318533317/100000000000000),(-53891818527837/100000000000000),(132795093429/100000000000000),(-226703/78125000000),(3757973/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((17/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(3324313263949063/100000000000000),(29003677601197/50000000000000),(-18026120687/6250000000000),(297336839/25000000000000),(2701123/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((17/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(10065076098311247/100000000000000),(196180653132481/100000000000000),(-547848103981/100000000000000),(652260637/50000000000000),(684971/5000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((17/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(372051508247/3200000000),(10273901279219/4000000000000),(-130650339871/100000000000000),(-99575753/6250000000000),(7637897/25000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((17/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(119446566973483/100000000000000),(96247266191/25000000000000),(-118418717/12500000000000),(1040593/50000000000000),(26783/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((17/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((17/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((17/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((17/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(62384609934315131/100000000000000),(94378600879931/50000000000000),(-610968497973/100000000000000),(313844407/20000000000000),(2073027/10000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((17/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(160295944953/100000000000000),(-242503833/50000000000000),(3037359/100000000000000),(-17973/100000000000000),(153/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((17/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(18636983776763/100000000000000),(355326230461/100000000000000),(-1102015543/100000000000000),(189577/5000000000000),(13717/12500000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((17/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((17/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((17/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (17/8) (1/40))

def c344 : Certificate := ⟨(1912335955261/10000000000000),(-5871192493/6250000000000),(117180643/20000000000000),(-3654309/100000000000000),(4611/20000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((17/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(7835520596519/100000000000000),(25050421303/20000000000000),(-781204287/100000000000000),(487241/10000000000000),(49631/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((17/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((17/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(76744228773/12500000000000),(19628309207/100000000000000),(4307257/12500000000000),(-1193393/100000000000000),(2629/10000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((17/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((17/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((17/8)+(1/40)*x)) := (SharedCertificates.h144 (17/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(7271233004573/100000000000000),(57731442463/25000000000000),(368519461/100000000000000),(-13973173/100000000000000),(62739/20000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((17/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((17/8)+(1/40)*x)) := (SharedCertificates.h148 (17/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-548201572276483/50000000000000),(-17508093303333/100000000000000),(21925982361/20000000000000),(-684220411/100000000000000),(174477/2500000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((17/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((17/8)+(1/40)*x)) := (SharedCertificates.h151 (17/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-45597093224753/2000000000000),(-3781570811549/10000000000000),(106981583687/50000000000000),(-1197220539/100000000000000),(8791223/50000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((17/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((17/8)+(1/40)*x)) := (SharedCertificates.h154 (17/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(8868865462837/312500000000),(8480687484297/20000000000000),(-9798536597/3125000000000),(558599207/25000000000000),(24428541/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((17/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((17/8)+(1/40)*x)) := (SharedCertificates.h157 (17/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(8449671595950759/100000000000000),(138391942974721/100000000000000),(-813892692353/100000000000000),(147043703/3125000000000),(3927139/6250000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((17/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((17/8)+(1/40)*x)) := (SharedCertificates.h160 (17/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(1193931017852853/12500000000000),(8718447678361/5000000000000),(-18328767657/2500000000000),(2475737657/100000000000000),(1087861/1000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((17/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((17/8)+(1/40)*x)) := (SharedCertificates.h41 (17/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(58142497511611/50000000000000),(270132522237/100000000000000),(-763975259/50000000000000),(8551427/100000000000000),(7847/6250000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((17/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((17/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((17/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((17/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((17/8)+(1/40)*x)) := (SharedCertificates.h167 (17/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(60824732490216131/100000000000000),(134107344958749/100000000000000),(-414271506817/50000000000000),(4975249213/100000000000000),(4749471/6250000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((17/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(16440680609/10000000000000),(-362486761/100000000000000),(607747/20000000000000),(-12543/50000000000000),(67/20000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((17/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(15703230826957/100000000000000),(25205169237/10000000000000),(-309434167/20000000000000),(9630389/100000000000000),(287091/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((17/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((17/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(217894305381343/100000000000000),(1054820768389/25000000000000),(-7567544053/100000000000000),(4544763/4000000000000),(4020279/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((17/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(51269248325021/50000000000000),(389604860541/50000000000000),(-1591046299/12500000000000),(203213331/100000000000000),(2077259/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((17/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((17/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(24891197681427/390625000000),(87710723876953/25000000000000),(31501/409600),(1717/2048000),(227539063/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((17/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1681/64),(41/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((17/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(68921/512),(5043/2560),(123/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((17/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(857763117700815133/100000000000000),(11956011823654161/20000000000000),(446904314756393/25000000000000),(29906502151489/100000000000000),(153812604829/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((17/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(182159849/1562500000000),(-101562087/12500000000000),(16164513/50000000000000),(-966299/100000000000000),(4539/12500000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((17/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5720513619043/100000000000000),(206504703/50000000000000),(-727651403/100000000000000),(15891567/100000000000000),(34562847/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((17/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((17/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((17/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel22

namespace Hf4Quad.Panel23
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(87/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((87/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (87/40) (1/40)

def c3 : Certificate := ⟨(381142857142857/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((87/40)+(1/40)*x)) := (SharedCertificates.h2 (87/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((87/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-144857142857143/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((87/40)+(1/40)*x)) := (SharedCertificates.h4 (87/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(7569/1600),(87/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((87/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(71585119047619/12500000000000),(13165079365079/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((87/40)+(1/40)*x)) := (SharedCertificates.h8 (87/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((87/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((87/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(658503/64000),(22707/64000),(261/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((87/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(128310529/1280000),(4424501/1280000),(1986575520833/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((87/40)+(1/40)*x)) := (SharedCertificates.h13 (87/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((87/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((87/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(57289761/2560000),(658503/640000),(22707/1280000),(87/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((87/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(3125929419642857/50000000000000),(57488357142857/20000000000000),(2477946428571/50000000000000),(9494047619/25000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((87/40)+(1/40)*x)) := (SharedCertificates.h18 (87/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((87/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(4867391803710937/100000000000000),(69933790283203/25000000000000),(658503/10240000),(7569/10240000),(425781251/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((87/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(6342031246464843/20000000000000),(455605692993163/25000000000000),(41894776367187/100000000000000),(96309830729/20000000000000),(554777201/20000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((87/40)+(1/40)*x)) := (SharedCertificates.h22 (87/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((87/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(10586577173071287/100000000000000),(730108770556639/100000000000000),(131125856781/625000000000),(5023979187/1562500000000),(1392309573/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((87/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(23772187048949493/100000000000000),(102466323486851/6250000000000),(9422190665457/20000000000000),(361003473771/50000000000000),(3126434831/50000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((87/40)+(1/40)*x)) := (SharedCertificates.h26 (87/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((87/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(23025805351430049/100000000000000),(115790687830467/6250000000000),(63884517423703/100000000000000),(611920664977/50000000000000),(7082264411/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((87/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(5464060158791733/100000000000000),(219818512135299/50000000000000),(94749358679/625000000000),(290419490203/100000000000000),(420158147/12500000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((87/40)+(1/40)*x)) := (SharedCertificates.h30 (87/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((87/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((87/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((87/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((87/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((87/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (87/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((87/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((87/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (87/40) (1/40))

def c43 : Certificate := ⟨(16129/1600),(127/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((87/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((87/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(23619094857/50000000000000),(-1487817/200000000000),(109829/1250000000000),(-18449/20000000000000),(931/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((87/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-260239209761519/25000000000000),(156369579073/100000000000000),(-156467339/12500000000000),(5010823/50000000000000),(5110991/12500000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((87/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((87/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (87/40) (1/40))

def c52 : Certificate := ⟨(27833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((87/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (87/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((87/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (87/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((87/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (87/40) (1/40))

def c56 : Certificate := ⟨(22770398481973/100000000000000),(-43207587253/100000000000000),(81987831/100000000000000),(-6223/4000000000000),(299/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((87/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1783681214421/20000000000000),(10801896813/6250000000000),(-327951327/100000000000000),(311149/50000000000000),(71/5000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((87/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((87/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((87/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((87/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((87/40)+(1/40)*x)) := (SharedCertificates.h61 (87/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-8101872688843/6250000000000),(-2604589434197/100000000000000),(1575037589/50000000000000),(-322071/12500000000000),(8163/20000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((87/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((87/40)+(1/40)*x)) := (SharedCertificates.h61 (87/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-68209305751423/50000000000000),(-1437976332937/50000000000000),(24870539/3125000000000),(2118713/50000000000000),(5649/10000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((87/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((87/40)+(1/40)*x)) := (SharedCertificates.h67 (87/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-318227395389551/50000000000000),(-12590386330117/100000000000000),(1156527393/6250000000000),(-1038271/3125000000000),(119709/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((87/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((87/40)+(1/40)*x)) := (SharedCertificates.h67 (87/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-681050047754397/100000000000000),(-14320973245709/100000000000000),(2467073567/50000000000000),(22787007/100000000000000),(63237/20000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((87/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((87/40)+(1/40)*x)) := (SharedCertificates.h72 (87/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(437846914379011/50000000000000),(15692922923857/100000000000000),(-56512317431/100000000000000),(29657223/25000000000000),(29293/12500000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((87/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((87/40)+(1/40)*x)) := (SharedCertificates.h72 (87/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1014530569168029/50000000000000),(2632526242157/6250000000000),(-6089841343/20000000000000),(-67765063/50000000000000),(268729/20000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((87/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((87/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((87/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(118632191812879/100000000000000),(47061015337/12500000000000),(-415695421/100000000000000),(44399/20000000000000),(6331/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((87/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5672734788775317/50000000000000),(7238644977621/50000000000000),(-67226449969/100000000000000),(148795129/100000000000000),(606923/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((87/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(55088068037/6250000000000),(-1124714571/100000000000000),(1664471/25000000000000),(-167/625000000000),(37/20000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((87/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(8942164643191/50000000000000),(348432062649/100000000000000),(-607024039/100000000000000),(282011/20000000000000),(27451/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((87/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((87/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((87/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (87/40) (1/40))

def c87 : Certificate := ⟨(1207729468599/6250000000000),(-93351070037/100000000000000),(56371419/12500000000000),(-1089303/50000000000000),(10579/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((87/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(378421900161/5000000000000),(124468093381/100000000000000),(-300647569/50000000000000),(2904807/100000000000000),(2239/10000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((87/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((87/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((87/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((87/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((87/40)+(1/40)*x)) := (SharedCertificates.h61 (87/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-27348751818399/25000000000000),(-185559679311/10000000000000),(1004337169/12500000000000),(-17162217/50000000000000),(6241/1562500000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((87/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((87/40)+(1/40)*x)) := (SharedCertificates.h61 (87/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-114237625349201/100000000000000),(-1009577440009/50000000000000),(737439393/10000000000000),(-6321147/25000000000000),(514481/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((87/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((87/40)+(1/40)*x)) := (SharedCertificates.h67 (87/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-269218332038153/50000000000000),(-180155488323/2000000000000),(20411243899/50000000000000),(-93624337/50000000000000),(1767749/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((87/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((87/40)+(1/40)*x)) := (SharedCertificates.h67 (87/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-285270952666311/50000000000000),(-10064696208667/100000000000000),(148824291/400000000000),(-64087277/50000000000000),(2568391/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((87/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((87/40)+(1/40)*x)) := (SharedCertificates.h72 (87/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(75150487995061/10000000000000),(2899316720183/25000000000000),(-69416765679/100000000000000),(385559/100000000000),(3100539/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((87/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((87/40)+(1/40)*x)) := (SharedCertificates.h72 (87/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(1703126342536669/100000000000000),(29764531109361/100000000000000),(-116947239397/100000000000000),(399759537/100000000000000),(319911/4000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((87/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((87/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((87/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(4628387541781/4000000000000),(66944191931/25000000000000),(-1138684513/100000000000000),(4752469/100000000000000),(5911/10000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((87/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2245997722569587/20000000000000),(2716575904437/25000000000000),(-14490919537/20000000000000),(426201907/100000000000000),(5317211/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((87/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(890472853067/100000000000000),(-430817373/50000000000000),(6578959/100000000000000),(-45721/100000000000000),(967/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((87/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(15165877733721/100000000000000),(50074068207/20000000000000),(-592898489/50000000000000),(2873459/50000000000000),(28219/25000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((87/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((87/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-344038390294649/100000000000000),(-6181594103921/100000000000000),(383702711/2000000000000),(-40743847/50000000000000),(15313999/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((87/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(11494252873563/25000000000000),(-264235698243/50000000000000),(6074383867/100000000000000),(-13964101/20000000000000),(81187/10000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((87/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-158178570250411/100000000000000),(-20479354921/2000000000000),(10295248093/50000000000000),(-137068987/50000000000000),(198709/1250000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((87/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((87/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((87/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((87/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((87/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((87/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((87/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((87/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((87/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((87/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (87/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((87/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((87/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(4728584413/100000000000000),(-10870309/5000000000000),(780913/12500000000000),(-143617/100000000000000),(329/10000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((87/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(119299982401799/100000000000000),(-10337592157/2000000000000),(613295729/12500000000000),(-22019531/50000000000000),(81552249/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((87/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((87/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (87/40) (1/40))

def c134 : Certificate := ⟨(34569/1600),(187/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((87/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((87/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(262467191601/5000000000000),(-41333416001/100000000000000),(39729/12207031250),(-2562677/100000000000000),(10171/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((87/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(113415354330687/100000000000000),(41749979331/12500000000000),(26036797/4000000000000),(-1281339/25000000000000),(420743/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((87/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((87/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (87/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((87/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (87/40) (1/40))

def c140 : Certificate := ⟨(6047187105683/25000000000000),(-2442772713/12500000000000),(-22296833/100000000000000),(69733/20000000000000),(49807/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((87/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(3245006309067/100000000000000),(15633745363/20000000000000),(89187329/100000000000000),(-1394661/100000000000000),(106293/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((87/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((87/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(52650329729/50000000000000),(5073160233/100000000000000),(66891767/100000000000000),(48919/100000000000000),(4059/25000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((87/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((87/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(125677388741/10000000000000),(60384049687/100000000000000),(19756021/2500000000000),(118291/25000000000000),(194331/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((87/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-454260100877443/100000000000000),(-2735169970933/25000000000000),(-12412260369/100000000000000),(97960971/50000000000000),(14883101/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((87/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-14427227116747/1562500000000),(-22597358597967/100000000000000),(-34332563373/100000000000000),(383737941/100000000000000),(61797287/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((87/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(243872981092087/20000000000000),(7159977251867/25000000000000),(7367727881/50000000000000),(-22344239/4000000000000),(82569843/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((87/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3446825092633089/100000000000000),(4197984601589/5000000000000),(117599833141/100000000000000),(-91404073/6250000000000),(28679511/12500000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((87/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(1815478003978623/50000000000000),(92914836343661/100000000000000),(3729494477/1562500000000),(-1321835877/100000000000000),(64475427/25000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((87/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(13324414159699/12500000000000),(161410613863/100000000000000),(9810657/4000000000000),(-2740403/100000000000000),(6897/1562500000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((87/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((87/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((87/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((87/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(27963591058434261/50000000000000),(648309306801/781250000000),(51821752527/50000000000000),(-1492158529/100000000000000),(4741863/2000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((87/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(8940196539/5000000000000),(-265305559/100000000000000),(62297/100000000000000),(5169/100000000000000),(389/50000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((87/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(81153650839/1250000000000),(78251125763/50000000000000),(45634161/25000000000000),(-2751179/100000000000000),(124817/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((87/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((87/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((87/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (87/40) (1/40))

def c175 : Certificate := ⟨(22714569965797/100000000000000),(-51698333617/100000000000000),(8456187/50000000000000),(984151/100000000000000),(134981/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((87/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(3047240045603/100000000000000),(1077048617/1562500000000),(-22549833/100000000000000),(-1312203/100000000000000),(216191/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((87/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((87/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(18571343791/20000000000000),(2100496433/50000000000000),(23070343/50000000000000),(-5553/5000000000000),(191/1250000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((87/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((87/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1108621493209/100000000000000),(50027871381/100000000000000),(136281623/25000000000000),(-1385231/100000000000000),(91579/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((87/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-17063192961053/4000000000000),(-603004184617/6250000000000),(801955677/25000000000000),(184016141/100000000000000),(30271903/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((87/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-866226123993033/100000000000000),(-1988875719057/10000000000000),(-142623453/100000000000000),(383008657/100000000000000),(15668179/25000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((87/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(286697857055341/25000000000000),(3166915056741/12500000000000),(-22200240633/100000000000000),(-119443437/25000000000000),(83881953/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((87/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(3234547535523453/100000000000000),(18485047792719/25000000000000),(-7148500837/100000000000000),(-17855453/1250000000000),(14550359/6250000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((87/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(3396730903476221/100000000000000),(20335789107099/25000000000000),(3054553299/4000000000000),(-796479217/50000000000000),(64930667/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((87/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(106187336810161/100000000000000),(71031607921/50000000000000),(52051/5000000000000),(-1367733/50000000000000),(223831/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((87/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((87/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((87/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((87/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(55717292171108627/100000000000000),(14627288889251/20000000000000),(-16767312829/100000000000000),(-1418832751/100000000000000),(240101593/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((87/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(89738747257/50000000000000),(-117794183/50000000000000),(90813/25000000000000),(2011/50000000000000),(789/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((87/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(6096367520941/100000000000000),(137990356283/100000000000000),(-42240427/100000000000000),(-260681/10000000000000),(501507/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((87/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((87/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(15018268673179/100000000000000),(143130707489/50000000000000),(-368576591/50000000000000),(893857/50000000000000),(2230783/10000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((87/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1380990222821/20000000000000),(26123594741/50000000000000),(-234865853/25000000000000),(11620367/100000000000000),(2150943/20000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((87/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((87/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((87/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((87/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((87/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((87/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (87/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((87/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((87/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((87/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (87/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((87/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(36949973661/100000000000000),(-21288449/20000000000000),(191939/10000000000000),(-159/1562500000000),(117/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((87/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(221800877050229/50000000000000),(-362773011891/25000000000000),(-1331260559/25000000000000),(-48006787/100000000000000),(89533/3125000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((87/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((87/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((87/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((87/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (87/40) (1/40))

def c223 : Certificate := ⟨(27889/1600),(167/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((87/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2895129201/2560000),(14901243/640000),(215147/1280000),(307/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((87/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((87/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(110222442667/100000000000000),(-1735786499/100000000000000),(4100283/20000000000000),(-107619/50000000000000),(2167/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((87/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(24930329091467/20000000000000),(120662455389/20000000000000),(259437133/20000000000000),(-4961293/100000000000000),(993961/20000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((87/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((87/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (87/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((87/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (87/40) (1/40))

def c231 : Certificate := ⟨(23548713650291/100000000000000),(-6691238903/20000000000000),(-6100601/25000000000000),(51499/12500000000000),(34661/12500000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((87/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(362821587427/6250000000000),(133824778059/100000000000000),(48804807/50000000000000),(-164797/10000000000000),(62293/5000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((87/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((87/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(67399426203/20000000000000),(15537445891/100000000000000),(11901467/6250000000000),(69917/100000000000000),(152307/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((87/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((87/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(4004839225289/100000000000000),(45935859179/25000000000000),(555182289/25000000000000),(301993/100000000000000),(909627/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((87/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-812487869096463/100000000000000),(-18719442887393/100000000000000),(-265732521/2000000000000),(233818569/100000000000000),(43620341/25000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((87/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-836303406910941/50000000000000),(-991123470539/2500000000000),(-13486579763/25000000000000),(45234189/10000000000000),(185084051/50000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((87/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(534470930264297/25000000000000),(2936420678403/6250000000000),(-20239337313/100000000000000),(-691536101/100000000000000),(48250427/10000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((87/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(6219509927238929/100000000000000),(18263056368157/12500000000000),(166276487081/100000000000000),(-357394089/20000000000000),(1365749727/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((87/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(340875292875781/5000000000000),(87062829648997/50000000000000),(524984872067/100000000000000),(-70628501/5000000000000),(1638278917/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((87/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(111947287928679/100000000000000),(283187002009/100000000000000),(3856427/1000000000000),(-3226023/100000000000000),(2644027/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((87/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((87/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((87/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((87/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(29326744765378659/50000000000000),(28578706085231/20000000000000),(60521625487/50000000000000),(-237954037/12500000000000),(5757683/400000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((87/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(170492839897/100000000000000),(-207680089/50000000000000),(660067/100000000000000),(2391/50000000000000),(2117/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((87/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(5811679673311/50000000000000),(268554577061/100000000000000),(8672523/4000000000000),(-62271/2000000000000),(3113689/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((87/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((87/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((87/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (87/40) (1/40))

def c259 : Certificate := ⟨(21099052320347/100000000000000),(-16114591899/20000000000000),(134451183/100000000000000),(810713/100000000000000),(675583/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((87/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(5201263572869/100000000000000),(53715306329/50000000000000),(-89634123/50000000000000),(-1080953/100000000000000),(1233859/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((87/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((87/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(33816428443/12500000000000),(2793874661/25000000000000),(96764937/100000000000000),(-3981/800000000000),(16627/12500000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((87/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((87/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(3218235025339/100000000000000),(132362182307/100000000000000),(225614277/20000000000000),(-95027/1562500000000),(1591257/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((87/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-364004755657799/50000000000000),(-15029943896543/100000000000000),(5058531327/20000000000000),(37989229/25000000000000),(172796667/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((87/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-1867774367403/125000000000),(-31644423619369/100000000000000),(36668975687/100000000000000),(372555933/100000000000000),(22756461/6250000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((87/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1924768181318471/100000000000000),(7621925367599/20000000000000),(-24607040431/25000000000000),(-284515371/100000000000000),(47699749/10000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((87/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(278071950889477/5000000000000),(116852115678817/100000000000000),(-77930129493/50000000000000),(-1344665321/100000000000000),(5382553/400000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((87/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(6039856955031671/100000000000000),(68453546181791/50000000000000),(5337007029/20000000000000),(-134309603/6250000000000),(395855343/25000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((87/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(55336529286641/50000000000000),(5650918099/2500000000000),(-52354311/20000000000000),(-2659531/100000000000000),(1300367/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((87/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((87/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((87/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((87/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(14502260762078651/25000000000000),(57290326810043/50000000000000),(-178898327087/100000000000000),(-1280188353/100000000000000),(352564109/25000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((87/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(172386915461/100000000000000),(-170251089/50000000000000),(1204203/100000000000000),(3/800000000000),(527/12500000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((87/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(2082384620607/20000000000000),(53861017273/25000000000000),(-10857437/3125000000000),(-212409/10000000000000),(3003617/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((87/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((87/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(24437224866917/25000000000000),(1827274252871/100000000000000),(-175522167/2000000000000),(-57690339/100000000000000),(7005127/25000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((87/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(22471011371877/50000000000000),(323551119207/100000000000000),(-969246341/12500000000000),(12520361/20000000000000),(1918499/12500000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((87/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((87/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((87/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((87/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((87/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((87/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (87/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((87/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1048169447068590383/100000000000000),(1509737320643511/50000000000000),(-45749615777077/100000000000000),0,(33929/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((87/40)+(1/40)*x)) := (SharedCertificates.h297 (87/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(381617687/4000000000000),(-2748327/10000000000000),(15487/3125000000000),(-657/25000000000000),(33/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((87/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(127335387293271/20000000000000),(219324287993/20000000000000),(8232413943/100000000000000),(6023933/25000000000000),(1938013/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((87/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((87/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (87/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((87/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (87/40) (1/40))

def c307 : Certificate := ⟨(760643885794813/25000000000000),(11091229182759/50000000000000),0,0,(531/50000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((87/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (87/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((87/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (87/40) (1/40))

def c311 : Certificate := ⟨(2132424456820489/100000000000000),(2817541634481/100000000000000),0,0,(531/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((87/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (87/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4689497894293/100000000000000),(-3098082917/50000000000000),(1023363/12500000000000),(-5409/50000000000000),(19/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((87/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(4458797375927/3125000000000),(851722891673/100000000000000),(-70335573/6250000000000),(148691/10000000000000),(607/20000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((87/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((87/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (87/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((87/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (87/40) (1/40))

def c316 : Certificate := ⟨(22589603671931/100000000000000),(-1358205749/3125000000000),(28209771/20000000000000),(-28609/6250000000000),(387/25000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((87/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(602599082017/6250000000000),(43462583967/25000000000000),(-564195423/100000000000000),(915487/50000000000000),(469/6250000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((87/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((87/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(464800836669/50000000000000),(65476283/195312500000),(96722313/50000000000000),(-804321/50000000000000),(5523/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((87/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((87/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(10975963403257/100000000000000),(98147397241/25000000000000),(2177960119/100000000000000),(-19321877/100000000000000),(137181/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((87/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-168595460855339/12500000000000),(-6070528353033/25000000000000),(39908970769/50000000000000),(-25642691/10000000000000),(44083/4000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((87/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1414843044482023/50000000000000),(-6670513115367/12500000000000),(131065560633/100000000000000),(-3579119/1250000000000),(1827991/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((87/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1719591873443879/50000000000000),(5686781483723/10000000000000),(-140693578127/50000000000000),(1154443223/100000000000000),(2628971/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((87/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(418210256515503/4000000000000),(97002422019619/50000000000000),(-16877318971/3125000000000),(1286761763/100000000000000),(6652593/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((87/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(12139769511216289/100000000000000),(128153067268349/50000000000000),(-139968635363/100000000000000),(-94591083/6250000000000),(29796527/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((87/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(60106386148941/50000000000000),(47653066079/12500000000000),(-46747311/5000000000000),(1026653/50000000000000),(13027/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((87/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((87/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((87/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((87/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(6275969297439121/10000000000000),(186332071915543/100000000000000),(-601618102313/100000000000000),(773774491/50000000000000),(4018309/20000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((87/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(31867587383/20000000000000),(-473070637/100000000000000),(1465979/50000000000000),(-17169/100000000000000),(29/20000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((87/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(604476821419/3125000000000),(175481611/50000000000),(-134949907/12500000000000),(73623/2000000000000),(21313/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((87/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((87/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((87/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (87/40) (1/40))

def c344 : Certificate := ⟨(18937796131387/100000000000000),(-18327720123/20000000000000),(564513199/100000000000000),(-3477519/100000000000000),(10837/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((87/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(8082938491483/100000000000000),(61092400409/50000000000000),(-752684267/100000000000000),(463669/10000000000000),(23699/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((87/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((87/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(65333894657/10000000000000),(1234515287/6250000000000),(13806621/50000000000000),(-108977/10000000000000),(24847/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((87/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((87/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((87/40)+(1/40)*x)) := (SharedCertificates.h144 (87/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(1546889877691/20000000000000),(1451482811/625000000000),(144230829/50000000000000),(-12731791/100000000000000),(74029/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((87/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((87/40)+(1/40)*x)) := (SharedCertificates.h148 (87/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1130986218020897/100000000000000),(-2134706274861/12500000000000),(21124931239/20000000000000),(-325601319/50000000000000),(1332707/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((87/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((87/40)+(1/40)*x)) := (SharedCertificates.h151 (87/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-2354639697965019/100000000000000),(-1478960537927/4000000000000),(206935633197/100000000000000),(-286437943/25000000000000),(16754811/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((87/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((87/40)+(1/40)*x)) := (SharedCertificates.h154 (87/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(2921607240738401/100000000000000),(41175549725141/100000000000000),(-150255292491/50000000000000),(264309921/12500000000000),(23214833/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((87/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((87/40)+(1/40)*x)) := (SharedCertificates.h157 (87/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(2180809283072187/25000000000000),(135191995204493/100000000000000),(-393144390361/50000000000000),(4497802293/100000000000000),(2394477/4000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((87/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((87/40)+(1/40)*x)) := (SharedCertificates.h160 (87/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(61857957498721/625000000000),(171465952324413/100000000000000),(-89797210523/12500000000000),(489596819/20000000000000),(103496199/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((87/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((87/40)+(1/40)*x)) := (SharedCertificates.h41 (87/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(1825300248899/1562500000000),(66030461557/25000000000000),(-369438823/25000000000000),(818361/10000000000000),(119643/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((87/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((87/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((87/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((87/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((87/40)+(1/40)*x)) := (SharedCertificates.h167 (87/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(6108967235106161/10000000000000),(13085196040287/10000000000000),(-399687482517/50000000000000),(4749538907/100000000000000),(36134823/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((87/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(163693790049/100000000000000),(-43828303/12500000000000),(2893007/100000000000000),(-2939/12500000000000),(313/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((87/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(2025152701531/12500000000000),(245976660909/100000000000000),(-1490815789/100000000000000),(1831899/20000000000000),(33903/12500000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((87/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((87/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(45260701139059/20000000000000),(1047591736583/25000000000000),(-1378580061/20000000000000),(111272967/100000000000000),(3883907/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((87/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(104047588825421/100000000000000),(730656195721/100000000000000),(-2313499329/20000000000000),(92059857/50000000000000),(762197/10000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((87/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((87/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(7105273092773437/100000000000000),(95656563720703/25000000000000),(840159/10240000),(8961/10240000),(464843751/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((87/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(42849/1600),(207/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((87/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(8869743/64000),(128547/64000),(621/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((87/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(196943582117861073/20000000000000),(67299345095621633/100000000000000),(39491004587113/2000000000000),(2026945329277/6250000000000),(8192411223/2500000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((87/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(126939907/1250000000000),(-21688883/3125000000000),(27070479/100000000000000),(-396431/50000000000000),(7291/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((87/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(178704753773/3125000000000),(-92597267/4000000000000),(-319129277/50000000000000),(6975937/50000000000000),(993107/3125000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((87/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((87/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((87/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel23

namespace Hf4Quad.Panel24
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(89/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((89/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (89/40) (1/40)

def c3 : Certificate := ⟨(389904761904761/100000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((89/40)+(1/40)*x)) := (SharedCertificates.h2 (89/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((89/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-29847619047619/10000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((89/40)+(1/40)*x)) := (SharedCertificates.h4 (89/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(7921/1600),(89/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((89/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(149828439153439/25000000000000),(3366931216931/25000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((89/40)+(1/40)*x)) := (SharedCertificates.h8 (89/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((89/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((89/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(704969/64000),(23763/64000),(267/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((89/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(5365801372974537/50000000000000),(361739418402777/100000000000000),(2032243923611/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((89/40)+(1/40)*x)) := (SharedCertificates.h13 (89/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((89/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((89/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(62742241/2560000),(704969/640000),(23763/1280000),(89/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((89/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(1711717884424603/25000000000000),(307724563492063/100000000000000),(5186369047619/100000000000000),(38849206349/100000000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((89/40)+(1/40)*x)) := (SharedCertificates.h18 (89/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((89/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(2726591527832031/50000000000000),(76589649658203/25000000000000),(704969/10240000),(7921/10240000),(108886719/25000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((89/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(4440809719867169/12500000000000),(1995869537018949/100000000000000),(22425500415943/50000000000000),(503943829571/100000000000000),(1418753621/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((89/40)+(1/40)*x)) := (SharedCertificates.h22 (89/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((89/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(12133332298852537/100000000000000),(102247182293701/12500000000000),(1148844744873/5000000000000),(344223144531/100000000000000),(728454591/25000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((89/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(27245429775836067/100000000000000),(918385273342787/50000000000000),(25797339138841/50000000000000),(772953981687/100000000000000),(204468339/3125000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((89/40)+(1/40)*x)) := (SharedCertificates.h26 (89/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((89/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(13498332182473447/50000000000000),(2123333152299191/100000000000000),(17893256901397/25000000000000),(1340318869017/100000000000000),(3032333987/20000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((89/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(400396956603131/6250000000000),(503870327410681/100000000000000),(8492196529393/50000000000000),(79514948777/25000000000000),(3597888343/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((89/40)+(1/40)*x)) := (SharedCertificates.h30 (89/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((89/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((89/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((89/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((89/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((89/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (89/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((89/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((89/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (89/40) (1/40))

def c43 : Certificate := ⟨(16641/1600),(129/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((89/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((89/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(45784794297/100000000000000),(-709841773/100000000000000),(4126987/50000000000000),(-85313/100000000000000),(53/6250000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((89/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-260162257015803/25000000000000),(75740127913/50000000000000),(-238704439/20000000000000),(9415239/100000000000000),(3840153/10000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((89/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((89/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (89/40) (1/40))

def c52 : Certificate := ⟨(140833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((89/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (89/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((89/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (89/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((89/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (89/40) (1/40))

def c56 : Certificate := ⟨(22684310018903/100000000000000),(-2144074671/5000000000000),(5066339/6250000000000),(-38309/25000000000000),(293/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((89/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(289461247637/3125000000000),(171525973677/100000000000000),(-162122849/50000000000000),(30647/5000000000000),(351/25000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((89/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((89/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((89/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((89/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((89/40)+(1/40)*x)) := (SharedCertificates.h61 (89/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-134826562226383/100000000000000),(-1296010050637/50000000000000),(15672897/500000000000),(-103539/4000000000000),(8039/20000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((89/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((89/40)+(1/40)*x)) := (SharedCertificates.h61 (89/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-142167299714707/100000000000000),(-574543760857/20000000000000),(820969947/100000000000000),(4133801/100000000000000),(55899/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((89/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((89/40)+(1/40)*x)) := (SharedCertificates.h67 (89/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-661561810370433/100000000000000),(-625838252431/5000000000000),(4576688947/25000000000000),(-32671453/100000000000000),(5939/5000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((89/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((89/40)+(1/40)*x)) := (SharedCertificates.h67 (89/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-354836038476451/50000000000000),(-1787620798857/12500000000000),(1013698457/20000000000000),(10999429/50000000000000),(31129/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((89/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((89/40)+(1/40)*x)) := (SharedCertificates.h72 (89/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(906854571321783/100000000000000),(618731644501/4000000000000),(-27902553343/50000000000000),(58555293/50000000000000),(116713/50000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((89/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((89/40)+(1/40)*x)) := (SharedCertificates.h72 (89/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(528294776932579/25000000000000),(20998509039537/50000000000000),(-15623191341/50000000000000),(-130221349/100000000000000),(659749/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((89/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((89/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((89/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(23876701412587/20000000000000),(374828025653/100000000000000),(-414348001/100000000000000),(227099/100000000000000),(6233/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((89/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5687078219255229/50000000000000),(177627033423/1250000000000),(-66338944903/100000000000000),(14704119/10000000000000),(597533/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((89/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(439593039451/50000000000000),(-274600083/25000000000000),(3250031/50000000000000),(-25893/100000000000000),(179/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((89/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(1857877653743/10000000000000),(34602077017/10000000000000),(-598651281/100000000000000),(1380989/100000000000000),(539/2000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((89/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((89/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((89/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (89/40) (1/40))

def c87 : Certificate := ⟨(19138755980861/100000000000000),(-22893248781/25000000000000),(219074151/50000000000000),(-524101/25000000000000),(5041/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((89/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(7814992025517/100000000000000),(122097326831/100000000000000),(-584197737/100000000000000),(698801/25000000000000),(867/4000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((89/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((89/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((89/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((89/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((89/40)+(1/40)*x)) := (SharedCertificates.h61 (89/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-28268583594693/25000000000000),(-1823865331897/100000000000000),(7832162963/100000000000000),(-16597359/50000000000000),(192863/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((89/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((89/40)+(1/40)*x)) := (SharedCertificates.h61 (89/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-59123319285923/50000000000000),(-1989958245487/100000000000000),(1806134529/25000000000000),(-12334919/50000000000000),(31041/6250000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((89/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((89/40)+(1/40)*x)) := (SharedCertificates.h67 (89/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-278145203580511/50000000000000),(-884670394113/10000000000000),(39719547031/100000000000000),(-90225601/50000000000000),(342207/20000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((89/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((89/40)+(1/40)*x)) := (SharedCertificates.h67 (89/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-29526174637227/5000000000000),(-2479349450563/25000000000000),(1138942749/3125000000000),(-12513723/10000000000000),(247739/10000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((89/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((89/40)+(1/40)*x)) := (SharedCertificates.h72 (89/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(387212399406247/50000000000000),(283104051773/2500000000000),(-8393943749/12500000000000),(369647629/100000000000000),(1495679/50000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((89/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((89/40)+(1/40)*x)) := (SharedCertificates.h72 (89/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(881095398950107/50000000000000),(366268841443/1250000000000),(-57286323637/50000000000000),(391770719/100000000000000),(7695709/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((89/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((89/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((89/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(58120362527311/50000000000000),(65819611593/25000000000000),(-222125583/20000000000000),(2300359/50000000000000),(11413/20000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((89/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2250286954885203/20000000000000),(5290763037129/50000000000000),(-69952332651/100000000000000),(20402133/5000000000000),(10232327/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((89/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(222193884613/25000000000000),(-41792899/5000000000000),(6311779/100000000000000),(-8673/20000000000000),(923/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((89/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(15661920752589/100000000000000),(24569521701/10000000000000),(-575993531/50000000000000),(5524899/100000000000000),(423/390625000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((89/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((89/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-7126509671013/2000000000000),(-47701709169/781250000000),(1870566347/10000000000000),(-39178173/50000000000000),(14871731/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((89/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(44943820224719/100000000000000),(-252493372049/50000000000000),(141850209/2500000000000),(-63752903/100000000000000),(362233/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((89/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-32029256948373/20000000000000),(-188958351019/20000000000000),(19022677461/100000000000000),(-62238571/25000000000000),(1843977/12500000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((89/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((89/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((89/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((89/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((89/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((89/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((89/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((89/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((89/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((89/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (89/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((89/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((89/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(4317656917/100000000000000),(-194051997/100000000000000),(2725449/50000000000000),(-122493/100000000000000),(2741/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((89/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(118285502375199/100000000000000),(-248885327373/50000000000000),(2325484707/50000000000000),(-41170933/100000000000000),(2950297/2000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((89/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((89/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (89/40) (1/40))

def c134 : Certificate := ⟨(35321/1600),(189/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((89/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((89/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(516795865633/10000000000000),(-40061695011/100000000000000),(12422231/4000000000000),(-240741/10000000000000),(18811/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((89/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(28521479328161/25000000000000),(33654327663/10000000000000),(77638943/12500000000000),(-2407419/50000000000000),(795881/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((89/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((89/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (89/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((89/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (89/40) (1/40))

def c140 : Certificate := ⟨(60373944041/250000000000),(-2453409317/12500000000000),(-2533941/12500000000000),(326717/100000000000000),(46959/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((89/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1700844767199/50000000000000),(3925454907/5000000000000),(8108611/10000000000000),(-163359/12500000000000),(6283/3125000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((89/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((89/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(28928729221/25000000000000),(5341271549/100000000000000),(3357669/5000000000000),(4801/12500000000000),(7993/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((89/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((89/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(1380706478173/100000000000000),(31775089081/50000000000000),(158539487/20000000000000),(173601/50000000000000),(191289/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((89/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-29761847966747/6250000000000),(-10988027979637/100000000000000),(-5637039031/50000000000000),(45907429/25000000000000),(28151949/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((89/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-968671560311893/100000000000000),(-5682544552969/25000000000000),(-32100345201/100000000000000),(360632919/100000000000000),(11706779/20000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((89/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(127669927165341/10000000000000),(28692297384577/100000000000000),(574774113/5000000000000),(-815393/156250000000),(78096771/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((89/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(3615203356627469/100000000000000),(21103225252111/25000000000000),(21818549161/20000000000000),(-1374361727/100000000000000),(217227313/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((89/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(3817729999577103/100000000000000),(46927004894001/50000000000000),(46193775733/20000000000000),(-626010531/50000000000000),(3832791/1562500000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((89/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(1336488674821/1250000000000),(162359467829/100000000000000),(286657/125000000000),(-321917/12500000000000),(209049/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((89/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((89/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((89/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((89/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(56093552120149323/100000000000000),(5211289120621/6250000000000),(47481859509/50000000000000),(-1402251127/100000000000000),(14048357/6250000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((89/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(17827360939/10000000000000),(-2070281/781250000000),(1439/1562500000000),(149/3125000000000),(183/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((89/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(680600506701/10000000000000),(78600050119/50000000000000),(166563191/100000000000000),(-2575617/100000000000000),(237303/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((89/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((89/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((89/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (89/40) (1/40))

def c175 : Certificate := ⟨(22611248658007/100000000000000),(-322619997/625000000000),(11287491/50000000000000),(904449/100000000000000),(126493/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((89/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(3185001789323/100000000000000),(34412799679/50000000000000),(-30099977/100000000000000),(-602967/50000000000000),(204291/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((89/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((89/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(101442363979/100000000000000),(2192096571/50000000000000),(45452261/100000000000000),(-29563/25000000000000),(299/2000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((89/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((89/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(302711621383/25000000000000),(52191407813/100000000000000),(107311599/20000000000000),(-1468971/100000000000000),(7/3906250000)⟩
theorem h181 : c181.Valid (fun x => f181 ((89/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-44586168502299/10000000000000),(-9633088240497/100000000000000),(2133321373/50000000000000),(3382459/2000000000000),(446969/1562500000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((89/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-113250150457041/12500000000000),(-4971212207523/25000000000000),(1034029877/50000000000000),(177130493/50000000000000),(29647107/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((89/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1197369534341613/100000000000000),(1262048110159/5000000000000),(-623394591/2500000000000),(-217333453/50000000000000),(7925427/10000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((89/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(1691194059941369/50000000000000),(36947450591127/50000000000000),(-96170909/625000000000),(-659637031/50000000000000),(6880581/3125000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((89/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(3559710123069377/100000000000000),(20407471241973/25000000000000),(67095870869/100000000000000),(-374378201/25000000000000),(246546151/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((89/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(851771567541/800000000000),(71017695929/50000000000000),(-14747693/100000000000000),(-63253/2500000000000),(105883/25000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((89/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((89/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((89/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((89/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(3491467929192761/6250000000000),(9131600173747/12500000000000),(-24943373701/100000000000000),(-1307976759/100000000000000),(22733589/10000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((89/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(179007802069/100000000000000),(-234088887/100000000000000),(193023/50000000000000),(3581/100000000000000),(93/12500000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((89/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(3186079425667/50000000000000),(8611936069/6250000000000),(-57237527/100000000000000),(-2395127/100000000000000),(4757/1000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((89/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((89/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(194848217433/1250000000000),(17708415311/6250000000000),(-363075117/50000000000000),(1870511/100000000000000),(21095827/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((89/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1751444651083/25000000000000),(2431239997/5000000000000),(-872705723/100000000000000),(10646361/100000000000000),(9935853/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((89/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((89/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((89/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((89/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((89/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((89/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (89/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((89/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((89/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((89/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (89/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((89/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(459308589/1250000000000),(-3955329/4000000000000),(930497/50000000000000),(-9301/100000000000000),(109/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((89/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(440677884358687/100000000000000),(-29459425909/2000000000000),(-1403854683/25000000000000),(-48833099/100000000000000),(2696677/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((89/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((89/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((89/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((89/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (89/40) (1/40))

def c223 : Certificate := ⟨(28561/1600),(169/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((89/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(3016070161/2560000),(15335229/640000),(218843/1280000),(309/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((89/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((89/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(53415593347/50000000000000),(-1656297469/100000000000000),(2407409/12500000000000),(-199063/100000000000000),(79/4000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((89/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(12586341970781/10000000000000),(19013836367/3125000000000),(79273107/6250000000000),(-4649007/100000000000000),(2359221/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((89/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((89/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (89/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((89/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (89/40) (1/40))

def c231 : Certificate := ⟨(23481706897627/100000000000000),(-524202493/1562500000000),(-22004389/100000000000000),(3877/1000000000000),(16361/6250000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((89/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(6073172409491/100000000000000),(26839167641/20000000000000),(88017553/100000000000000),(-1550803/100000000000000),(1182503/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((89/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((89/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(184417115577/50000000000000),(16299889241/100000000000000),(38155229/20000000000000),(9573/20000000000000),(9431/6250000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((89/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((89/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(4381210896321/100000000000000),(192628909763/100000000000000),(2221744587/100000000000000),(7857/20000000000000),(225249/12500000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((89/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-106247257354673/12500000000000),(-9384919630107/50000000000000),(-11925170827/100000000000000),(220197897/100000000000000),(165613791/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((89/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-21901361345169/1250000000000),(-39855394577273/100000000000000),(-25652812019/50000000000000),(214127743/50000000000000),(35223083/10000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((89/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(278970347861577/12500000000000),(46893653646927/100000000000000),(-6063891327/25000000000000),(-647808459/100000000000000),(91606041/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((89/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(203511557235671/3125000000000),(146748495323587/100000000000000),(38959755729/25000000000000),(-52924101/3125000000000),(1298623779/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((89/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(3583922962795967/50000000000000),(176208866938813/100000000000000),(516671979577/100000000000000),(-135945037/10000000000000),(392293501/25000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((89/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(14064397381267/12500000000000),(284691565651/100000000000000),(366811251/100000000000000),(-3053741/100000000000000),(1257951/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((89/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((89/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((89/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((89/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(14734936433803337/25000000000000),(143355256770553/100000000000000),(109916927987/100000000000000),(-45163707/2500000000000),(54871241/4000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((89/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(84832398539/50000000000000),(-206332249/50000000000000),(85911/12500000000000),(2149/50000000000000),(1997/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((89/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(12161311244519/100000000000000),(134692630559/50000000000000),(99361387/50000000000000),(-583899/20000000000000),(595783/20000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((89/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((89/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((89/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (89/40) (1/40))

def c259 : Certificate := ⟨(20938450500129/100000000000000),(-40012903679/50000000000000),(139031899/100000000000000),(8971/1250000000000),(631583/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((89/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(135384983329/2500000000000),(26675269119/25000000000000),(-185375867/100000000000000),(-239227/25000000000000),(146101/12500000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((89/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((89/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(469224799/160000000000),(11556578767/100000000000000),(9377351/10000000000000),(-499237/100000000000000),(26159/20000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((89/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((89/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(108981968647/3125000000000),(27360288107/20000000000000),(545775499/50000000000000),(-6088429/100000000000000),(1564419/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((89/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-757967048760693/100000000000000),(-14927021244463/100000000000000),(13075618497/50000000000000),(26903027/20000000000000),(32738039/20000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((89/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-9733492223681/625000000000),(-1259736728903/4000000000000),(9699808077/25000000000000),(67609313/20000000000000),(345578031/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((89/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(400118309518139/20000000000000),(1508508061033/4000000000000),(-19997084879/20000000000000),(-235420123/100000000000000),(451832057/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((89/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(5794509321145481/100000000000000),(116213076403913/100000000000000),(-163528025787/100000000000000),(-303310483/25000000000000),(638226511/50000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((89/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1578440234523103/25000000000000),(136988542273373/100000000000000),(7080955843/50000000000000),(-1013443881/50000000000000),(483397/32000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((89/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(22224812833139/20000000000000),(224958731719/100000000000000),(-17311139/6250000000000),(-2413053/100000000000000),(2468411/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((89/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((89/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((89/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((89/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(29118739398176979/50000000000000),(2846256156287/2500000000000),(-93085738233/50000000000000),(-229247449/20000000000000),(67006309/5000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((89/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(171710730043/100000000000000),(-335682611/100000000000000),(602577/50000000000000),(-1/2000000000000),(993/25000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((89/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(338793906249/3125000000000),(214029828443/100000000000000),(-89859663/25000000000000),(-1880157/100000000000000),(357767/12500000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((89/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((89/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(101367883291237/100000000000000),(447869995473/25000000000000),(-364820147/4000000000000),(-57162427/100000000000000),(13308317/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((89/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(2847412452001/6250000000000),(293265169029/100000000000000),(-1478843407/20000000000000),(57390111/100000000000000),(7109729/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((89/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((89/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((89/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((89/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((89/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((89/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (89/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((89/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1054025397888056123/100000000000000),(2836476178178717/100000000000000),(-45749615777077/100000000000000),0,(136449/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((89/40)+(1/40)*x)) := (SharedCertificates.h297 (89/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4743718709/50000000000000),(-25531539/100000000000000),(240253/50000000000000),(-1201/50000000000000),(3/10000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((89/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(5111226456683/800000000000),(564925176197/50000000000000),(8384276699/100000000000000),(26428731/100000000000000),(3580673/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((89/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((89/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (89/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((89/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (89/40) (1/40))

def c307 : Certificate := ⟨(3086940459910289/100000000000000),(11091229182759/50000000000000),0,0,(213/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((89/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (89/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((89/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (89/40) (1/40))

def c311 : Certificate := ⟨(534514885022363/25000000000000),(2817541634481/100000000000000),0,0,(133/12500000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((89/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (89/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2338569111967/50000000000000),(-6163547567/100000000000000),(4061171/50000000000000),(-669/6250000000000),(9/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((89/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(36095118050137/25000000000000),(84723919561/10000000000000),(-69780907/6250000000000),(1471309/100000000000000),(1493/50000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((89/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((89/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (89/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((89/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (89/40) (1/40))

def c316 : Certificate := ⟨(22503239061069/100000000000000),(-8580766867/20000000000000),(17292207/12500000000000),(-446051/100000000000000),(749/50000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((89/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(249676093893/2500000000000),(171615337337/100000000000000),(-276675313/50000000000000),(892101/50000000000000),(1463/20000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((89/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((89/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(498705214893/50000000000000),(17139298831/50000000000000),(183991501/100000000000000),(-385723/25000000000000),(1337/12500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((89/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((89/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(5884850762669/50000000000000),(401072916301/100000000000000),(51613277/2500000000000),(-18494271/100000000000000),(66269/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((89/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-1397010680559547/100000000000000),(-23965893286561/100000000000000),(78298448183/100000000000000),(-62525401/25000000000000),(1072883/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((89/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-733973079885291/25000000000000),(-10568652659083/20000000000000),(16169886787/12500000000000),(-282492243/100000000000000),(888503/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((89/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(3551802995378801/100000000000000),(55755983539449/100000000000000),(-274562207697/100000000000000),(112073147/10000000000000),(5113769/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((89/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(5420558031385727/50000000000000),(191859917368431/100000000000000),(-66550863749/12500000000000),(1268994439/100000000000000),(12912743/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((89/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(3162952488275187/25000000000000),(127864203901419/50000000000000),(-37204564451/25000000000000),(-718481479/50000000000000),(14522889/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((89/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(60485748970613/50000000000000),(23594329521/6250000000000),(-922709751/100000000000000),(253189/12500000000000),(12663/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((89/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((89/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((89/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((89/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(31564981491410197/50000000000000),(183944083251393/100000000000000),(-592397990463/100000000000000),(1525802423/100000000000000),(9732187/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((89/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(15840338767/10000000000000),(-115386437/25000000000000),(1415623/50000000000000),(-1641/10000000000000),(69/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((89/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(20040895567281/100000000000000),(34668857031/10000000000000),(-264458223/25000000000000),(893701/25000000000000),(103523/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((89/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((89/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((89/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (89/40) (1/40))

def c344 : Certificate := ⟨(3751349900273/20000000000000),(-17884320593/20000000000000),(544151843/100000000000000),(-3311293/100000000000000),(10193/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((89/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(8324333998179/100000000000000),(7451800247/6250000000000),(-45345987/6250000000000),(4415057/100000000000000),(45277/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((89/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((89/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(173236341283/25000000000000),(794000309/4000000000000),(21363031/100000000000000),(-124381/12500000000000),(11753/50000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((89/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((89/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((89/40)+(1/40)*x)) := (SharedCertificates.h144 (89/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(8199978208347/100000000000000),(116621474937/50000000000000),(215520991/100000000000000),(-5799503/50000000000000),(279809/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((89/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((89/40)+(1/40)*x)) := (SharedCertificates.h148 (89/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-58236208308561/5000000000000),(-4165709973791/25000000000000),(101811550569/100000000000000),(-124029357/20000000000000),(3181997/50000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((89/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((89/40)+(1/40)*x)) := (SharedCertificates.h151 (89/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-1213884524619859/50000000000000),(-18079911122841/50000000000000),(20020874127/10000000000000),(-43879149/4000000000000),(15972669/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((89/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((89/40)+(1/40)*x)) := (SharedCertificates.h154 (89/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1501386492467893/50000000000000),(9999606286129/25000000000000),(-288163825779/100000000000000),(80094093/4000000000000),(5517873/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((89/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((89/40)+(1/40)*x)) := (SharedCertificates.h157 (89/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(4495255775280547/50000000000000),(132100016967973/100000000000000),(-759896849779/100000000000000),(430128931/10000000000000),(11410769/20000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((89/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((89/40)+(1/40)*x)) := (SharedCertificates.h160 (89/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(2559337779328771/25000000000000),(168621696179531/100000000000000),(-703781503099/100000000000000),(1208445993/50000000000000),(98515897/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((89/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((89/40)+(1/40)*x)) := (SharedCertificates.h41 (89/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(11734161336149/10000000000000),(258307615629/100000000000000),(-1429708553/100000000000000),(3917533/50000000000000),(5703/5000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((89/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((89/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((89/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((89/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((89/40)+(1/40)*x)) := (SharedCertificates.h167 (89/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(61348216334366989/100000000000000),(127710589465563/100000000000000),(-12055061301/1562500000000),(907223367/20000000000000),(68768313/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((89/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(32600784823/20000000000000),(-339330603/100000000000000),(689089/25000000000000),(-22059/100000000000000),(73/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((89/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(8343642023327/50000000000000),(60030379101/25000000000000),(-359299661/25000000000000),(8717331/100000000000000),(25633/10000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((89/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((89/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(234657554185687/100000000000000),(2082061258561/50000000000000),(-6231370959/100000000000000),(109251307/100000000000000),(1862291/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((89/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(105464069296937/100000000000000),(68652619537/10000000000000),(-10514393639/100000000000000),(33448193/20000000000000),(1748371/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((89/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((89/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(3952025922363281/50000000000000),(104127501220703/25000000000000),(895073/10240000),(1869/2048000),(14831543/3125000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((89/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(43681/1600),(209/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((89/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(9129329/64000),(131043/64000),(627/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((89/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(225495905386142811/20000000000000),(75597305191489063/100000000000000),(217711788181317/10000000000000),(17559657830383/50000000000000),(348710108103/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((89/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(8869340649/100000000000000),(-594687741/100000000000000),(11373683/50000000000000),(-163289/25000000000000),(2941/12500000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((89/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2855738669363/50000000000000),(-4707498569/100000000000000),(-139926437/25000000000000),(1533933/12500000000000),(7313369/25000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((89/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((89/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((89/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel24
