import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel4
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(49/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((49/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (49/40) (1/40)

def c3 : Certificate := ⟨(107333333333333/50000000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((49/40)+(1/40)*x)) := (SharedCertificates.h2 (49/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((49/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-24647619047619/20000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((49/40)+(1/40)*x)) := (SharedCertificates.h4 (49/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(2401/1600),(49/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((49/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(90831481481481/50000000000000),(3707407407407/50000000000000),(75661375661/100000000000000),0,(3/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((49/40)+(1/40)*x)) := (SharedCertificates.h8 (49/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((49/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((49/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(117649/64000),(7203/64000),(147/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((49/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1790947306134259/100000000000000),(27412458767361/25000000000000),(2237751736111/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((49/40)+(1/40)*x)) := (SharedCertificates.h13 (49/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((49/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((49/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(5764801/2560000),(117649/640000),(7203/1280000),(49/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((49/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(314547673611111/50000000000000),(25677361111111/50000000000000),(1572083333333/100000000000000),(2673611111/12500000000000),(54563493/50000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((49/40)+(1/40)*x)) := (SharedCertificates.h18 (49/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((49/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(137927367675781/50000000000000),(7037110595703/25000000000000),(117649/10240000),(2401/10240000),(30029297/12500000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((49/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(224642814575647/12500000000000),(5730684045297/3125000000000),(7484975079571/100000000000000),(7637729673/5000000000000),(62603299/4000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((49/40)+(1/40)*x)) := (SharedCertificates.h22 (49/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((49/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(337922050805663/100000000000000),(41378210302733/100000000000000),(211113317871/10000000000000),(57445800781/100000000000000),(886474613/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((49/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(151760971811559/20000000000000),(92914880700951/100000000000000),(4740555137801/100000000000000),(64497348813/50000000000000),(497645273/25000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((49/40)+(1/40)*x)) := (SharedCertificates.h26 (49/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((49/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(413954512236937/100000000000000),(59136358890989/100000000000000),(226287087593/6250000000000),(3848419857/3125000000000),(2544238287/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((49/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(98232062824479/100000000000000),(3508287958017/25000000000000),(429586280573/50000000000000),(29223556501/100000000000000),(301875893/50000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((49/40)+(1/40)*x)) := (SharedCertificates.h30 (49/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((49/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((49/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((49/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((49/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((49/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (49/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((49/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((49/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (49/40) (1/40))

def c43 : Certificate := ⟨(7921/1600),(89/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((49/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((49/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(12023493907/12500000000000),(-432305399/20000000000000),(3643023/10000000000000),(-136443/25000000000000),(1979/25000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((49/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-131187026949631/12500000000000),(80733034563/25000000000000),(-3713452017/100000000000000),(42687667/100000000000000),(43043171/25000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((49/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((49/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (49/40) (1/40))

def c52 : Certificate := ⟨(53749999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((49/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (49/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((49/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (49/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((49/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (49/40) (1/40))

def c56 : Certificate := ⟨(24539877300613/100000000000000),(-50183798161/100000000000000),(51312677/50000000000000),(-52467/25000000000000),(27/6250000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((49/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(368098159509/20000000000000),(100367596321/50000000000000),(-410501417/100000000000000),(839471/100000000000000),(1789/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((49/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((49/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((49/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((49/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((49/40)+(1/40)*x)) := (SharedCertificates.h61 (49/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-25970115548181/100000000000000),(-570925369993/20000000000000),(3420005673/100000000000000),(-2049749/100000000000000),(2793/5000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((49/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((49/40)+(1/40)*x)) := (SharedCertificates.h61 (49/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-26244848752407/100000000000000),(-2914963002941/100000000000000),(186331713/100000000000000),(6575107/100000000000000),(3443/5000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((49/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((49/40)+(1/40)*x)) := (SharedCertificates.h67 (49/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-32329347463567/25000000000000),(-14157795758463/100000000000000),(5748726871/25000000000000),(-11630569/25000000000000),(69611/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((49/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((49/40)+(1/40)*x)) := (SharedCertificates.h67 (49/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-32803607622011/25000000000000),(-7285810962327/50000000000000),(634744737/50000000000000),(43572033/100000000000000),(437659/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((49/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((49/40)+(1/40)*x)) := (SharedCertificates.h72 (49/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(190836544224041/100000000000000),(20545612327019/100000000000000),(-35895510097/50000000000000),(150209913/100000000000000),(234937/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((49/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((49/40)+(1/40)*x)) := (SharedCertificates.h72 (49/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(196763862777021/50000000000000),(8735364574507/20000000000000),(-7930136279/100000000000000),(-271877601/100000000000000),(241587/12500000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((49/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((49/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((49/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(3241089239339/3125000000000),(20442970539/5000000000000),(-21658357/5000000000000),(61801/100000000000000),(4357/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((49/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10689629294899781/100000000000000),(5069982110669/25000000000000),(-43058846901/50000000000000),(91239749/50000000000000),(1656093/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((49/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(116935766949/12500000000000),(-1774766119/100000000000000),(2725867/25000000000000),(-50953/100000000000000),(91/25000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((49/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(920349328067/25000000000000),(401606425697/100000000000000),(-80643861/10000000000000),(1079569/50000000000000),(9507/25000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((49/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((49/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((49/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (49/40) (1/40))

def c87 : Certificate := ⟨(11834319526627/50000000000000),(-140051118659/100000000000000),(207176211/25000000000000),(-4903579/100000000000000),(29191/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((49/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1775147928993/100000000000000),(186734824877/100000000000000),(-1104939793/100000000000000),(1307621/20000000000000),(433/1000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((49/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((49/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((49/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((49/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((49/40)+(1/40)*x)) := (SharedCertificates.h61 (49/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-25041140016091/100000000000000),(-2654065380797/100000000000000),(6806167601/50000000000000),(-34083257/50000000000000),(837033/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((49/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((49/40)+(1/40)*x)) := (SharedCertificates.h61 (49/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-12648294142147/50000000000000),(-677040415969/25000000000000),(1378927671/12500000000000),(-9908987/25000000000000),(543751/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((49/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((49/40)+(1/40)*x)) := (SharedCertificates.h67 (49/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-24941881378509/20000000000000),(-13166749156913/100000000000000),(72764040687/100000000000000),(-409501803/100000000000000),(343861/10000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((49/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((49/40)+(1/40)*x)) := (SharedCertificates.h67 (49/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-126474131483223/100000000000000),(-13538042908931/100000000000000),(55428512753/100000000000000),(-19172979/10000000000000),(139927/2500000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((49/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((49/40)+(1/40)*x)) := (SharedCertificates.h72 (49/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(5754544675579/3125000000000),(19130665075821/100000000000000),(-3472937947/2500000000000),(185584017/20000000000000),(6468859/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((49/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((49/40)+(1/40)*x)) := (SharedCertificates.h72 (49/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(379318772648947/100000000000000),(10145308931249/25000000000000),(-169591503817/100000000000000),(488445771/100000000000000),(3719779/20000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((49/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((49/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((49/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(25895451839921/25000000000000),(380099288507/100000000000000),(-190040927/10000000000000),(9181717/100000000000000),(125073/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((49/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(1068302309041013/10000000000000),(4723127253637/25000000000000),(-150353209349/100000000000000),(1049478657/100000000000000),(24289177/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((49/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(11700807809/1250000000000),(-1655393723/100000000000000),(8050851/50000000000000),(-143731/100000000000000),(1393/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((49/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(443833605711/12500000000000),(373587372743/100000000000000),(-87927541/4000000000000),(6684323/50000000000000),(140079/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((49/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((49/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-9487532579653/12500000000000),(-253508591009/3125000000000),(8442059669/25000000000000),(-99182831/50000000000000),(8813203/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((49/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(10204081632653/12500000000000),(-832986255727/50000000000000),(33999439009/100000000000000),(-693866103/100000000000000),(7227773/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((49/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-1239187928771/2000000000000),(-5357787756183/100000000000000),(17113564549/12500000000000),(-2955982507/100000000000000),(19643047/20000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((49/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((49/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((49/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((49/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((49/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((49/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((49/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((49/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((49/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((49/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (49/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((49/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((49/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(5873998749/12500000000000),(-239755051/6250000000000),(24464801/12500000000000),(-7988507/100000000000000),(344921/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((49/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(149643278342101/100000000000000),(-614924714293/50000000000000),(9073132003/50000000000000),(-86827741/25000000000000),(428124639/20000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((49/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((49/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (49/40) (1/40))

def c134 : Certificate := ⟨(21801/1600),(149/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((49/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((49/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(7490636704119/100000000000000),(-1683289147/2000000000000),(47283403/5000000000000),(-2656371/25000000000000),(60373/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((49/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(102064606741561/100000000000000),(124168875981/50000000000000),(945668059/50000000000000),(-21250971/100000000000000),(1531201/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((49/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((49/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (49/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((49/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (49/40) (1/40))

def c140 : Certificate := ⟨(12435812344989/50000000000000),(-3072423317/20000000000000),(-13438639/12500000000000),(22707/1562500000000),(38179/20000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((49/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(102700248017/20000000000000),(1920264573/3125000000000),(86007289/20000000000000),(-5812993/100000000000000),(154291/20000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((49/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((49/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(527367047/20000000000000),(631077273/100000000000000),(67481/160000000000),(234401/50000000000000),(889/6250000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((49/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((49/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3951867807/12500000000000),(7563205507/100000000000000),(504876101/100000000000000),(1112771/20000000000000),(4287/2500000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((49/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-71890011268779/100000000000000),(-8602727022989/100000000000000),(-30098863163/50000000000000),(162837703/20000000000000),(1687651/1562500000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((49/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-144149503323163/100000000000000),(-8646960496699/50000000000000),(-126314717739/100000000000000),(390503107/25000000000000),(217998869/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((49/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(12309860496599/6250000000000),(2935034672697/12500000000000),(153668659063/100000000000000),(-593397643/25000000000000),(59744589/20000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((49/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(270093841335047/50000000000000),(64762488696061/100000000000000),(93520523649/20000000000000),(-5792851/97656250000),(203907559/25000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((49/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(136181010746961/25000000000000),(65849876110601/100000000000000),(540577677679/100000000000000),(-5095691461/100000000000000),(839658671/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((49/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(20205927863081/20000000000000),(24705601989/20000000000000),(180449703/20000000000000),(-174331/1562500000000),(778567/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((49/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((49/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((49/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((49/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(53039721485272537/100000000000000),(64650343039441/100000000000000),(460005302981/100000000000000),(-3012413361/50000000000000),(102787283/12500000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((49/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(188537943261/100000000000000),(-45961941/20000000000000),(-271009/20000000000000),(1253/5000000000000),(2979/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((49/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(1027011507097/100000000000000),(61450086671/50000000000000),(860483373/100000000000000),(-58027/500000000000),(1624317/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((49/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((49/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((49/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (49/40) (1/40))

def c175 : Certificate := ⟨(12309394557589/50000000000000),(-45154119343/100000000000000),(-417719/160000000000),(4973557/100000000000000),(571581/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((49/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(254140589881/50000000000000),(7525686557/12500000000000),(174049583/50000000000000),(-663141/10000000000000),(785711/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((49/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((49/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(2583497577/100000000000000),(306013187/50000000000000),(19892829/50000000000000),(351737/100000000000000),(197/1250000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((49/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((49/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(1548785403/5000000000000),(7334984043/100000000000000),(119067129/25000000000000),(4165443/100000000000000),(94827/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((49/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-35579603861493/50000000000000),(-8428713012419/100000000000000),(-6090867321/12500000000000),(92872879/10000000000000),(13750517/12500000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((49/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-35670104798471/25000000000000),(-529475662533/3125000000000),(-25759422281/25000000000000),(1807557639/100000000000000),(222205549/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((49/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(194963036490401/100000000000000),(4601418788387/20000000000000),(15349629827/12500000000000),(-2655457211/100000000000000),(12185681/4000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((49/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(534686199172073/100000000000000),(63450086263543/100000000000000),(47582309681/12500000000000),(-854423553/12500000000000),(415578809/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((49/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(134782664348113/25000000000000),(16126149422863/25000000000000),(449497105297/100000000000000),(-620328789/10000000000000),(857952509/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((49/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(101019145857101/100000000000000),(60511505643/50000000000000),(73598399/10000000000000),(-12911083/100000000000000),(793591/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((49/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((49/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((49/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((49/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(6629278684926823/12500000000000),(791766786699/1250000000000),(18674604027/5000000000000),(-6906725923/100000000000000),(838484189/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((49/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(11784841717/6250000000000),(-45040659/20000000000000),(-52947/5000000000000),(13703/50000000000000),(1523/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((49/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(127071389243/12500000000000),(24082819161/20000000000000),(87073101/12500000000000),(-3311089/25000000000000),(416289/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((49/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((49/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(611616805951/20000000000000),(169485229919/50000000000000),(-14575869/5000000000000),(-19280721/100000000000000),(6777277/12500000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((49/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(249639512633/10000000000000),(112881870073/50000000000000),(-30283729/625000000000),(83146281/100000000000000),(47807527/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((49/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((49/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((49/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((49/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((49/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((49/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (49/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((49/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((49/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((49/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (49/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((49/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(2790761797/6250000000000),(-334438041/100000000000000),(4860087/100000000000000),(-27021/50000000000000),(21/3125000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((49/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(493650877366837/100000000000000),(-156931592339/12500000000000),(556437121/100000000000000),(-14078783/20000000000000),(14261137/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((49/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((49/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((49/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((49/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (49/40) (1/40))

def c223 : Certificate := ⟨(16641/1600),(129/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((49/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1186187121/2560000),(8000709/640000),(149483/1280000),(269/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((49/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((49/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(56109638233/25000000000000),(-1260890747/25000000000000),(8500387/10000000000000),(-1273467/100000000000000),(18467/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((49/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(103994578493677/100000000000000),(468773727047/100000000000000),(636882137/25000000000000),(-4419001/20000000000000),(3421111/20000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((49/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((49/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (49/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((49/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (49/40) (1/40))

def c231 : Certificate := ⟨(24752807419559/100000000000000),(-1795114713/6250000000000),(-122760167/100000000000000),(419331/25000000000000),(1053273/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((49/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(494385160881/50000000000000),(114887341629/100000000000000),(98208133/20000000000000),(-6709297/100000000000000),(4297233/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((49/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((49/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(9776667491/100000000000000),(1135971937/50000000000000),(141701541/100000000000000),(124451/12500000000000),(107971/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((49/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((49/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(58563336159/50000000000000),(27195933567/100000000000000),(1692299919/100000000000000),(2895253/25000000000000),(1298201/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((49/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-69213343466453/50000000000000),(-804191217951/5000000000000),(-17174285079/25000000000000),(235371503/25000000000000),(601643013/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((49/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-278224412091151/100000000000000),(-32486522478709/100000000000000),(-78664326349/50000000000000),(347859463/20000000000000),(243668747/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((49/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(75585114692743/20000000000000),(10897691200877/25000000000000),(37201484983/25000000000000),(-288748753/10000000000000),(1660758589/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((49/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(520972826879429/50000000000000),(474597304299/390625000000),(142250021587/25000000000000),(-6713661049/100000000000000),(4554087787/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((49/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1058813736636613/100000000000000),(125428486810003/100000000000000),(163249359969/20000000000000),(-4816725069/100000000000000),(4738989227/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((49/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(20397463462203/20000000000000),(58011656783/25000000000000),(1123782871/100000000000000),(-6211493/50000000000000),(8702437/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((49/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((49/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((49/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((49/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(334626254597503/625000000000),(24217489643651/20000000000000),(33922980271/6250000000000),(-6953152931/100000000000000),(1151121549/25000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((49/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(186775541791/100000000000000),(-422414811/100000000000000),(-93811/10000000000000),(1533/5000000000000),(16253/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((49/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(49440127329/2500000000000),(45959429951/20000000000000),(984788039/100000000000000),(-13296437/100000000000000),(9115391/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((49/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((49/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((49/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (49/40) (1/40))

def c259 : Certificate := ⟨(3034100359667/12500000000000),(-16571215741/20000000000000),(-167445243/100000000000000),(240557/4000000000000),(768803/25000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((49/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(19391923271/2000000000000),(55237385803/50000000000000),(111630161/50000000000000),(-1002321/12500000000000),(869193/20000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((49/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((49/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(9401167203/100000000000000),(1071159147/50000000000000),(63188099/50000000000000),(337797/100000000000000),(111157/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((49/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((49/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(56315849861/50000000000000),(1282275201/5000000000000),(1509288277/100000000000000),(3759727/100000000000000),(666989/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((49/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-135742370824361/100000000000000),(-3866523734351/25000000000000),(-6242645561/20000000000000),(1124351581/100000000000000),(304225689/50000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((49/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-10912123144553/4000000000000),(-6246571157397/20000000000000),(-20051181083/25000000000000),(549493227/25000000000000),(246486783/20000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((49/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1447849354619/390625000000),(41928575918799/100000000000000),(50064074911/100000000000000),(-625449/19531250000),(840390349/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((49/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(102166977442737/10000000000000),(58407261083187/50000000000000),(56411353811/20000000000000),(-8331348499/100000000000000),(4606153099/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((49/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(207577622720299/20000000000000),(120521143136821/100000000000000),(502556080911/100000000000000),(-7600099743/100000000000000),(4797732009/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((49/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(101948593494303/100000000000000),(111545930753/50000000000000),(286448421/50000000000000),(-15699339/100000000000000),(8803087/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((49/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((49/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((49/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((49/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(5351999251182239/10000000000000),(58214320379593/50000000000000),(51732835363/20000000000000),(-8442843147/100000000000000),(1164390783/25000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((49/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(93423032503/50000000000000),(-406469291/100000000000000),(-2349/12500000000000),(787/2500000000000),(16467/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((49/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(1939253099429/100000000000000),(110485158497/50000000000000),(89785957/20000000000000),(-3187829/20000000000000),(462181/5000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((49/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((49/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(1933560483293/10000000000000),(13600270319/625000000000),(1440182963/100000000000000),(-3251407/2000000000000),(45771003/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((49/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(3156833442111/20000000000000),(1454235976143/100000000000000),(-14251312833/50000000000000),(112243937/25000000000000),(91362053/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((49/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((49/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((49/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((49/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((49/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((49/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (49/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((49/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(867366965517585661/100000000000000),(1299289088068961/20000000000000),(-45749615777077/100000000000000),0,(112823/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((49/40)+(1/40)*x)) := (SharedCertificates.h297 (49/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(288228639/2500000000000),(-86351531/100000000000000),(1254869/100000000000000),(-6977/50000000000000),(7/4000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((49/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(303098534628909/50000000000000),(507281017787/100000000000000),(4179462601/50000000000000),(-2242547/6250000000000),(3513673/20000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((49/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((49/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (49/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((49/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (49/40) (1/40))

def c307 : Certificate := ⟨(2199642125289539/100000000000000),(11091229182759/50000000000000),0,0,(203/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((49/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (49/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((49/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (49/40) (1/40))

def c311 : Certificate := ⟨(1012678937355101/50000000000000),(2817541634481/100000000000000),0,0,(507/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((49/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (49/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4937399027039/100000000000000),(-34342887/500000000000),(4777551/50000000000000),(-13293/100000000000000),(23/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((49/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(21721021778477/20000000000000),(944152361613/100000000000000),(-656720637/50000000000000),(913579/50000000000000),(3513/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((49/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((49/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (49/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((49/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (49/40) (1/40))

def c316 : Certificate := ⟨(3059188377229/12500000000000),(-56550246057/100000000000000),(104668983/50000000000000),(-48433/6250000000000),(147/5000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((49/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(2105971928669/100000000000000),(113100492113/50000000000000),(-837351867/100000000000000),(3099709/100000000000000),(12259/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((49/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((49/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(44351177643/100000000000000),(476372923/5000000000000),(238200031/50000000000000),(-3657639/100000000000000),(21661/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((49/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((49/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(530346085013/100000000000000),(113727564717/100000000000000),(2827187691/50000000000000),(-45736047/100000000000000),(7079/2500000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((49/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-58964980214797/20000000000000),(-7916135768247/25000000000000),(58800576473/50000000000000),(-423068057/100000000000000),(935327/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((49/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-119176213936533/20000000000000),(-2020938087491/3125000000000),(2097229797/1250000000000),(-354808321/100000000000000),(3223317/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((49/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(159650020896359/20000000000000),(1318399338131/1562500000000),(-460141700893/100000000000000),(2088477187/100000000000000),(4512629/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((49/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(2228081448223407/100000000000000),(9643746028329/4000000000000),(-176182802927/25000000000000),(1576038513/100000000000000),(12207603/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((49/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2305116064797383/100000000000000),(257745646979213/100000000000000),(72248157537/50000000000000),(-14713351/390625000000),(6070689/12500000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((49/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(104256295034981/100000000000000),(14435294591/3125000000000),(-149787959/12500000000000),(2541779/100000000000000),(46179/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((49/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((49/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((49/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((49/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(54719989641561307/100000000000000),(59829881882759/25000000000000),(-399629240849/50000000000000),(469509527/25000000000000),(4805747/12500000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((49/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(36549714521/20000000000000),(-799256403/100000000000000),(3082429/50000000000000),(-44909/100000000000000),(449/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((49/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(842513341061/20000000000000),(452602703061/100000000000000),(-826938251/50000000000000),(426007/6250000000000),(177691/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((49/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((49/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((49/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (49/40) (1/40))

def c344 : Certificate := ⟨(4696871800287/20000000000000),(-31242858051/20000000000000),(1256427889/100000000000000),(-10105419/100000000000000),(41051/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((49/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(126303416547/6250000000000),(208285720339/100000000000000),(-1675237187/100000000000000),(1347389/10000000000000),(123597/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((49/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((49/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(510481697/1250000000000),(841830339/10000000000000),(73224239/20000000000000),(-1286797/20000000000000),(90163/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((49/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((49/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((49/40)+(1/40)*x)) := (SharedCertificates.h144 (49/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(48841185421/10000000000000),(100509275649/100000000000000),(2172478411/50000000000000),(-39100943/50000000000000),(278983/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((49/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((49/40)+(1/40)*x)) := (SharedCertificates.h148 (49/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-282909782971541/100000000000000),(-14578476204463/50000000000000),(117411087927/50000000000000),(-1880492983/100000000000000),(17552037/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((49/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((49/40)+(1/40)*x)) := (SharedCertificates.h151 (49/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-571556501676781/100000000000000),(-14874620501787/25000000000000),(41782146879/10000000000000),(-1435630507/50000000000000),(11806829/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((49/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((49/40)+(1/40)*x)) := (SharedCertificates.h154 (49/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(766478719703691/100000000000000),(15559430780951/20000000000000),(-187718666783/25000000000000),(1383883179/20000000000000),(69107511/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((49/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((49/40)+(1/40)*x)) := (SharedCertificates.h157 (49/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(2137386818951063/100000000000000),(110934319746129/50000000000000),(-1624973106217/100000000000000),(1440429847/12500000000000),(17005437/10000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((49/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((49/40)+(1/40)*x)) := (SharedCertificates.h160 (49/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(2208284360458733/100000000000000),(118285517461059/50000000000000),(-972046945683/100000000000000),(246620227/25000000000000),(153131753/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((49/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((49/40)+(1/40)*x)) := (SharedCertificates.h41 (49/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(6505159241579/6250000000000),(106247436017/25000000000000),(-2984353179/100000000000000),(4102759/20000000000000),(337357/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((49/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((49/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((49/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((49/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((49/40)+(1/40)*x)) := (SharedCertificates.h167 (49/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(54629948305876689/100000000000000),(27538114899857/12500000000000),(-1697707743771/100000000000000),(3116388767/25000000000000),(5458911/2500000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((49/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(36609955931/20000000000000),(-36909029/5000000000000),(866539/10000000000000),(-49827/50000000000000),(1589/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((49/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(161690386239/4000000000000),(104185407963/25000000000000),(-1667147389/50000000000000),(6820093/25000000000000),(93009/10000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((49/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((49/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(50040515474401/100000000000000),(5311815047183/100000000000000),(-12569057279/50000000000000),(251093789/100000000000000),(8885473/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((49/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(8169880077453/20000000000000),(3502514316327/100000000000000),(-92000793851/100000000000000),(1041270871/50000000000000),(65258109/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((49/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((49/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(250521137207031/50000000000000),(11632774658203/25000000000000),(175273/10240000),(637/2048000),(69824219/25000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((49/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(28561/1600),(169/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((49/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(4826809/64000),(85683/64000),(507/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((49/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(37788052492535377/100000000000000),(4180117669677573/100000000000000),(97677828653167/50000000000000),(1002757433911/20000000000000),(38820923159/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((49/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(264633907819/100000000000000),(-14636913007/50000000000000),(935087967/50000000000000),(-90652093/100000000000000),(5750771/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((49/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1571166470679/50000000000000),(23522203859/10000000000000),(-9600680459/100000000000000),(268310277/100000000000000),(16150239/10000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((49/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((49/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((49/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel4

namespace Hf4Quad.Panel5
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(51/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((51/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (51/40) (1/40)

def c3 : Certificate := ⟨(223428571428571/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((51/40)+(1/40)*x)) := (SharedCertificates.h2 (51/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((51/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-33/25),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((51/40)+(1/40)*x)) := (SharedCertificates.h4 (51/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(2601/1600),(51/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((51/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(98397619047619/50000000000000),(385873015873/5000000000000),(75661375661/100000000000000),0,(1/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((51/40)+(1/40)*x)) := (SharedCertificates.h8 (51/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((51/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((51/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(132651/64000),(7803/64000),(153/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((51/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(25847293/1280000),(1520429/1280000),(1164544270833/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((51/40)+(1/40)*x)) := (SharedCertificates.h13 (51/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((51/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((51/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(6765201/2560000),(132651/640000),(7803/1280000),(51/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((51/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(738265982142857/100000000000000),(28951607142857/50000000000000),(340607142857/20000000000000),(22261904761/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((51/40)+(1/40)*x)) := (SharedCertificates.h18 (51/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((51/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(336938721679687/100000000000000),(8258302001953/25000000000000),(132651/10240000),(2601/10240000),(250000001/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((51/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(219509337568359/10000000000000),(26900654113769/12500000000000),(8439420898437/100000000000000),(33095768229/20000000000000),(814351857/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((51/40)+(1/40)*x)) := (SharedCertificates.h22 (51/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((51/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(536996087677/125000000000),(3158800515747/6250000000000),(495498120117/20000000000000),(64770996093/100000000000000),(96000977/10000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((51/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(964660908402619/100000000000000),(283723796589/250000000000),(5563211697821/100000000000000),(72721721539/50000000000000),(13473153/625000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((51/40)+(1/40)*x)) := (SharedCertificates.h26 (51/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((51/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(27386800471527/5000000000000),(37589726137389/50000000000000),(1105580180511/25000000000000),(144520285033/100000000000000),(573457521/20000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((51/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(16247328057513/12500000000000),(4460050839317/25000000000000),(1049423726897/100000000000000),(6858978607/20000000000000),(680411903/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((51/40)+(1/40)*x)) := (SharedCertificates.h30 (51/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((51/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((51/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((51/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((51/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((51/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (51/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((51/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((51/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (51/40) (1/40))

def c43 : Certificate := ⟨(8281/1600),(91/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((51/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((51/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(92006371441/100000000000000),(-1011059027/50000000000000),(1041613/3125000000000),(-61047/12500000000000),(3461/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((51/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-104886487138981/10000000000000),(61715043799/20000000000000),(-433588381/12500000000000),(4872507/12500000000000),(393309/250000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((51/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((51/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (51/40) (1/40))

def c52 : Certificate := ⟨(21833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((51/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (51/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((51/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (51/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((51/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (51/40) (1/40))

def c56 : Certificate := ⟨(6109979633401/25000000000000),(-9955160299/20000000000000),(101376377/100000000000000),(-20647/10000000000000),(213/50000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((51/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(2240325865579/100000000000000),(24887900747/12500000000000),(-50688189/12500000000000),(206469/25000000000000),(221/12500000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((51/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((51/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((51/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((51/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((51/40)+(1/40)*x)) := (SharedCertificates.h61 (51/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-6333141143429/20000000000000),(-2840971611137/100000000000000),(851891927/25000000000000),(-2095799/100000000000000),(54911/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((51/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((51/40)+(1/40)*x)) := (SharedCertificates.h61 (51/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-16036988556903/50000000000000),(-145706967039/5000000000000),(56339603/25000000000000),(804267/12500000000000),(13639/20000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((51/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((51/40)+(1/40)*x)) := (SharedCertificates.h67 (51/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-157541372195931/100000000000000),(-14066370952449/100000000000000),(22718351493/100000000000000),(-365331/800000000000),(138241/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((51/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((51/40)+(1/40)*x)) := (SharedCertificates.h67 (51/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-20044031337603/12500000000000),(-14566026887897/100000000000000),(1526594361/100000000000000),(42137383/100000000000000),(214881/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((51/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((51/40)+(1/40)*x)) := (SharedCertificates.h72 (51/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(115820901468653/50000000000000),(20260243687523/100000000000000),(-35447533687/50000000000000),(9277639/6250000000000),(236299/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((51/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((51/40)+(1/40)*x)) := (SharedCertificates.h72 (51/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(240423747112493/50000000000000),(43641876726539/100000000000000),(-9533769701/100000000000000),(-262710227/100000000000000),(1894821/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((51/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((51/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((51/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(104530842330997/100000000000000),(407127533197/100000000000000),(-54094931/12500000000000),(74007/100000000000000),(1713/20000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((51/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10729846137438547/100000000000000),(9968820301133/50000000000000),(-42513968163/50000000000000),(4519243/2500000000000),(162897/10000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((51/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(232994953327/25000000000000),(-1731756293/100000000000000),(10603269/100000000000000),(-6141/12500000000000),(351/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((51/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(2240700789487/50000000000000),(398406374499/100000000000000),(-793638203/100000000000000),(210793/10000000000000),(1873/5000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((51/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((51/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((51/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (51/40) (1/40))

def c87 : Certificate := ⟨(23391812865497/100000000000000),(-34198556821/25000000000000),(799966241/100000000000000),(-2339083/50000000000000),(13761/50000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((51/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(214424951267/10000000000000),(45598075761/25000000000000),(-133327707/12500000000000),(6237553/100000000000000),(41741/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((51/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((51/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((51/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((51/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((51/40)+(1/40)*x)) := (SharedCertificates.h61 (51/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-3786920191967/12500000000000),(-2600423595447/100000000000000),(13211138407/100000000000000),(-65585497/100000000000000),(40081/5000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((51/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((51/40)+(1/40)*x)) := (SharedCertificates.h61 (51/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-1916818832467/6250000000000),(-266450822051/10000000000000),(10796147357/100000000000000),(-4848621/12500000000000),(1041039/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((51/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((51/40)+(1/40)*x)) := (SharedCertificates.h67 (51/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-37688771985621/25000000000000),(-12880532997833/100000000000000),(562898221/800000000000),(-391261881/100000000000000),(662643/20000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((51/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((51/40)+(1/40)*x)) := (SharedCertificates.h67 (51/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-19166253890679/12500000000000),(-1331861765597/10000000000000),(54287144351/100000000000000),(-188699837/100000000000000),(2671737/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((51/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((51/40)+(1/40)*x)) := (SharedCertificates.h72 (51/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(110929210192583/50000000000000),(18585945250409/100000000000000),(-33371976053/25000000000000),(44120383/5000000000000),(1552037/25000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((51/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((51/40)+(1/40)*x)) := (SharedCertificates.h72 (51/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(57475849232069/12500000000000),(39908747085029/100000000000000),(-166649287977/100000000000000),(491978487/100000000000000),(883809/5000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((51/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((51/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((51/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(20866895417013/20000000000000),(186303249113/50000000000000),(-36926317/2000000000000),(8851731/100000000000000),(29923/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((51/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5360107492352639/50000000000000),(18303477105821/100000000000000),(-144215156141/100000000000000),(199412831/20000000000000),(23135849/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((51/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(466408556837/50000000000000),(-63706919/4000000000000),(15268147/100000000000000),(-67127/50000000000000),(2609/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((51/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4289156462929/100000000000000),(364952404119/100000000000000),(-2119944931/100000000000000),(6359727/50000000000000),(132687/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((51/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((51/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-735930418611/800000000000),(-797953830291/10000000000000),(32610861049/100000000000000),(-187569729/100000000000000),(9313503/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((51/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(78431372549019/100000000000000),(-1537870049981/100000000000000),(6030862941/20000000000000),(-591261073/100000000000000),(1478153/12500000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((51/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-36075020520147/50000000000000),(-4843754726983/100000000000000),(120552728803/100000000000000),(-2510892509/100000000000000),(8687581/10000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((51/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((51/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((51/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((51/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((51/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((51/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((51/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((51/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((51/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((51/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (51/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((51/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((51/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(2502692371/6250000000000),(-785158391/25000000000000),(1231621/800000000000),(-3018679/50000000000000),(249077/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((51/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(147253543864901/100000000000000),(-1161122065927/100000000000000),(325763089/2000000000000),(-138189111/50000000000000),(1787273801/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((51/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((51/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (51/40) (1/40))

def c134 : Certificate := ⟨(22401/1600),(151/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((51/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((51/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(7326007326007/100000000000000),(-20126393753/25000000000000),(110584581/12500000000000),(-4860861/50000000000000),(54011/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((51/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(25642170329669/25000000000000),(255655516631/100000000000000),(176935329/10000000000000),(-4860863/25000000000000),(2820963/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((51/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((51/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (51/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((51/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (51/40) (1/40))

def c140 : Certificate := ⟨(12420240898079/50000000000000),(-3943802947/25000000000000),(-99159647/100000000000000),(41627/3125000000000),(7019/4000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((51/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(638072815367/100000000000000),(63100847151/100000000000000),(396638587/100000000000000),(-2664129/50000000000000),(710911/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((51/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((51/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(4071369177/100000000000000),(805258703/100000000000000),(8975771/20000000000000),(54071/12500000000000),(15171/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((51/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((51/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(12201118381/25000000000000),(385907601/4000000000000),(536924993/100000000000000),(5122703/100000000000000),(182767/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((51/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-44664941371651/50000000000000),(-8834026245817/100000000000000),(-55519694857/100000000000000),(186590819/25000000000000),(99533407/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((51/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-35846075600109/20000000000000),(-17780972635027/100000000000000),(-57295763/48828125000),(1431361753/100000000000000),(4023581/2000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((51/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(122257206798697/50000000000000),(6016818678393/25000000000000),(70013144579/50000000000000),(-2177266163/100000000000000),(137681223/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((51/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(671536636138169/100000000000000),(66563746912283/100000000000000),(433520478781/100000000000000),(-543777393/10000000000000),(752415871/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((51/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(135709248315241/20000000000000),(2123525952159/3125000000000),(255667296121/50000000000000),(-582560253/12500000000000),(155624329/20000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((51/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(101280216999911/100000000000000),(25401390601/20000000000000),(838156029/100000000000000),(-2555987/25000000000000),(1436993/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((51/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((51/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((51/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((51/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(10634163005023803/20000000000000),(16605029410561/25000000000000),(3323290493/781250000000),(-1381381429/25000000000000),(379759417/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((51/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(188073099787/100000000000000),(-234937859/100000000000000),(-1211157/100000000000000),(22937/100000000000000),(137/5000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((51/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(63808147501/5000000000000),(126206832643/100000000000000),(24806801/3125000000000),(-10633809/100000000000000),(1506263/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((51/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((51/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((51/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (51/40) (1/40))

def c175 : Certificate := ⟨(24527475489371/100000000000000),(-9228096337/20000000000000),(-232532983/100000000000000),(454729/10000000000000),(523303/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((51/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(315016340419/50000000000000),(12304128449/20000000000000),(38755497/12500000000000),(-1212611/20000000000000),(36231/5000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((51/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((51/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(3969411789/100000000000000),(775200303/100000000000000),(835093/2000000000000),(305083/100000000000000),(8283/50000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((51/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((51/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(11895731071/25000000000000),(928775159/10000000000000),(499551233/100000000000000),(72029/2000000000000),(9961/5000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((51/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-88204275529347/100000000000000),(-861280212511/10000000000000),(-10849286973/25000000000000),(212295907/25000000000000),(12681391/12500000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((51/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-44241216599093/25000000000000),(-8667153566759/50000000000000),(-1158223159/1250000000000),(1654951729/100000000000000),(205212777/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((51/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(241447645630731/100000000000000),(23467365542031/100000000000000),(107570310021/100000000000000),(-2423867643/100000000000000),(70258793/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((51/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(663055513954487/100000000000000),(64893066571773/100000000000000),(341409770787/100000000000000),(-3128590457/50000000000000),(383655257/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((51/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(669889247739923/100000000000000),(66230201432501/100000000000000),(16552198043/4000000000000),(-2851493053/50000000000000),(159111037/20000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((51/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(20252806954693/20000000000000),(123816484793/100000000000000),(330921301/50000000000000),(-11821027/100000000000000),(732903/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((51/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((51/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((51/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((51/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(10632470417262163/20000000000000),(12950966328161/20000000000000),(333837775849/100000000000000),(-1580277159/25000000000000),(775002449/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((51/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(188103039229/100000000000000),(-28640053/12500000000000),(-56383/6250000000000),(24903/100000000000000),(1401/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((51/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(1260082034467/100000000000000),(123046168697/100000000000000),(77573689/12500000000000),(-12106261/100000000000000),(386229/25000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((51/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((51/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(233419413797/6250000000000),(337584977501/100000000000000),(-79651891/20000000000000),(-4079867/25000000000000),(54541259/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((51/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(2929184800589/100000000000000),(207337535283/100000000000000),(-2188901113/50000000000000),(18259919/25000000000000),(45982409/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((51/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((51/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((51/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((51/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((51/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((51/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (51/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((51/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((51/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((51/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (51/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((51/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(44002331023/100000000000000),(-7890641/2500000000000),(2275551/50000000000000),(-49051/100000000000000),(299/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((51/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(785826629157/160000000000),(-313513607649/25000000000000),(286821/195312500000),(-66244739/100000000000000),(6414537/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((51/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((51/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((51/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((51/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (51/40) (1/40))

def c223 : Certificate := ⟨(17161/1600),(131/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((51/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1251397281/2560000),(8302911/640000),(152723/1280000),(271/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((51/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((51/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(107340766681/50000000000000),(-4718275459/100000000000000),(77773771/100000000000000),(-1139543/100000000000000),(323/2000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((51/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(52471071705101/50000000000000),(478706866793/100000000000000),(2421022017/100000000000000),(-5028301/25000000000000),(15797221/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((51/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((51/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (51/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((51/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (51/40) (1/40))

def c231 : Certificate := ⟨(24694885831801/100000000000000),(-29193334443/100000000000000),(-113131749/100000000000000),(191857/12500000000000),(968273/100000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((51/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1220456672793/100000000000000),(116773337769/100000000000000),(452526993/100000000000000),(-245577/4000000000000),(396879/10000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((51/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((51/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(14895144901/100000000000000),(570067197/20000000000000),(29481183/20000000000000),(907003/100000000000000),(11853/10000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((51/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((51/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(11148635077/6250000000000),(4262458809/12500000000000),(351696251/20000000000000),(10493667/100000000000000),(1424279/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((51/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-170861757162849/100000000000000),(-510863838057/3125000000000),(-31645845493/50000000000000),(430922183/50000000000000),(277831089/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((51/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-171906581049293/50000000000000),(-6619114289949/20000000000000),(-147342889443/100000000000000),(1592162049/100000000000000),(140982279/12500000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((51/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(116419932086633/25000000000000),(8830467165167/20000000000000),(132221985379/100000000000000),(-2644962431/100000000000000),(1533986293/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((51/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(1287162925751099/100000000000000),(61847327274167/50000000000000),(530432537411/100000000000000),(-1230613133/20000000000000),(210660513/5000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((51/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1312898038066743/100000000000000),(64318705104973/50000000000000),(394317507063/50000000000000),(-2198162549/50000000000000),(4416859087/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((51/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(102455808490487/100000000000000),(236397011523/100000000000000),(1052459901/100000000000000),(-11371847/100000000000000),(805611/10000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((51/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((51/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((51/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((51/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(26892246130524209/50000000000000),(123177433916081/100000000000000),(50279639713/10000000000000),(-6381623921/100000000000000),(2134281343/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((51/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(185927199079/100000000000000),(-53226391/12500000000000),(-762919/100000000000000),(6947/25000000000000),(7467/50000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((51/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(122051727447/5000000000000),(9343258713/4000000000000),(227129559/25000000000000),(-12148631/100000000000000),(8495089/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((51/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((51/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((51/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (51/40) (1/40))

def c259 : Certificate := ⟨(12053233920559/50000000000000),(-1669121953/2000000000000),(-8321831/6250000000000),(5428633/100000000000000),(700513/25000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((51/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(595688105921/50000000000000),(55637398433/50000000000000),(88766197/50000000000000),(-3619089/50000000000000),(501629/12500000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((51/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((51/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(14193772781/100000000000000),(2651402919/100000000000000),(128050961/100000000000000),(222629/100000000000000),(120389/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((51/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((51/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(169987070907/100000000000000),(31722070477/100000000000000),(1527609311/100000000000000),(1186953/50000000000000),(90251/6250000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((51/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-33358128894471/20000000000000),(-15577904479271/100000000000000),(-4960147027/20000000000000),(1015117059/100000000000000),(561840973/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((51/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-167786221688791/50000000000000),(-15764065260789/50000000000000),(-67634929369/100000000000000),(249450439/12500000000000),(570252581/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((51/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(56835238911909/12500000000000),(4209177059163/10000000000000),(7966393061/25000000000000),(-2869867329/100000000000000),(1552068851/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((51/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(62818099728241/5000000000000),(29461488606113/25000000000000),(58608348113/25000000000000),(-944625453/12500000000000),(4260032807/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((51/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1280881018309837/100000000000000),(122442542559269/100000000000000),(229360786447/50000000000000),(-1755466743/25000000000000),(2234053997/50000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((51/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(20479389239293/20000000000000),(225200996651/100000000000000),(483115749/100000000000000),(-14253727/100000000000000),(8146453/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((51/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((51/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((51/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((51/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(10750763709266523/20000000000000),(58682621699123/50000000000000),(210430421211/100000000000000),(-7649250591/100000000000000),(4315751211/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((51/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(46508323829/25000000000000),(-12693193/3125000000000),(79293/50000000000000),(6929/25000000000000),(7561/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((51/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(1191432583719/50000000000000),(222581186399/100000000000000),(89516593/25000000000000),(-14377071/100000000000000),(4302957/50000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((51/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((51/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(11846090167227/50000000000000),(435982085521/20000000000000),(50728049/10000000000000),(-37172031/25000000000000),(21228853/25000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((51/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(18582102223101/100000000000000),(672689361579/50000000000000),(-12991053957/50000000000000),(392834959/100000000000000),(40744961/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((51/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((51/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((51/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((51/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((51/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((51/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (51/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((51/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(880176857935166967/100000000000000),(12626893954473/200000000000),(-45749615777077/100000000000000),0,(57227/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((51/40)+(1/40)*x)) := (SharedCertificates.h297 (51/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(1420169127/12500000000000),(-8149419/10000000000000),(1175089/100000000000000),(-2533/20000000000000),(39/25000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((51/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(607244791379703/100000000000000),(540308677971/100000000000000),(4080129683/50000000000000),(-7616107/25000000000000),(3180941/20000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((51/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((51/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (51/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((51/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (51/40) (1/40))

def c307 : Certificate := ⟨(2244007042020577/100000000000000),(11091229182759/50000000000000),0,0,(1017/100000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((51/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (51/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((51/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (51/40) (1/40))

def c311 : Certificate := ⟨(507748239494791/25000000000000),(2817541634481/100000000000000),0,0,(1017/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((51/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (51/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2461849993303/50000000000000),(-1707628977/25000000000000),(947579/10000000000000),(-6573/50000000000000),(23/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((51/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(27622043606851/25000000000000),(93892044159/10000000000000),(-1302538953/100000000000000),(903483/50000000000000),(3489/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((51/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((51/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (51/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((51/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (51/40) (1/40))

def c316 : Certificate := ⟨(4872247544743/20000000000000),(-55722102381/100000000000000),(102378201/50000000000000),(-376199/50000000000000),(2837/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((51/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(2555049105137/100000000000000),(222888409519/100000000000000),(-204756403/25000000000000),(752397/25000000000000),(11931/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((51/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((51/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(510021557/781250000000),(91118533/800000000000),(454939417/100000000000000),(-1748617/50000000000000),(521/2500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((51/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((51/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(780057098437/100000000000000),(33951188319/25000000000000),(1077264271/20000000000000),(-43633469/100000000000000),(271571/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((51/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-357686943877267/100000000000000),(-31199168797667/100000000000000),(57548756511/50000000000000),(-41154049/10000000000000),(363123/20000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((51/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-11321137914017/1562500000000),(-64003151488761/100000000000000),(165658185901/100000000000000),(-175948203/50000000000000),(6243313/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((51/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(482590612484043/50000000000000),(82561781444337/100000000000000),(-223906772899/50000000000000),(1010664649/50000000000000),(4381681/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((51/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(2707462414645347/100000000000000),(59573400283559/25000000000000),(-347651594249/50000000000000),(391608677/25000000000000),(5896001/25000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((51/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2821155548788483/100000000000000),(258279106870363/100000000000000),(122400445493/100000000000000),(-3599791007/100000000000000),(47324461/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((51/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(10517538096957/10000000000000),(457166635663/100000000000000),(-1183111807/100000000000000),(1260971/50000000000000),(22351/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((51/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((51/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((51/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((51/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(5519544667092319/10000000000000),(236144997506327/100000000000000),(-788015135287/100000000000000),(373888777/20000000000000),(37053401/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((51/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(45293591243/25000000000000),(-155025179/20000000000000),(2951423/50000000000000),(-21229/50000000000000),(21/5000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((51/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(5111210650389/100000000000000),(44606802453/10000000000000),(-806850771/50000000000000),(1315471/20000000000000),(34769/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((51/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((51/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((51/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (51/40) (1/40))

def c344 : Certificate := ⟨(11588438284483/50000000000000),(-151307294171/100000000000000),(1197694967/100000000000000),(-592533/6250000000000),(37903/50000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((51/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(2430831241377/100000000000000),(100871529447/50000000000000),(-1596926623/100000000000000),(12640703/100000000000000),(116973/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((51/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((51/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(1477235131/2500000000000),(1961613321/20000000000000),(65873087/20000000000000),(-5828829/100000000000000),(20769/25000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((51/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((51/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((51/40)+(1/40)*x)) := (SharedCertificates.h144 (51/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(353100067717/50000000000000),(58490773309/50000000000000),(6237897/160000000000),(-35346599/50000000000000),(205041/20000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((51/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((51/40)+(1/40)*x)) := (SharedCertificates.h148 (51/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-170149603629631/50000000000000),(-55155781077/195312500000),(11194461117/5000000000000),(-882665183/50000000000000),(8297133/50000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((51/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((51/40)+(1/40)*x)) := (SharedCertificates.h151 (51/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-688904847029777/100000000000000),(-28930523713427/50000000000000),(401044396771/100000000000000),(-544535209/20000000000000),(44384119/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((51/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((51/40)+(1/40)*x)) := (SharedCertificates.h154 (51/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(14361311151331/1562500000000),(74874755545483/100000000000000),(-142159475889/20000000000000),(6446482283/100000000000000),(12954369/20000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((51/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((51/40)+(1/40)*x)) := (SharedCertificates.h157 (51/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(643678788671669/25000000000000),(107752279743449/50000000000000),(-389418587803/25000000000000),(5457972849/50000000000000),(3992649/2500000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((51/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((51/40)+(1/40)*x)) := (SharedCertificates.h160 (51/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(2677546764159033/100000000000000),(232695934377643/100000000000000),(-1930406933/200000000000),(643229821/50000000000000),(286788769/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((51/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((51/40)+(1/40)*x)) := (SharedCertificates.h41 (51/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(52460375943997/50000000000000),(413294184393/100000000000000),(-2864487811/100000000000000),(19452577/100000000000000),(158511/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((51/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((51/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((51/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((51/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((51/40)+(1/40)*x)) := (SharedCertificates.h167 (51/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(11012773134198741/20000000000000),(213660950060851/100000000000000),(-1624947219819/100000000000000),(5897559331/50000000000000),(203985697/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((51/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(181607300507/100000000000000),(-704679701/100000000000000),(4046799/50000000000000),(-91103/100000000000000),(1431/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((51/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4862620398201/100000000000000),(10093116907/2500000000000),(-99247847/3125000000000),(5106409/20000000000000),(8647/1000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((51/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((51/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(30282784771787/50000000000000),(41713691103/800000000000),(-1183970029/5000000000000),(58852669/25000000000000),(8514771/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((51/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(9500481497031/20000000000000),(1579078902253/50000000000000),(-80496741721/100000000000000),(440750827/25000000000000),(28197957/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((51/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((51/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(601204385742187/100000000000000),(13439981689453/25000000000000),(7803/409600),(3417/10240000),(289062501/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((51/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(29241/1600),(171/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((51/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(5000211/64000),(87723/64000),(513/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((51/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(46971074731817603/100000000000000),(2512112730188029/50000000000000),(2841786787191/1250000000000),(707319679367/12500000000000),(85128396123/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((51/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(212896980899/100000000000000),(-22772364439/100000000000000),(175674251/12500000000000),(-65754719/100000000000000),(4010063/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((51/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(715284415593/20000000000000),(19984369697/10000000000000),(-1626958301/20000000000000),(221970869/100000000000000),(152902067/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((51/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((51/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((51/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel5

namespace Hf4Quad.Panel6
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(53/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((53/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (53/40) (1/40)

def c3 : Certificate := ⟨(58047619047619/25000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((53/40)+(1/40)*x)) := (SharedCertificates.h2 (53/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((53/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-28152380952381/20000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((53/40)+(1/40)*x)) := (SharedCertificates.h4 (53/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(2809/1600),(53/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((53/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(53133201058201/25000000000000),(1604021164021/20000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((53/40)+(1/40)*x)) := (SharedCertificates.h8 (53/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((53/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((53/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(148877/64000),(8427/64000),(159/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((53/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1133162466724537/50000000000000),(128282543402777/100000000000000),(1210212673611/50000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((53/40)+(1/40)*x)) := (SharedCertificates.h13 (53/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((53/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((53/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(7890481/2560000),(148877/640000),(8427/1280000),(53/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((53/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(861064394841269/100000000000000),(16246498015873/25000000000000),(459806547619/25000000000000),(11567460317/50000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((53/40)+(1/40)*x)) := (SharedCertificates.h18 (53/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((53/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(102098509033203/25000000000000),(9631934814453/25000000000000),(148877/10240000),(2809/10240000),(129882813/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((53/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(133030575844003/5000000000000),(50200217299623/20000000000000),(591983694571/6250000000000),(89356029369/50000000000000),(1692324951/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((53/40)+(1/40)*x)) := (SharedCertificates.h22 (53/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((53/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(21644883915039/4000000000000),(61259105419921/100000000000000),(577916088867/20000000000000),(9086730957/12500000000000),(1036474613/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((53/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(1215091102320443/100000000000000),(68778741640779/50000000000000),(3244280266073/50000000000000),(163234227223/100000000000000),(290925811/12500000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((53/40)+(1/40)*x)) := (SharedCertificates.h26 (53/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((53/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(358493389842833/50000000000000),(47348183564147/50000000000000),(5360171724241/100000000000000),(42139714813/25000000000000),(1608293461/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((53/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(85071050446831/50000000000000),(11235799115619/50000000000000),(1271977258371/100000000000000),(19999642427/50000000000000),(11926581/1562500000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((53/40)+(1/40)*x)) := (SharedCertificates.h30 (53/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((53/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((53/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((53/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((53/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((53/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (53/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((53/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((53/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (53/40) (1/40))

def c43 : Certificate := ⟨(8649/1600),(93/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((53/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((53/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(88091659371/100000000000000),(-7400173/390625000000),(30555553/100000000000000),(-438073/100000000000000),(759/12500000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((53/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-524130645433149/50000000000000),(147577212687/50000000000000),(-3244999321/100000000000000),(3566571/10000000000000),(144058261/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((53/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((53/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (53/40) (1/40))

def c52 : Certificate := ⟨(27708333333333/25000000000000),(833333333333/100000000000000),0,0,(1/25000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((53/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (53/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((53/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (53/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((53/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (53/40) (1/40))

def c56 : Certificate := ⟨(973630831643/4000000000000),(-24686380113/50000000000000),(50073793/50000000000000),(-10157/5000000000000),(13/3125000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((53/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(2636916835699/100000000000000),(197491040901/100000000000000),(-400590347/100000000000000),(203139/25000000000000),(109/6250000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((53/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((53/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((53/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((53/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((53/40)+(1/40)*x)) := (SharedCertificates.h61 (53/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-3733403552369/10000000000000),(-2827366666693/100000000000000),(678972199/20000000000000),(-2139341/100000000000000),(3371/6250000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((53/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((53/40)+(1/40)*x)) := (SharedCertificates.h61 (53/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-37901303167957/100000000000000),(-1456580627811/50000000000000),(263545201/100000000000000),(6295147/100000000000000),(16871/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((53/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((53/40)+(1/40)*x)) := (SharedCertificates.h67 (53/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-46395901085779/25000000000000),(-3494010545203/25000000000000),(2805858779/12500000000000),(-44830571/100000000000000),(5481/4000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((53/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((53/40)+(1/40)*x)) := (SharedCertificates.h67 (53/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-189477863806151/100000000000000),(-727971023213/5000000000000),(355045683/20000000000000),(40748197/100000000000000),(42183/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((53/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((53/40)+(1/40)*x)) := (SharedCertificates.h72 (53/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(271879894057767/100000000000000),(9989218839847/50000000000000),(-7000969613/10000000000000),(36670703/25000000000000),(741/312500000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((53/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((53/40)+(1/40)*x)) := (SharedCertificates.h72 (53/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(568091028895369/100000000000000),(43600625028131/100000000000000),(-5541583981/50000000000000),(-253798221/100000000000000),(464283/25000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((53/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((53/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((53/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(105343366975381/100000000000000),(81079486163/20000000000000),(-432280051/100000000000000),(10713/12500000000000),(8411/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((53/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5384691374806537/50000000000000),(19599691203803/100000000000000),(-10493561297/12500000000000),(179042593/100000000000000),(800573/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((53/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(37142332973/4000000000000),(-422481419/25000000000000),(1289223/12500000000000),(-23691/50000000000000),(337/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((53/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(5275056538551/100000000000000),(98814229249/25000000000000),(-156228031/20000000000000),(1029167/50000000000000),(18437/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((53/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((53/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((53/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (53/40) (1/40))

def c87 : Certificate := ⟨(23121387283237/100000000000000),(-33412409369/25000000000000),(772541257/100000000000000),(-4465557/100000000000000),(5193/20000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((53/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(2504816955683/100000000000000),(178199516633/100000000000000),(-103005501/10000000000000),(238163/4000000000000),(20123/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((53/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((53/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((53/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((53/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((53/40)+(1/40)*x)) := (SharedCertificates.h61 (53/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-35443883858451/100000000000000),(-2548356093353/100000000000000),(6412538993/50000000000000),(-31560039/50000000000000),(768129/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((53/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((53/40)+(1/40)*x)) := (SharedCertificates.h61 (53/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-17977620896101/50000000000000),(-655446429523/25000000000000),(330185879/3125000000000),(-2371547/6250000000000),(498547/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((53/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((53/40)+(1/40)*x)) := (SharedCertificates.h67 (53/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-88118899945339/50000000000000),(-12603709164597/100000000000000),(17016714413/25000000000000),(-93510549/25000000000000),(3193093/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((53/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((53/40)+(1/40)*x)) := (SharedCertificates.h67 (53/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-35950324238359/20000000000000),(-327593022901/2500000000000),(53164398369/100000000000000),(-37105541/20000000000000),(2552493/50000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((53/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((53/40)+(1/40)*x)) := (SharedCertificates.h72 (53/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(258503331260987/100000000000000),(1806240850303/10000000000000),(-128323331939/100000000000000),(839542433/100000000000000),(5959331/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((53/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((53/40)+(1/40)*x)) := (SharedCertificates.h72 (53/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(538961631238291/100000000000000),(39248062408081/100000000000000),(-163691284993/100000000000000),(246874057/50000000000000),(16813581/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((53/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((53/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((53/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(5253618749559/5000000000000),(365326176681/100000000000000),(-112135083/6250000000000),(8535321/100000000000000),(7163/6250000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((53/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(16806645241093/156250000000),(17738380833059/100000000000000),(-34595586089/25000000000000),(947697053/100000000000000),(344557/1562500000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((53/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(929691784163/100000000000000),(-1533175819/100000000000000),(226393/1562500000000),(-31383/25000000000000),(153/6250000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((53/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(5010682005413/100000000000000),(356622782247/100000000000000),(-2045475261/100000000000000),(1513769/12500000000000),(25157/10000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((53/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((53/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-10782141563609/10000000000000),(-981413128569/12500000000000),(31515749307/100000000000000),(-35519129/20000000000000),(19332383/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((53/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(75471698113207/100000000000000),(-1423994304023/100000000000000),(26867817057/100000000000000),(-101387989/20000000000000),(9748847/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((53/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-81374653310257/100000000000000),(-4390142411921/100000000000000),(106618346871/100000000000000),(-2145701371/100000000000000),(38578621/50000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((53/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((53/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((53/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((53/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((53/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((53/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((53/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((53/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((53/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((53/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (53/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((53/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((53/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(34332440683/100000000000000),(-2591127599/100000000000000),(122222999/100000000000000),(-4612189/100000000000000),(91087/50000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((53/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(144994351367827/100000000000000),(-1099069525797/100000000000000),(14787830047/100000000000000),(-226539891/100000000000000),(1502745911/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((53/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((53/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (53/40) (1/40))

def c134 : Certificate := ⟨(23009/1600),(153/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((53/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((53/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3584229390681/50000000000000),(-77080201951/100000000000000),(1326111/160000000000),(-8912037/100000000000000),(96873/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((53/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(103086917562723/100000000000000),(262506262753/100000000000000),(1657638739/100000000000000),(-17824083/100000000000000),(260367/10000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((53/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((53/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (53/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((53/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (53/40) (1/40))

def c140 : Certificate := ⟨(24808545165557/100000000000000),(-16156313173/100000000000000),(-5718753/6250000000000),(1223037/100000000000000),(161603/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((53/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(765819337771/100000000000000),(4039078293/6250000000000),(36600019/10000000000000),(-4892149/100000000000000),(641/97656250000)⟩
theorem h141 : c141.Valid (fun x => f141 ((53/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((53/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(5864792581/100000000000000),(247456341/25000000000000),(47370033/100000000000000),(398127/100000000000000),(1991/12500000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((53/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((53/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3514384177/5000000000000),(2371032709/20000000000000),(566392573/100000000000000),(587941/12500000000000),(191773/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((53/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-26803542252817/25000000000000),(-1130924895449/12500000000000),(-25613885187/50000000000000),(42833929/6250000000000),(91899519/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((53/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-215250481414999/100000000000000),(-18233644912641/100000000000000),(-54555837003/50000000000000),(131407571/10000000000000),(186017573/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((53/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(293192015230513/100000000000000),(24601979338631/100000000000000),(6375155929/5000000000000),(-400026483/20000000000000),(254312949/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((53/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(161271125161797/20000000000000),(68234398118353/100000000000000),(100562204421/25000000000000),(-2496987369/50000000000000),(347723013/50000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((53/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(816460759286849/100000000000000),(69943838475489/100000000000000),(60569628577/12500000000000),(-4272757653/100000000000000),(22578393/3125000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((53/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(101537503468123/100000000000000),(6512016537/5000000000000),(779370413/100000000000000),(-9386171/100000000000000),(166087/12500000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((53/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((53/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((53/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((53/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(166579104709731/312500000000),(13611435743521/20000000000000),(393598005931/100000000000000),(-507676849/10000000000000),(87862129/12500000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((53/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(187598558981/100000000000000),(-119757561/50000000000000),(-1079399/100000000000000),(21013/100000000000000),(631/25000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((53/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(1531668619067/100000000000000),(32314521523/25000000000000),(732683063/100000000000000),(-975963/10000000000000),(43731/3125000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((53/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((53/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((53/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (53/40) (1/40))

def c175 : Certificate := ⟨(2443429997701/10000000000000),(-9403525837/20000000000000),(-103213489/50000000000000),(2080503/50000000000000),(239949/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((53/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(377133348659/50000000000000),(31345086123/50000000000000),(27523597/10000000000000),(-554801/10000000000000),(669491/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((53/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((53/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(2844591253/50000000000000),(945702183/100000000000000),(43452603/100000000000000),(130699/50000000000000),(687/4000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((53/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((53/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(34092183427/50000000000000),(5663513423/50000000000000),(64944837/12500000000000),(3073777/100000000000000),(206419/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((53/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-105596823332549/100000000000000),(-548530995847/6250000000000),(-19260914171/50000000000000),(777097689/100000000000000),(46866401/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((53/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-6624723653777/3125000000000),(-4421411311333/25000000000000),(-41574634891/50000000000000),(1516857237/100000000000000),(189861863/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((53/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(72198424942379/25000000000000),(11934710880499/50000000000000),(46834021907/50000000000000),(-2213585089/100000000000000),(259717509/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((53/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(794158306885213/100000000000000),(33092882612653/50000000000000),(305462921117/100000000000000),(-2866855623/50000000000000),(709647539/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((53/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(803960175449539/100000000000000),(67818833650203/100000000000000),(95240334439/25000000000000),(-1050540177/20000000000000),(184751533/25000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((53/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(50757111288571/50000000000000),(5053041867/4000000000000),(593924543/100000000000000),(-5417311/50000000000000),(1356157/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((53/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((53/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((53/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((53/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(26646573812120541/50000000000000),(13203300725161/20000000000000),(297528590701/100000000000000),(-1158125963/20000000000000),(358807651/50000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((53/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(93820692207/50000000000000),(-232439417/100000000000000),(-151929/20000000000000),(22627/100000000000000),(323/12500000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((53/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(30171240067/2000000000000),(125387478009/100000000000000),(551096183/100000000000000),(-1384377/12500000000000),(1435733/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((53/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((53/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(4408162671059/100000000000000),(33580743567/10000000000000),(-243870133/50000000000000),(-13549469/100000000000000),(6729963/12500000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((53/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(41586440293/1250000000000),(95333794371/50000000000000),(-247850471/6250000000000),(64596769/100000000000000),(43519371/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((53/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((53/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((53/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((53/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((53/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((53/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (53/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((53/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((53/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((53/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (53/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((53/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(10847225239/25000000000000),(-29799153/10000000000000),(4270399/100000000000000),(-22301/50000000000000),(267/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((53/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(244316799719039/50000000000000),(-627123455343/50000000000000),(-119755559/50000000000000),(-31320923/50000000000000),(5785773/50000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((53/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((53/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((53/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((53/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (53/40) (1/40))

def c223 : Certificate := ⟨(17689/1600),(133/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((53/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1319051041/2560000),(8611617/640000),(155987/1280000),(273/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((53/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((53/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(513868013/250000000000),(-884074001/20000000000000),(7129629/10000000000000),(-102217/10000000000000),(7083/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((53/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(52954541990957/50000000000000),(7627450987/1562500000000),(461148079/20000000000000),(-4587109/25000000000000),(7309547/50000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((53/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((53/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (53/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((53/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (53/40) (1/40))

def c231 : Certificate := ⟨(24636058651117/100000000000000),(-29627967411/100000000000000),(-104312177/100000000000000),(1407379/100000000000000),(55743/6250000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((53/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(181970674441/12500000000000),(118511869643/100000000000000),(83449741/20000000000000),(-70369/1250000000000),(918237/25000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((53/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((53/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(5298132217/25000000000000),(138020383/4000000000000),(38149739/25000000000000),(825073/100000000000000),(3979/3125000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((53/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((53/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(63423329853/25000000000000),(20627710463/50000000000000),(227298641/12500000000000),(9488749/100000000000000),(1529207/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((53/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-101901731097183/50000000000000),(-16590760511183/100000000000000),(-29169198059/50000000000000),(197645949/25000000000000),(514245641/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((53/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-205290605512677/50000000000000),(-33666377343861/100000000000000),(-215923899/156250000000),(182610643/12500000000000),(130781819/12500000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((53/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(554492578087633/100000000000000),(22325189435833/50000000000000),(2340344247/2000000000000),(-242723/10000000000),(1419785569/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((53/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(153662577637697/10000000000000),(125744607411059/100000000000000),(495044248239/100000000000000),(-353285227/6250000000000),(3905882173/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((53/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(786646498963459/50000000000000),(4116897623813/3125000000000),(190848044677/25000000000000),(-2012936781/50000000000000),(4125288301/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((53/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(25733180829981/25000000000000),(240474248861/100000000000000),(493548183/50000000000000),(-10433967/100000000000000),(934153/12500000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((53/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((53/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((53/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((53/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(54032808318122279/100000000000000),(31278535211681/25000000000000),(466067564917/100000000000000),(-1174195571/20000000000000),(495674817/12500000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((53/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(92536371061/50000000000000),(-428539953/100000000000000),(-302039/50000000000000),(6301/25000000000000),(3437/25000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((53/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(727934123219/25000000000000),(118536990627/50000000000000),(209691321/25000000000000),(-139019/1250000000000),(7933069/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((53/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((53/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((53/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (53/40) (1/40))

def c259 : Certificate := ⟨(23939065391163/100000000000000),(-41962856197/50000000000000),(-4087363/4000000000000),(1225627/25000000000000),(2557853/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((53/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(1414579478449/100000000000000),(111900949857/100000000000000),(136245433/100000000000000),(-6536679/100000000000000),(92819/2500000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((53/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((53/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(625323469/3125000000000),(633171149/20000000000000),(5162913/4000000000000),(59993/50000000000000),(5113/4000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((53/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((53/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(119779043729/50000000000000),(18927959151/50000000000000),(384520613/25000000000000),(1141559/100000000000000),(766263/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((53/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-49509434560829/25000000000000),(-15665329410153/100000000000000),(-19009915703/100000000000000),(458454127/50000000000000),(129950841/25000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((53/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-79776731034099/20000000000000),(-15887735302599/50000000000000),(-56217101389/100000000000000),(362714007/20000000000000),(211493991/20000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((53/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(107794114574787/20000000000000),(42186021809623/100000000000000),(15558741933/100000000000000),(-128554669/5000000000000),(717982333/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((53/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(1492932619490203/100000000000000),(59347932673819/50000000000000),(191218677323/100000000000000),(-3430113489/50000000000000),(3947515581/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((53/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1527545889296209/100000000000000),(124195303619669/100000000000000),(20908964577/5000000000000),(-6501389679/100000000000000),(4169006567/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((53/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(51424584653953/50000000000000),(226967755459/100000000000000),(401563691/100000000000000),(-3238343/25000000000000),(1510669/20000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((53/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((53/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((53/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((53/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(26994665517758821/50000000000000),(2362362150027/2000000000000),(41678962289/25000000000000),(-1733715313/25000000000000),(2003368531/50000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((53/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(37044356017/20000000000000),(-81045813/20000000000000),(19663/6250000000000),(12177/50000000000000),(6957/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((53/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(2829347687769/100000000000000),(223846692221/100000000000000),(276089441/100000000000000),(-12973827/100000000000000),(8026693/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((53/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((53/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(5610573255731/20000000000000),(2180205906379/100000000000000),(-10852471/3125000000000),(-13642127/10000000000000),(39457129/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((53/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(2646496818741/12500000000000),(249193440397/20000000000000),(-4754182509/20000000000000),(172774167/50000000000000),(14577859/20000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((53/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((53/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((53/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((53/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((53/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((53/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (53/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((53/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(178524150685306333/20000000000000),(1532612128532049/25000000000000),(-45749615777077/100000000000000),0,(29009/25000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((53/40)+(1/40)*x)) := (SharedCertificates.h297 (53/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(5601483027/50000000000000),(-76941083/100000000000000),(275653/25000000000000),(-11517/100000000000000),(7/5000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((53/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(152089454116141/25000000000000),(114520904489/20000000000000),(799252363/10000000000000),(-25592003/100000000000000),(14460909/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((53/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((53/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (53/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((53/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (53/40) (1/40))

def c307 : Certificate := ⟨(1144185979375807/50000000000000),(11091229182759/50000000000000),0,0,(51/5000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((53/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (53/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((53/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (53/40) (1/40))

def c311 : Certificate := ⟨(2036628041248127/100000000000000),(2817541634481/100000000000000),0,0,(1019/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((53/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (53/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(2455038376539/50000000000000),(-849096239/12500000000000),(1174669/12500000000000),(-13001/100000000000000),(23/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((53/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(56180409785309/50000000000000),(933731889577/100000000000000),(-129175699/10000000000000),(446763/25000000000000),(867/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((53/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((53/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (53/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((53/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (53/40) (1/40))

def c316 : Certificate := ⟨(24250606569297/100000000000000),(-13728004469/25000000000000),(200307567/100000000000000),(-18267/2500000000000),(171/6250000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((53/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(2997573722811/100000000000000),(219648071501/100000000000000),(-801230271/100000000000000),(1461359/50000000000000),(11613/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((53/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((53/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(22463620559/25000000000000),(13168225747/100000000000000),(434417817/100000000000000),(-3344553/100000000000000),(2507/12500000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((53/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((53/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(214573375627/20000000000000),(156834527139/100000000000000),(513056219/10000000000000),(-41636743/100000000000000),(65137/25000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((53/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-419628161217921/100000000000000),(-30743672248159/100000000000000),(28165479551/25000000000000),(-10009617/2500000000000),(1762563/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((53/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-53243706617579/6250000000000),(-63344729424609/100000000000000),(163555904587/100000000000000),(-13953603/4000000000000),(6047859/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((53/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(141066196693041/12500000000000),(10099315270921/12500000000000),(-435880746979/100000000000000),(978337807/50000000000000),(8509727/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((53/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(636256182980453/20000000000000),(117765571943309/50000000000000),(-342968071013/50000000000000),(1555736607/100000000000000),(11394033/50000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((53/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(3338174890459373/100000000000000),(258726158789637/100000000000000),(101285791623/100000000000000),(-3439502317/100000000000000),(23056569/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((53/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(53042500963929/50000000000000),(452464368749/100000000000000),(-46721709/4000000000000),(2500883/100000000000000),(21641/50000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((53/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((53/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((53/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((53/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(27832299770711783/50000000000000),(582538327241/250000000000),(-776828434819/100000000000000),(929594131/50000000000000),(17860319/50000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((53/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(89823694793/50000000000000),(-752014679/100000000000000),(5655051/100000000000000),(-5021/12500000000000),(393/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((53/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(239877762021/4000000000000),(219845612627/50000000000000),(-9843287/625000000000),(6349557/100000000000000),(169899/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((53/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((53/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((53/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (53/40) (1/40))

def c344 : Certificate := ⟨(4575795619651/20000000000000),(-36656981467/25000000000000),(1142566443/100000000000000),(-8903201/100000000000000),(70081/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((53/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(1414014601163/50000000000000),(48875975289/25000000000000),(-761710963/50000000000000),(5935467/50000000000000),(55383/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((53/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((53/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(19994372923/25000000000000),(691113427/6250000000000),(296052119/100000000000000),(-660659/12500000000000),(19173/25000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((53/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((53/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((53/40)+(1/40)*x)) := (SharedCertificates.h144 (53/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(955206326663/100000000000000),(65877811643/50000000000000),(3495080417/100000000000000),(-63963987/100000000000000),(471883/50000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((53/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((53/40)+(1/40)*x)) := (SharedCertificates.h148 (53/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-19794853740589/5000000000000),(-13682476304353/50000000000000),(42724189419/20000000000000),(-103675029/6250000000000),(15698937/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((53/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((53/40)+(1/40)*x)) := (SharedCertificates.h151 (53/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-12547566586533/1562500000000),(-56288975400477/100000000000000),(96282758747/25000000000000),(-2583248589/100000000000000),(334041/800000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((53/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((53/40)+(1/40)*x)) := (SharedCertificates.h154 (53/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1066080916671609/100000000000000),(4506696901483/6250000000000),(-673439213847/100000000000000),(3006195251/50000000000000),(379789/625000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((53/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((53/40)+(1/40)*x)) := (SharedCertificates.h157 (53/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(2999579742086197/100000000000000),(2617531715829/1250000000000),(-1493906698271/100000000000000),(5172985273/50000000000000),(2346091/1562500000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((53/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((53/40)+(1/40)*x)) := (SharedCertificates.h160 (53/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(627817728909761/20000000000000),(228851616850533/100000000000000),(-956701509673/100000000000000),(1540351017/100000000000000),(268859821/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((53/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((53/40)+(1/40)*x)) := (SharedCertificates.h41 (53/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(13217004487043/12500000000000),(50258202143/12500000000000),(-2750791733/100000000000000),(4614149/25000000000000),(18639/6250000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((53/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((53/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((53/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((53/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((53/40)+(1/40)*x)) := (SharedCertificates.h167 (53/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(27742390430671699/50000000000000),(103650073514033/50000000000000),(-1556083090917/100000000000000),(558314237/5000000000000),(190824189/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((53/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(18022960251/10000000000000),(-673367049/100000000000000),(1892597/25000000000000),(-83441/100000000000000),(1293/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((53/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(2828783493253/50000000000000),(1528596761/390625000000),(-1513814759/50000000000000),(23923949/100000000000000),(804629/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((53/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((53/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(70901128864503/100000000000000),(1280565172779/25000000000000),(-4462020789/20000000000000),(110626503/50000000000000),(407563/5000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((53/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(53510285935473/100000000000000),(714057272213/25000000000000),(-70728929183/100000000000000),(750745749/50000000000000),(48969123/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((53/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((53/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(44788496887207/6250000000000),(15447442626953/25000000000000),(216293/10240000),(3657/10240000),(149414063/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((53/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(29929/1600),(173/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((53/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(5177717/64000),(89787/64000),(519/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((53/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(57975540434334691/100000000000000),(3002130793004557/50000000000000),(16461331784069/6250000000000),(79560177919/1250000000000),(23279337557/25000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((53/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(86243266773/50000000000000),(-3572728291/20000000000000),(266613501/25000000000000),(-48230069/100000000000000),(2213/78125000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((53/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(3945266323263/100000000000000),(169810315553/100000000000000),(-3459677323/50000000000000),(184485271/100000000000000),(142766337/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((53/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((53/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((53/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel6
