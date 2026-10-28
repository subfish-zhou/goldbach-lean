import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel10
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(61/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((61/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (61/40) (1/40)

def c3 : Certificate := ⟨(53447619047619/20000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((61/40)+(1/40)*x)) := (SharedCertificates.h2 (61/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((61/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-43952380952381/25000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((61/40)+(1/40)*x)) := (SharedCertificates.h4 (61/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(3721/1600),(61/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((61/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(140767989417989/50000000000000),(9230687830687/100000000000000),(75661375661/100000000000000),0,(3/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((61/40)+(1/40)*x)) := (SharedCertificates.h8 (61/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((61/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((61/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(226981/64000),(11163/64000),(183/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((61/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(431910822120949/12500000000000),(169932126736111/100000000000000),(696443142361/25000000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((61/40)+(1/40)*x)) := (SharedCertificates.h13 (61/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((61/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((61/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(13845841/2560000),(226981/640000),(11163/1280000),(61/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((61/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(755477435515873/50000000000000),(99079007936507/100000000000000),(2436369047619/100000000000000),(13313492063/50000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((61/40)+(1/40)*x)) := (SharedCertificates.h18 (61/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((61/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(51550067199707/6250000000000),(16901661376953/25000000000000),(226981/10240000),(3721/10240000),(149414063/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((61/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(2686713131978803/50000000000000),(440444775734227/100000000000000),(2888162463831/20000000000000),(118367314091/50000000000000),(389361981/20000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((61/40)+(1/40)*x)) := (SharedCertificates.h22 (61/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((61/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(25156432793457/2000000000000),(1933127519989/1562500000000),(1014099682617/20000000000000),(55415283203/50000000000000),(1371630863/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((61/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(141222090972793/5000000000000),(277813949454673/100000000000000),(11385817600599/100000000000000),(248870330067/100000000000000),(3080000733/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((61/40)+(1/40)*x)) := (SharedCertificates.h26 (61/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((61/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(239772250062637/12500000000000),(220118786942747/100000000000000),(10825514111937/100000000000000),(18486192131/6250000000000),(4896791999/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((61/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(91037336849179/20000000000000),(52234537536413/100000000000000),(1284455841059/50000000000000),(70188843773/100000000000000),(290504129/25000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((61/40)+(1/40)*x)) := (SharedCertificates.h30 (61/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((61/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((61/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((61/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((61/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((61/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (61/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((61/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((61/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (61/40) (1/40))

def c43 : Certificate := ⟨(10201/1600),(101/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((61/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((61/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(74689222811/100000000000000),(-92437157/6250000000000),(4393053/20000000000000),(-289971/100000000000000),(1847/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((61/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-261522738196923/25000000000000),(249358487053/100000000000000),(-2520147599/100000000000000),(6366621/25000000000000),(25787603/25000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((61/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((61/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (61/40) (1/40))

def c52 : Certificate := ⟨(58749999999999/50000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((61/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (61/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((61/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (61/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((61/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (61/40) (1/40))

def c56 : Certificate := ⟨(23952095808383/100000000000000),(-11952143617/25000000000000),(11928287/12500000000000),(-23809/12500000000000),(383/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((61/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(2095808383233/50000000000000),(191234297871/100000000000000),(-190852593/50000000000000),(380943/50000000000000),(1661/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((61/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((61/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((61/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((61/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((61/40)+(1/40)*x)) := (SharedCertificates.h61 (61/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-2986840689877/5000000000000),(-693367469227/25000000000000),(26733077/800000000000),(-1145107/50000000000000),(6299/12500000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((61/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((61/40)+(1/40)*x)) := (SharedCertificates.h61 (61/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-12237314606683/20000000000000),(-726942668751/25000000000000),(408133991/100000000000000),(2879651/50000000000000),(16201/25000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((61/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((61/40)+(1/40)*x)) := (SharedCertificates.h67 (61/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-59195576061343/20000000000000),(-6812646583723/50000000000000),(21409367921/100000000000000),(-41677181/100000000000000),(66447/50000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((61/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((61/40)+(1/40)*x)) := (SharedCertificates.h67 (61/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-305819432108587/100000000000000),(-2904706429023/20000000000000),(336286359/12500000000000),(35616523/100000000000000),(392793/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((61/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((61/40)+(1/40)*x)) := (SharedCertificates.h72 (61/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(85460196377511/20000000000000),(18885998824231/100000000000000),(-66572923939/100000000000000),(17467847/12500000000000),(239713/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((61/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((61/40)+(1/40)*x)) := (SharedCertificates.h72 (61/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(183212232031601/20000000000000),(43376752004389/100000000000000),(-3353619653/20000000000000),(-110288043/50000000000000),(1717211/100000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((61/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((61/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((61/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(108558930044101/100000000000000),(398500213527/100000000000000),(-429704043/100000000000000),(6387/5000000000000),(7847/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((61/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(5460449175871009/50000000000000),(1829044393221/10000000000000),(-79735584159/100000000000000),(86001711/50000000000000),(749033/50000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((61/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(457837793097/50000000000000),(-1533583817/100000000000000),(9253987/100000000000000),(-20559/50000000000000),(29/10000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((61/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(2097037099543/25000000000000),(191570881241/50000000000000),(-733988051/100000000000000),(468701/25000000000000),(34553/100000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((61/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((61/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((61/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (61/40) (1/40))

def c87 : Certificate := ⟨(5524861878453/25000000000000),(-3815512347/3125000000000),(337282859/50000000000000),(-3726883/100000000000000),(5177/25000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((61/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(966850828729/25000000000000),(162795193471/100000000000000),(-899420959/100000000000000),(621147/12500000000000),(17429/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((61/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((61/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((61/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((61/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((61/40)+(1/40)*x)) := (SharedCertificates.h61 (61/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-27520527456419/50000000000000),(-23546840691/1000000000000),(2854791939/25000000000000),(-1697001/3125000000000),(325513/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((61/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((61/40)+(1/40)*x)) := (SharedCertificates.h61 (61/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-3517019124443/6250000000000),(-2459802030173/100000000000000),(2423814249/25000000000000),(-34635329/100000000000000),(843447/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((61/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((61/40)+(1/40)*x)) := (SharedCertificates.h67 (61/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-1364472545357/500000000000),(-2316480523527/20000000000000),(2991805363/5000000000000),(-314070691/100000000000000),(2761153/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((61/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((61/40)+(1/40)*x)) := (SharedCertificates.h67 (61/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-70318040833543/25000000000000),(-6143930454883/50000000000000),(24436223193/50000000000000),(-85982223/50000000000000),(856277/20000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((61/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((61/40)+(1/40)*x)) := (SharedCertificates.h72 (61/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(197599709548729/50000000000000),(8080188305909/50000000000000),(-110023332237/100000000000000),(345608801/50000000000000),(5073043/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((61/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((61/40)+(1/40)*x)) := (SharedCertificates.h72 (61/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(842722607001767/100000000000000),(18361847914159/50000000000000),(-30376174691/20000000000000),(951841/195312500000),(13875239/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((61/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((61/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((61/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(53942187356917/50000000000000),(338182280359/100000000000000),(-40084691/2500000000000),(7394279/100000000000000),(96887/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((61/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(2722441334284213/25000000000000),(3138929453049/20000000000000),(-58883369643/50000000000000),(24278849/3125000000000),(18315523/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((61/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(459146716683/50000000000000),(-1323471267/100000000000000),(739891/6250000000000),(-9689/10000000000000),(1917/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((61/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(7738666361587/100000000000000),(81519523929/25000000000000),(-1780975991/100000000000000),(2003253/20000000000000),(204683/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((61/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((61/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-16870115017467/10000000000000),(-7378871190689/100000000000000),(13835445841/50000000000000),(-18053641/12500000000000),(10073433/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((61/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(65573770491803/100000000000000),(-33593120129/3125000000000),(3524524079/20000000000000),(-288895417/100000000000000),(2407463/50000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((61/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-110623705032571/100000000000000),(-3025100698279/100000000000000),(67736661731/100000000000000),(-602572351/50000000000000),(2488133/5000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((61/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((61/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((61/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((61/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((61/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((61/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((61/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((61/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((61/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((61/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (61/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((61/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((61/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1222837741/6250000000000),(-1282977303/100000000000000),(13145259/25000000000000),(-1723969/100000000000000),(29089/50000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((61/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(137049358842589/100000000000000),(-897820466363/100000000000000),(2151128747/20000000000000),(-31771649/25000000000000),(199513579/25000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((61/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((61/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (61/40) (1/40))

def c134 : Certificate := ⟨(25521/1600),(161/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((61/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((61/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3300330033003/50000000000000),(-65353069961/100000000000000),(323530049/50000000000000),(-800817/12500000000000),(16017/25000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((61/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(13160581683167/12500000000000),(285960526737/100000000000000),(1294120187/100000000000000),(-6406539/50000000000000),(240471/12500000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((61/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((61/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (61/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((61/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (61/40) (1/40))

def c140 : Certificate := ⟨(3084251992549/12500000000000),(-17409478831/100000000000000),(-66503181/100000000000000),(441291/50000000000000),(23651/20000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((61/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1303936238431/100000000000000),(69637915323/100000000000000),(266012721/100000000000000),(-882583/25000000000000),(60689/12500000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((61/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((61/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(8501248569/50000000000000),(1816068027/100000000000000),(11086333/20000000000000),(34803/12500000000000),(17571/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((61/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((61/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(50896640553/25000000000000),(1357610951/6250000000000),(661114591/100000000000000),(1624081/50000000000000),(105581/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((61/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-182548418741379/100000000000000),(-2437220783421/25000000000000),(-3721749227/10000000000000),(98959963/20000000000000),(16994243/25000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((61/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-91870615436333/25000000000000),(-19752858423729/100000000000000),(-82243375247/100000000000000),(237384661/25000000000000),(2768069/2000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((61/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(497223714807359/100000000000000),(1643570349669/6250000000000),(21652366873/25000000000000),(-1443640779/100000000000000),(188280971/100000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((61/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(275123306111199/20000000000000),(576632539601/781250000000),(300078137669/100000000000000),(-3612959677/100000000000000),(516626729/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((61/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(1405007375240083/100000000000000),(38480278062037/50000000000000),(397255691329/100000000000000),(-3087578851/100000000000000),(546747669/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((61/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(51312437487/50000000000),(141091898673/100000000000000),(587457107/100000000000000),(-42389/625000000000),(197719/20000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((61/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((61/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((61/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((61/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(10774512598409889/20000000000000),(36739306448273/50000000000000),(28965708267/10000000000000),(-3678315063/100000000000000),(104968289/20000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((61/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(580072643/312500000000),(-253177831/100000000000000),(-26109/4000000000000),(597/4000000000000),(37/2000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((61/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(81500634159/3125000000000),(69649757517/50000000000000),(533381007/100000000000000),(-7029671/100000000000000),(530247/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((61/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((61/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((61/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (61/40) (1/40))

def c175 : Certificate := ⟨(24046903365973/100000000000000),(-4960730791/10000000000000),(-24432401/20000000000000),(1468951/50000000000000),(344679/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((61/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(254159102407/20000000000000),(16535769303/25000000000000),(162882673/100000000000000),(-979301/25000000000000),(248001/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((61/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((61/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(8074606167/50000000000000),(1681086513/100000000000000),(23944439/50000000000000),(115911/100000000000000),(4549/25000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((61/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((61/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(48345025269/25000000000000),(125680929/625000000000),(571172943/100000000000000),(165053/12500000000000),(109137/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((61/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-35581782843851/20000000000000),(-4629823679257/50000000000000),(-569567503/2500000000000),(54882831/10000000000000),(3472169/5000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((61/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-358083601867209/100000000000000),(-9377703616461/50000000000000),(-13077767117/25000000000000),(6753807/625000000000),(35357/25000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((61/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(484705761791613/100000000000000),(24989894339973/100000000000000),(12264100691/25000000000000),(-772756901/50000000000000),(96268543/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((61/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(335123726676043/25000000000000),(70088400834607/100000000000000),(23621100003/12500000000000),(-1019634953/25000000000000),(52783063/10000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((61/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(684202592931829/50000000000000),(14600976147891/20000000000000),(136456869371/50000000000000),(-1921720281/50000000000000),(559211539/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((61/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(25639435059101/25000000000000),(133967240937/100000000000000),(23353389/6250000000000),(-7718497/100000000000000),(5051/500000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((61/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((61/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((61/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((61/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(10767519301986569/20000000000000),(3489145000451/5000000000000),(179969215061/100000000000000),(-2055725871/50000000000000),(536260597/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((61/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(185743804483/100000000000000),(-48151263/20000000000000),(-154423/50000000000000),(15389/100000000000000),(379/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((61/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(508345570593/20000000000000),(132307521043/100000000000000),(65386047/20000000000000),(-7810899/100000000000000),(33971/3125000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((61/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((61/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(7057696816173/100000000000000),(326000208693/100000000000000),(-705603953/100000000000000),(-5394511/100000000000000),(23178607/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((61/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(1156999478061/25000000000000),(137901810417/100000000000000),(-1361688267/50000000000000),(10277033/25000000000000),(258157/800000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((61/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((61/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((61/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((61/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((61/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((61/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (61/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((61/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((61/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((61/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (61/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((61/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(20628706237/50000000000000),(-237261791/100000000000000),(337513/10000000000000),(-30973/100000000000000),(349/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((61/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(59819219043113/12500000000000),(-634681577021/50000000000000),(-161007793/10000000000000),(-26304047/50000000000000),(1567011/20000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((61/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((61/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((61/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((61/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (61/40) (1/40))

def c223 : Certificate := ⟨(19881/1600),(141/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((61/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1615152321/2560000),(9912441/640000),(169283/1280000),(281/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((61/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((61/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(174274853227/100000000000000),(-3450987193/100000000000000),(10250457/20000000000000),(-338299/50000000000000),(8613/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((61/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(21990658881369/20000000000000),(65238614603/12500000000000),(1934749711/100000000000000),(-6478481/50000000000000),(2730403/25000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((61/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((61/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (61/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((61/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (61/40) (1/40))

def c231 : Certificate := ⟨(1219651132999/5000000000000),(-15527300559/50000000000000),(-37792989/50000000000000),(126719/12500000000000),(81681/12500000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((61/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(606977340019/25000000000000),(124218404469/100000000000000),(75585977/25000000000000),(-1013753/25000000000000),(2743857/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((61/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((61/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(58947438607/100000000000000),(3015910269/50000000000000),(5280731/3125000000000),(554229/100000000000000),(149257/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((61/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((61/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(28180275301/4000000000000),(71942505049/100000000000000),(1002126733/50000000000000),(246893/4000000000000),(894853/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((61/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-339890205622097/100000000000000),(-8693977399819/50000000000000),(-42187989797/100000000000000),(71316267/12500000000000),(192089617/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((61/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-688066846937561/100000000000000),(-35625523223797/100000000000000),(-54153628873/50000000000000),(1058061233/100000000000000),(789179963/100000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((61/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(918039464248883/100000000000000),(11526106162173/25000000000000),(16859754451/25000000000000),(-874919403/50000000000000),(1061068311/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((61/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(257159399416149/10000000000000),(13268907230879/10000000000000),(379144278707/100000000000000),(-102857703/2500000000000),(2938436939/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((61/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(1337088385327299/50000000000000),(8953828222697/6250000000000),(340535137437/50000000000000),(-1460907117/50000000000000),(799555899/25000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((61/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(104914766158759/100000000000000),(63617157369/25000000000000),(96708901/12500000000000),(-1511159/20000000000000),(5636971/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((61/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((61/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((61/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((61/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(27530385597313287/50000000000000),(32888843608029/25000000000000),(345352874691/100000000000000),(-2149352409/50000000000000),(3008635087/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((61/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(90808753519/50000000000000),(-105941/24414062500),(-20471/20000000000000),(3429/20000000000000),(10049/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((61/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(1214193296163/25000000000000),(248583342427/100000000000000),(30627297/5000000000000),(-993759/12500000000000),(245691/4000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((61/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((61/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((61/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (61/40) (1/40))

def c259 : Certificate := ⟨(23263394399773/100000000000000),(-84734864407/100000000000000),(-5478281/100000000000000),(653547/20000000000000),(902893/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((61/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(1157737066817/50000000000000),(14122477401/12500000000000),(7304373/100000000000000),(-2178491/50000000000000),(172949/6250000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((61/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((61/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(10722840927/20000000000000),(5232036979/100000000000000),(127982657/100000000000000),(-37053/20000000000000),(18031/12500000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((61/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((61/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(640887609539/100000000000000),(62421004359/100000000000000),(1518034949/100000000000000),(-2499883/100000000000000),(345751/20000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((61/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-20259471195121/6250000000000),(-494218914789/3125000000000),(-916892563/100000000000000),(122322261/20000000000000),(387437279/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((61/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-131167680491933/20000000000000),(-6473353511487/20000000000000),(-9978948227/50000000000000),(249209759/20000000000000),(397503977/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((61/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(438135886440849/50000000000000),(21003410611499/50000000000000),(-34265756679/100000000000000),(-1644923957/100000000000000),(535118947/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((61/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(2451537686557111/100000000000000),(15073934689119/12500000000000),(13599853437/25000000000000),(-1171685737/25000000000000),(1480318827/50000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((61/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1272388641166369/50000000000000),(25950564959787/20000000000000),(14151750291/5000000000000),(-608120029/12500000000000),(803197549/25000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((61/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(104684562471903/100000000000000),(46238335079/20000000000000),(142591403/100000000000000),(-8899229/100000000000000),(709827/12500000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((61/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((61/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((61/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((61/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(27470857836076209/50000000000000),(59805643652037/50000000000000),(1801441109/6250000000000),(-2352526929/50000000000000),(3028309849/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((61/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(182011061679/100000000000000),(-396248591/100000000000000),(76717/10000000000000),(3531/25000000000000),(2029/20000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((61/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(4631776148939/100000000000000),(226080849849/100000000000000),(10267023/50000000000000),(-8621439/100000000000000),(6171531/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((61/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((61/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(45407808878997/100000000000000),(13444244713/625000000000),(-3148357373/100000000000000),(-99973881/100000000000000),(59914997/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((61/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(2977561237967/10000000000000),(230604728621/25000000000000),(-4296529547/25000000000000),(108091499/50000000000000),(599209/1250000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((61/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((61/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((61/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((61/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((61/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((61/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (61/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((61/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(938736366129824367/100000000000000),(5398454661694979/100000000000000),(-45749615777077/100000000000000),0,(24379/20000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((61/40)+(1/40)*x)) := (SharedCertificates.h297 (61/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(5326309047/50000000000000),(-61260731/100000000000000),(435727/50000000000000),(-3999/50000000000000),(93/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((61/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(4907514682407/800000000000),(2177130651/312500000000),(7580463427/100000000000000),(-9693221/100000000000000),(5037893/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((61/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((61/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (61/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((61/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (61/40) (1/40))

def c307 : Certificate := ⟨(616457906418941/25000000000000),(11091229182759/50000000000000),0,0,(103/10000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((61/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (61/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((61/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (61/40) (1/40))

def c311 : Certificate := ⟨(2059168374323977/100000000000000),(2817541634481/100000000000000),0,0,(1029/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((61/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (61/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(48563294409/1000000000000),(-6644872057/100000000000000),(4546059/50000000000000),(-12441/100000000000000),(11/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((61/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(23949781440143/20000000000000),(228350474913/25000000000000),(-1249799657/100000000000000),(1710081/100000000000000),(3359/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((61/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((61/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (61/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((61/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (61/40) (1/40))

def c316 : Certificate := ⟨(23823766610113/100000000000000),(-518421211/1000000000000),(183747059/100000000000000),(-130253/20000000000000),(297/12500000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((61/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(2352466779773/50000000000000),(103684242199/50000000000000),(-734988237/100000000000000),(2605059/100000000000000),(10439/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((61/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((61/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(221363997997/100000000000000),(4878274707/25000000000000),(180427733/50000000000000),(-43799/1562500000000),(17273/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((61/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((61/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(1317768958951/50000000000000),(23140295093/10000000000000),(263664721/6250000000000),(-17297579/50000000000000),(221749/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((61/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-658566698028467/100000000000000),(-7253808796397/25000000000000),(103557323077/100000000000000),(-179609973/50000000000000),(1569189/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((61/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-21068226910319/1562500000000),(-759924786869/1250000000000),(155340943921/100000000000000),(-167734907/50000000000000),(5339059/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((61/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(27311869865839/1562500000000),(74180462765911/100000000000000),(-391819008761/100000000000000),(430248781/25000000000000),(7574571/100000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((61/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1255605144677743/25000000000000),(112425883791849/50000000000000),(-324596434751/50000000000000),(47002881/3125000000000),(498183/2500000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((61/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(5412783340141933/100000000000000),(259724996030787/100000000000000),(25889169011/100000000000000),(-2859191849/100000000000000),(41566753/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((61/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(109631231117089/100000000000000),(54281258453/12500000000000),(-69320063/6250000000000),(1203491/50000000000000),(38151/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((61/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((61/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((61/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((61/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(57479950852451677/100000000000000),(220939862510253/100000000000000),(-732824112357/100000000000000),(451145343/25000000000000),(30953491/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((61/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(173973704773/100000000000000),(-668715367/100000000000000),(4788417/100000000000000),(-16197/50000000000000),(61/20000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((61/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(470840985409/5000000000000),(207828541919/50000000000000),(-1432593977/100000000000000),(5535931/100000000000000),(76911/50000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((61/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((61/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((61/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (61/40) (1/40))

def c344 : Certificate := ⟨(10887393997189/50000000000000),(-64962247251/50000000000000),(953000179/100000000000000),(-1398057/20000000000000),(51801/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((61/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(2150141337081/50000000000000),(34646531867/20000000000000),(-635333453/50000000000000),(9320379/100000000000000),(89527/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((61/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((61/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(23115538847/12500000000000),(1489898807/10000000000000),(47702751/25000000000000),(-720163/20000000000000),(56691/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((61/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((61/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((61/40)+(1/40)*x)) := (SharedCertificates.h144 (61/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(1101593596559/50000000000000),(22108220129/12500000000000),(111320047/5000000000000),(-21608511/50000000000000),(13813/2000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((61/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((61/40)+(1/40)*x)) := (SharedCertificates.h148 (61/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-120388966221107/20000000000000),(-12120574969729/50000000000000),(1392714863/781250000000),(-130489669/10000000000000),(3162577/25000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((61/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((61/40)+(1/40)*x)) := (SharedCertificates.h151 (61/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-614982239022703/50000000000000),(-25295173811659/50000000000000),(329107865269/100000000000000),(-2105082101/100000000000000),(33012783/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((61/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((61/40)+(1/40)*x)) := (SharedCertificates.h154 (61/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(400679220051159/25000000000000),(62388345716137/100000000000000),(-273532221639/50000000000000),(919228239/20000000000000),(1899639/4000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((61/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((61/40)+(1/40)*x)) := (SharedCertificates.h157 (61/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(4584218164185409/100000000000000),(93676798298233/50000000000000),(-635006885683/50000000000000),(1678596391/20000000000000),(118457723/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((61/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((61/40)+(1/40)*x)) := (SharedCertificates.h160 (61/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(1227391371697651/25000000000000),(213890486880537/100000000000000),(-455406833187/50000000000000),(2201337303/100000000000000),(209880603/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((61/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((61/40)+(1/40)*x)) := (SharedCertificates.h41 (61/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(1087854896591/1000000000000),(18068215337/5000000000000),(-293815351/12500000000000),(15039943/100000000000000),(47149/20000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((61/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((61/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((61/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((61/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((61/40)+(1/40)*x)) := (SharedCertificates.h167 (61/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(57049013263679937/100000000000000),(184400261950853/100000000000000),(-131500077509/10000000000000),(450711523/5000000000000),(236757/160000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((61/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(175287869639/100000000000000),(-141646311/25000000000000),(587183/10000000000000),(-59737/100000000000000),(881/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((61/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4302936375163/50000000000000),(17355360211/5000000000000),(-2520136471/100000000000000),(18645671/100000000000000),(608647/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((61/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((61/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(5527914241039/5000000000000),(4804656998303/100000000000000),(-17567359741/100000000000000),(176875593/100000000000000),(6783161/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((61/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(18124308987013/25000000000000),(490528868787/25000000000000),(-43685407621/100000000000000),(832138217/100000000000000),(29037677/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((61/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((61/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(341413559814453/25000000000000),(25768106689453/25000000000000),(63257/2048000),(4697/10240000),(168945313/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((61/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(32761/1600),(181/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((61/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(5929741/64000),(98283/64000),(543/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((61/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(63265436987116073/50000000000000),(465883369070169/4000000000000),(228024463764251/50000000000000),(9888981916137/100000000000000),(130522541647/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((61/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(39516047293/50000000000000),(-3637426319/50000000000000),(192396993/50000000000000),(-1922047/12500000000000),(394269/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((61/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2470297312709/50000000000000),(43702095337/50000000000000),(-1873492103/50000000000000),(92018591/100000000000000),(25428971/25000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((61/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((61/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((61/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel10

namespace Hf4Quad.Panel11
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(63/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((63/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (63/40) (1/40)

def c3 : Certificate := ⟨(69/25),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((63/40)+(1/40)*x)) := (SharedCertificates.h2 (63/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((63/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-184571428571429/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((63/40)+(1/40)*x)) := (SharedCertificates.h4 (63/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(3969/1600),(63/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((63/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(3003/1000),(9533333333333/100000000000000),(75661375661/100000000000000),0,(1/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((63/40)+(1/40)*x)) := (SharedCertificates.h8 (63/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((63/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((63/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(250047/64000),(11907/64000),(189/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((63/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(48722121/1280000),(2320101/1280000),(36827/1280000),(608912037/4000000000000),(1/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((63/40)+(1/40)*x)) := (SharedCertificates.h13 (63/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((63/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((63/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(15752961/2560000),(250047/640000),(11907/1280000),(63/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((63/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(2750517/160000),(43659/40000),(2079/80000),(11/40000),(21825397/20000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((63/40)+(1/40)*x)) := (SharedCertificates.h18 (63/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((63/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(969176311523437/100000000000000),(19229688720703/25000000000000),(250047/10240000),(3969/10240000),(308593751/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((63/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(1262800838496093/20000000000000),(125277860961913/25000000000000),(15908299804687/100000000000000),(15782043457/6250000000000),(251303893/12500000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((63/40)+(1/40)*x)) := (SharedCertificates.h22 (63/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((63/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(1526452690649413/100000000000000),(72688223364257/50000000000000),(576890661621/10000000000000),(61046630859/50000000000000),(292548829/20000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((63/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(214228347192993/6250000000000),(81610798930663/25000000000000),(12954095068357/100000000000000),(54832148437/20000000000000),(65691917/2000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((63/40)+(1/40)*x)) := (SharedCertificates.h26 (63/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((63/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(96166519510913/4000000000000),(66782305215911/25000000000000),(12720439088743/100000000000000),(336519552611/100000000000000),(5392722177/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((63/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(570511693130217/100000000000000),(63390188125579/100000000000000),(3018580386931/100000000000000),(9982077999/12500000000000),(255940307/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((63/40)+(1/40)*x)) := (SharedCertificates.h30 (63/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((63/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((63/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((63/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((63/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((63/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (63/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((63/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((63/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (63/40) (1/40))

def c43 : Certificate := ⟨(10609/1600),(103/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((63/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((63/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(17954207793/25000000000000),(-1394501577/100000000000000),(812331/4000000000000),(-262891/100000000000000),(1641/50000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((63/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-261400529199927/25000000000000),(239575383081/100000000000000),(-593338667/25000000000000),(11756373/50000000000000),(95275069/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((63/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((63/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (63/40) (1/40))

def c52 : Certificate := ⟨(23833333333333/20000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((63/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (63/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((63/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (63/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((63/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (63/40) (1/40))

def c56 : Certificate := ⟨(11928429423459/50000000000000),(-47429142837/100000000000000),(9429253/10000000000000),(-187461/100000000000000),(47/12500000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((63/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(182902584493/4000000000000),(189716571347/100000000000000),(-377170123/100000000000000),(749841/100000000000000),(1641/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((63/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((63/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((63/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((63/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((63/40)+(1/40)*x)) := (SharedCertificates.h61 (63/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-8158800675073/12500000000000),(-69003273813/2500000000000),(1663897623/50000000000000),(-2322567/100000000000000),(24777/50000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((63/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((63/40)+(1/40)*x)) := (SharedCertificates.h61 (63/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-67000436032219/100000000000000),(-1453034772639/50000000000000),(44230197/10000000000000),(5630369/100000000000000),(64141/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((63/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((63/40)+(1/40)*x)) := (SharedCertificates.h67 (63/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-323143161090863/100000000000000),(-2708030566391/20000000000000),(10580771639/50000000000000),(-40933869/100000000000000),(131869/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((63/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((63/40)+(1/40)*x)) := (SharedCertificates.h67 (63/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-16742772634697/5000000000000),(-14512348356903/100000000000000),(2900419599/100000000000000),(34432707/100000000000000),(77199/20000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((63/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((63/40)+(1/40)*x)) := (SharedCertificates.h72 (63/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(464807802361801/100000000000000),(1862137720223/10000000000000),(-65739594357/100000000000000),(69017849/50000000000000),(29997/12500000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((63/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((63/40)+(1/40)*x)) := (SharedCertificates.h72 (63/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(250686460690123/25000000000000),(43307063843411/100000000000000),(-722730091/4000000000000),(-5321139/2500000000000),(421071/25000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((63/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((63/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((63/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(27338553173997/25000000000000),(24798935519/6250000000000),(-428909167/100000000000000),(137147/100000000000000),(3857/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((63/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(10957161669737287/100000000000000),(1123347407157/6250000000000),(-39354453749/50000000000000),(17022093/10000000000000),(368389/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((63/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(182529021683/20000000000000),(-748527801/50000000000000),(9011523/100000000000000),(-19857/50000000000000),(139/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((63/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(2287877720947/25000000000000),(47528517119/12500000000000),(-361433587/50000000000000),(916181/50000000000000),(849/2500000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((63/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((63/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((63/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (63/40) (1/40))

def c87 : Certificate := ⟨(21857923497267/100000000000000),(-14930275613/12500000000000),(163172411/25000000000000),(-3566611/100000000000000),(19601/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((63/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(167577413479/4000000000000),(159256273203/100000000000000),(-43512643/5000000000000),(4755479/100000000000000),(33647/100000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((63/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((63/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((63/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((63/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((63/40)+(1/40)*x)) := (SharedCertificates.h61 (63/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-14926294206053/25000000000000),(-2309651087873/100000000000000),(693705661/6250000000000),(-13084063/25000000000000),(625441/100000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((63/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((63/40)+(1/40)*x)) := (SharedCertificates.h61 (63/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-61153404493527/100000000000000),(-1210716701599/50000000000000),(9489859403/100000000000000),(-16916223/50000000000000),(101237/12500000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((63/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((63/40)+(1/40)*x)) := (SharedCertificates.h67 (63/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-147911227962933/50000000000000),(-11346774143799/100000000000000),(28995588189/50000000000000),(-150511633/50000000000000),(2664279/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((63/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((63/40)+(1/40)*x)) := (SharedCertificates.h67 (63/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-76413441022879/25000000000000),(-12094420708403/100000000000000),(11962789197/25000000000000),(-42115567/25000000000000),(1025901/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((63/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((63/40)+(1/40)*x)) := (SharedCertificates.h72 (63/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(42708554358073/10000000000000),(15728447957757/100000000000000),(-105973020091/100000000000000),(659190387/100000000000000),(121907/2500000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((63/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((63/40)+(1/40)*x)) := (SharedCertificates.h72 (63/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(183113273225703/20000000000000),(1806100236311/5000000000000),(-74484405559/50000000000000),(19328453/4000000000000),(6624869/50000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((63/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((63/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((63/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(13569298044797/12500000000000),(331856423577/100000000000000),(-1559797477/100000000000000),(1784387/25000000000000),(23257/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((63/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5460344852562103/50000000000000),(15232753869063/100000000000000),(-56608403689/50000000000000),(740072491/100000000000000),(1751151/10000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((63/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(3662772323/400000000000),(-319314249/25000000000000),(1409343/12500000000000),(-91023/100000000000000),(1807/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((63/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(8383777864313/100000000000000),(319072562441/100000000000000),(-344448033/20000000000000),(4783367/50000000000000),(97369/50000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((63/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((63/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-91674675168543/50000000000000),(-908736585057/12500000000000),(2682527183/10000000000000),(-137520923/100000000000000),(20017799/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((63/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(63492063492063/100000000000000),(-1007810531621/100000000000000),(3199398513/20000000000000),(-253920517/100000000000000),(819099/20000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((63/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-29103071482077/25000000000000),(-22143926513/800000000000),(3810517547/6250000000000),(-13188317/1250000000000),(87793/195312500000)⟩
theorem h115 : c115.Valid (fun x => f115 ((63/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((63/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((63/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((63/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((63/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((63/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((63/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((63/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((63/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((63/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (63/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((63/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((63/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(859836671/5000000000000),(-1091856091/100000000000000),(21663811/50000000000000),(-1375481/100000000000000),(44787/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((63/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(67647875798051/50000000000000),(-856267945989/100000000000000),(2006731647/20000000000000),(-57010729/50000000000000),(138069103/20000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((63/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((63/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (63/40) (1/40))

def c134 : Certificate := ⟨(26169/1600),(163/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((63/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((63/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(1294498381877/20000000000000),(-15709931819/25000000000000),(610094439/100000000000000),(-5923247/100000000000000),(58073/100000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((63/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(21172330097087/20000000000000),(72746803027/25000000000000),(1220188869/100000000000000),(-2369299/20000000000000),(895473/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((63/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((63/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (63/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((63/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (63/40) (1/40))

def c140 : Certificate := ⟨(24638937894327/100000000000000),(-17665171959/100000000000000),(-30704821/50000000000000),(81631/10000000000000),(21961/20000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((63/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(45132763209/3125000000000),(70660687833/100000000000000),(245638567/100000000000000),(-816311/25000000000000),(113021/25000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((63/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((63/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(2607316883/12500000000000),(1020515869/50000000000000),(5702459/10000000000000),(252823/100000000000000),(17729/100000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((63/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((63/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3121249033/1250000000000),(24403948149/100000000000000),(679661039/100000000000000),(73433/2500000000000),(106489/50000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((63/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-101095586444563/50000000000000),(-9891967403301/100000000000000),(-3436172603/10000000000000),(457708627/100000000000000),(63296937/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((63/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-203654850588953/50000000000000),(-20070726849937/100000000000000),(-38380729577/50000000000000),(175780417/20000000000000),(32266449/25000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((63/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(275076539400081/50000000000000),(26626685823289/100000000000000),(78279598773/100000000000000),(-83416711/6250000000000),(35070027/20000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((63/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(76220321049267/5000000000000),(74967019664281/100000000000000),(279217034709/100000000000000),(-3345027641/100000000000000),(481579029/100000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((63/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(156049327520327/10000000000000),(39256727173801/50000000000000),(1517676617/400000000000),(-2861789217/100000000000000),(512031259/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((63/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(2572733884511/2500000000000),(35840601851/25000000000000),(137075431/25000000000000),(-1255533/20000000000000),(921897/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((63/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((63/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((63/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((63/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(54020649978778507/100000000000000),(18648553594437/25000000000000),(53683064111/20000000000000),(-3406594883/100000000000000),(122467399/25000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((63/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(185114396141/100000000000000),(-255614529/100000000000000),(-70853/12500000000000),(6863/50000000000000),(1719/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((63/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(2888697703213/100000000000000),(141350859369/100000000000000),(492822429/100000000000000),(-259931/4000000000000),(993349/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((63/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((63/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((63/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (63/40) (1/40))

def c175 : Certificate := ⟨(23947223110233/100000000000000),(-50061686847/100000000000000),(-105268337/100000000000000),(2696987/100000000000000),(7961/2500000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((63/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1403702519689/100000000000000),(13349783159/20000000000000),(140357781/100000000000000),(-224749/6250000000000),(2887/625000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((63/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((63/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(19703807637/100000000000000),(74956497/4000000000000),(48494589/100000000000000),(4321/5000000000000),(18203/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((63/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((63/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(47178505191/20000000000000),(2801004579/12500000000000),(144504171/25000000000000),(966031/100000000000000),(218271/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((63/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-19651504152713/10000000000000),(-4672188106711/50000000000000),(-19626687491/100000000000000),(125965027/25000000000000),(64671699/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((63/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-79159038420481/20000000000000),(-18952035326551/100000000000000),(-46088772949/100000000000000),(497399353/50000000000000),(131885887/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((63/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(106973936599183/20000000000000),(12584056692083/50000000000000),(40184988967/100000000000000),(-1413621507/100000000000000),(35864429/20000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((63/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(370348906222679/25000000000000),(70796666740797/100000000000000),(8274496089/5000000000000),(-187635581/5000000000000),(246017961/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((63/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(1515476421099757/100000000000000),(74051541811041/100000000000000),(62673041361/25000000000000),(-3568015797/100000000000000),(523488671/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((63/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(20565421769403/20000000000000),(27074348803/20000000000000),(329210151/100000000000000),(-1776387/25000000000000),(942043/100000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((63/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((63/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((63/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((63/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(10795569995025843/20000000000000),(70454793150423/100000000000000),(15630816169/10000000000000),(-756117193/20000000000000),(500469839/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((63/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(9263058833/5000000000000),(-241812853/100000000000000),(-4417/2000000000000),(3491/25000000000000),(1759/100000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((63/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(1403794724867/50000000000000),(133524140923/100000000000000),(282022179/100000000000000),(-1792069/25000000000000),(1017513/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((63/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((63/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(7706834516651/100000000000000),(20194919787/6250000000000),(-366894349/50000000000000),(-4039981/100000000000000),(44086063/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((63/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(244661413227/5000000000000),(127484450779/100000000000000),(-2489460297/100000000000000),(1478007/4000000000000),(29669881/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((63/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((63/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((63/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((63/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((63/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((63/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (63/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((63/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((63/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((63/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (63/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((63/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(40796147007/100000000000000),(-28015281/12500000000000),(3197247/100000000000000),(-14183/50000000000000),(79/25000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((63/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(238004084199041/50000000000000),(-1276427812177/100000000000000),(-192062303/10000000000000),(-50968429/100000000000000),(1429693/20000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((63/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((63/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((63/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((63/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (63/40) (1/40))

def c223 : Certificate := ⟨(20449/1600),(143/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((63/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(1695815121/2560000),(10254387/640000),(172667/1280000),(283/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((63/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((63/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(41893151517/25000000000000),(-813459253/25000000000000),(1895439/4000000000000),(-613411/100000000000000),(3827/50000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((63/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(111004749701363/100000000000000),(264748321613/50000000000000),(1860138847/100000000000000),(-11931057/100000000000000),(10197697/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((63/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((63/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (63/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((63/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (63/40) (1/40))

def c231 : Certificate := ⟨(24330619067701/100000000000000),(-31345090619/100000000000000),(-69734497/100000000000000),(187599/20000000000000),(303529/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((63/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(334690466149/12500000000000),(125380362473/100000000000000),(278937987/100000000000000),(-3751981/100000000000000),(512367/20000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((63/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((63/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(71691333203/100000000000000),(6714177913/100000000000000),(86069807/50000000000000),(249273/50000000000000),(152281/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((63/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((63/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(856456893519/100000000000000),(16006162767/20000000000000),(101961037/5000000000000),(2746059/50000000000000),(365069/20000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((63/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-187415195125163/50000000000000),(-2193754259179/12500000000000),(-38893985653/100000000000000),(528172277/100000000000000),(44837233/12500000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((63/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-94967852102117/12500000000000),(-36046371521193/100000000000000),(-3193558523/3125000000000),(981041051/100000000000000),(184659273/25000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((63/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(505252170768907/50000000000000),(11588430275881/25000000000000),(57340577211/100000000000000),(-101151109/6250000000000),(198155729/20000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((63/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(283845640918079/10000000000000),(26831497296957/20000000000000),(355357337919/100000000000000),(-190981777/5000000000000),(1374195883/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((63/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(2963400603448773/100000000000000),(145951311535823/100000000000000),(33208189623/5000000000000),(-339698877/12500000000000),(3014048413/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((63/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(105426738791587/100000000000000),(257474902859/100000000000000),(182503897/25000000000000),(-875677/12500000000000),(5275951/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((63/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((63/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((63/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((63/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(55325229587686653/100000000000000),(66443219655351/50000000000000),(160240623557/50000000000000),(-79937567/2000000000000),(705036867/25000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((63/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(36149872579/20000000000000),(-108536103/25000000000000),(-2123/50000000000000),(7791/50000000000000),(933/10000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((63/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(133908192769/2500000000000),(62735156903/25000000000000),(283353267/50000000000000),(-7339899/100000000000000),(5785743/100000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((63/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((63/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((63/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (63/40) (1/40))

def c259 : Certificate := ⟨(23093928249913/100000000000000),(-21179714373/25000000000000),(1316657/10000000000000),(1476229/50000000000000),(1661767/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((63/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(508285800023/20000000000000),(22591695331/20000000000000),(-4388857/25000000000000),(-3936611/100000000000000),(1290717/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((63/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((63/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(32294306813/50000000000000),(5741518967/100000000000000),(126703857/100000000000000),(-119877/50000000000000),(72969/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((63/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((63/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(771780415997/100000000000000),(68460477719/100000000000000),(1501057719/100000000000000),(-3144007/100000000000000),(1748857/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((63/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-355780445764791/100000000000000),(-3162315013173/20000000000000),(2573104659/100000000000000),(69087351/12500000000000),(90358909/25000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((63/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-144128405491521/20000000000000),(-4054012198659/12500000000000),(-6408571041/50000000000000),(1135985549/100000000000000),(185808631/25000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((63/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(19202711191429/2000000000000),(41850748522343/100000000000000),(-21796434969/50000000000000),(-1467140551/100000000000000),(998377789/100000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((63/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(538580322734423/20000000000000),(3773580064043/3125000000000),(13782165427/50000000000000),(-533139201/12500000000000),(110646907/4000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((63/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(561075363045921/20000000000000),(130827904686763/100000000000000),(254827383153/100000000000000),(-908474961/20000000000000),(302177749/10000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((63/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(3285857706683/3125000000000),(231658472277/100000000000000),(91593001/100000000000000),(-507061/6250000000000),(2654403/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((63/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((63/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((63/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((63/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(27590508394847313/50000000000000),(59835945992879/50000000000000),(1911816111/100000000000000),(-534045899/12500000000000),(56697459/2000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((63/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(90610871109/50000000000000),(-393018289/100000000000000),(169213/20000000000000),(12209/100000000000000),(9411/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((63/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(2541976370169/50000000000000),(226062964221/100000000000000),(-14319829/50000000000000),(-1945973/25000000000000),(5800363/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((63/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((63/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(24848293875447/50000000000000),(213731341733/10000000000000),(-3727882661/100000000000000),(-23335301/25000000000000),(56139823/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((63/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(15776694524093/50000000000000),(171235389349/20000000000000),(-15957019893/100000000000000),(194021773/100000000000000),(21715341/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((63/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((63/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((63/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((63/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((63/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((63/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (63/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((63/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(949350276990106021/100000000000000),(2607728099293337/50000000000000),(-45749615777077/100000000000000),0,(61621/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((63/40)+(1/40)*x)) := (SharedCertificates.h297 (63/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10533519863/100000000000000),(-14467029/25000000000000),(33021/4000000000000),(-1831/25000000000000),(83/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((63/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(614862950615531/100000000000000),(363450773041/50000000000000),(7532602379/100000000000000),(-158979/2500000000000),(4581449/50000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((63/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((63/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (63/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((63/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (63/40) (1/40))

def c307 : Certificate := ⟨(1255098271203401/50000000000000),(11091229182759/50000000000000),0,0,(129/12500000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((63/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (63/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((63/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (63/40) (1/40))

def c311 : Certificate := ⟨(2064803457592939/100000000000000),(2817541634481/100000000000000),0,0,(129/12500000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((63/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (63/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(605384495751/12500000000000),(-6608652327/100000000000000),(9017881/100000000000000),(-6153/50000000000000),(11/50000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((63/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(121570725444867/100000000000000),(454211573779/50000000000000),(-619797507/50000000000000),(845741/50000000000000),(3339/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((63/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((63/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (63/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((63/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (63/40) (1/40))

def c316 : Certificate := ⟨(11860406091347/50000000000000),(-12778718709/25000000000000),(89947109/50000000000000),(-633121/100000000000000),(287/12500000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((63/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(5116751269221/100000000000000),(204459499343/100000000000000),(-719576873/100000000000000),(1266241/50000000000000),(1017/10000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((63/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((63/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(26181143551/10000000000000),(4184673611/20000000000000),(344398951/100000000000000),(-107333/4000000000000),(3331/20000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((63/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((63/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(3114944746221/100000000000000),(123934313279/50000000000000),(2007875789/50000000000000),(-8261439/25000000000000),(213209/100000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((63/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-716185793716103/100000000000000),(-7151319571623/25000000000000),(10143061477/10000000000000),(-87433121/25000000000000),(1525383/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((63/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-146933580107183/10000000000000),(-30088315322013/50000000000000),(153338775277/100000000000000),(-82976421/25000000000000),(1294747/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((63/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1894766980399623/100000000000000),(72633622112263/100000000000000),(-763309939/200000000000),(833672463/50000000000000),(920003/12500000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((63/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(1367384836550107/25000000000000),(222272987173301/100000000000000),(-640212017009/100000000000000),(744710019/50000000000000),(19286807/100000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((63/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(2966157140258277/50000000000000),(12989738581101/5000000000000),(4564781723/50000000000000),(-545648491/20000000000000),(810107/2000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((63/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(1726489280843/1562500000000),(429842366741/100000000000000),(-218950959/20000000000000),(2381639/100000000000000),(7399/20000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((63/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((63/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((63/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((63/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(57918913685503557/100000000000000),(5450753911611/2500000000000),(-180511327587/25000000000000),(89409573/5000000000000),(7472417/25000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((63/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(172655171923/100000000000000),(-649943719/100000000000000),(4599053/100000000000000),(-15373/50000000000000),(143/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((63/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(5121223710019/50000000000000),(409992405533/100000000000000),(-69996343/5000000000000),(5354361/100000000000000),(29953/20000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((63/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((63/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((63/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (63/40) (1/40))

def c344 : Certificate := ⟨(10759347946157/50000000000000),(-63097383013/50000000000000),(912259599/100000000000000),(-3297353/50000000000000),(6021/12500000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((63/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(2320869405123/50000000000000),(168259688033/100000000000000),(-608173067/50000000000000),(439647/5000000000000),(42501/50000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((63/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((63/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(8618295673/4000000000000),(7810175241/50000000000000),(34038801/20000000000000),(-65539/2000000000000),(52781/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((63/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((63/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((63/40)+(1/40)*x)) := (SharedCertificates.h144 (63/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(641371690787/25000000000000),(46317259543/25000000000000),(989602023/50000000000000),(-4906227/12500000000000),(641577/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((63/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((63/40)+(1/40)*x)) := (SharedCertificates.h148 (63/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-162431087559921/25000000000000),(-5885859984937/25000000000000),(42665214037/25000000000000),(-1231531203/100000000000000),(12003609/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((63/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((63/40)+(1/40)*x)) := (SharedCertificates.h151 (63/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-53193814967743/4000000000000),(-24649380901489/50000000000000),(158393663567/50000000000000),(-2002794389/100000000000000),(7799693/25000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((63/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((63/40)+(1/40)*x)) := (SharedCertificates.h154 (63/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(345068298618901/20000000000000),(30127033227593/50000000000000),(-260181620649/50000000000000),(4308053861/100000000000000),(11187231/25000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((63/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((63/40)+(1/40)*x)) := (SharedCertificates.h157 (63/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(990782319290509/20000000000000),(45593140758959/25000000000000),(-1220920163531/100000000000000),(319032171/4000000000000),(111898087/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((63/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((63/40)+(1/40)*x)) := (SharedCertificates.h160 (63/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(5333721025153929/100000000000000),(105137030452621/50000000000000),(-897301703973/100000000000000),(2299011797/100000000000000),(49444183/25000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((63/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((63/40)+(1/40)*x)) := (SharedCertificates.h41 (63/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(109498935012317/100000000000000),(88034931637/25000000000000),(-2262498263/100000000000000),(1430893/10000000000000),(44557/20000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((63/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((63/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((63/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((63/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((63/40)+(1/40)*x)) := (SharedCertificates.h167 (63/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(1794144530105891/3125000000000),(44811641365571/25000000000000),(-78894147957/6250000000000),(4277653037/50000000000000),(27852247/20000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((63/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(174177717991/100000000000000),(-271898017/50000000000000),(2763671/50000000000000),(-431/781250000000),(201/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((63/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(9290153565619/100000000000000),(84311499353/25000000000000),(-2411548633/100000000000000),(4390979/25000000000000),(568879/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((63/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((63/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(7506170422023/6250000000000),(2368237435517/50000000000000),(-2066543751/12500000000000),(42063677/25000000000000),(6452527/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((63/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(19063289960693/25000000000000),(1796918015849/100000000000000),(-39019238353/100000000000000),(5809451/800000000000),(12856399/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((63/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((63/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(1584526350585937/100000000000000),(28997149658203/25000000000000),(345303/10240000),(4977/10240000),(347656251/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((63/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(33489/1600),(183/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((63/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(6128487/64000),(100467/64000),(549/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((63/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(151730455323802457/100000000000000),(3398543858334857/25000000000000),(259287500969329/50000000000000),(10967390814331/100000000000000),(70673052563/50000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((63/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(32953173371/50000000000000),(-590482931/10000000000000),(151894033/50000000000000),(-2950087/25000000000000),(36677/6250000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((63/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5101121866009/100000000000000),(73462308901/100000000000000),(-1618918071/50000000000000),(19532523/25000000000000),(23203703/25000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((63/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((63/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((63/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel11

namespace Hf4Quad.Panel12
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(13/8),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((13/8)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (13/8) (1/40)

def c3 : Certificate := ⟨(17797619047619/6250000000000),(547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((13/8)+(1/40)*x)) := (SharedCertificates.h2 (13/8) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((13/8)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-193333333333333/100000000000000),(-547619047619/12500000000000),0,0,(3/100000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((13/8)+(1/40)*x)) := (SharedCertificates.h4 (13/8) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(169/64),(13/160),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((13/8)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(9989666005291/3125000000000),(4917989417989/50000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((13/8)+(1/40)*x)) := (SharedCertificates.h8 (13/8) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((13/8)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((13/8)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(2197/512),(507/2560),(39/12800),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((13/8)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(4180561704282407/100000000000000),(192949001736111/100000000000000),(593689236111/20000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((13/8)+(1/40)*x)) := (SharedCertificates.h13 (13/8) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((13/8)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((13/8)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(28561/4096),(2197/5120),(507/51200),(13/128000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((13/8)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(973992435515873/50000000000000),(29968998015873/25000000000000),(2766369047619/100000000000000),(28373015873/100000000000000),(21825397/20000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((13/8)+(1/40)*x)) := (SharedCertificates.h18 (13/8) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((13/8)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(566548156738281/50000000000000),(21790313720703/25000000000000),(2197/81920),(169/409600),(19897461/6250000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((13/8)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(7381912649649157/100000000000000),(567839434588393/100000000000000),(17471982602719/100000000000000),(268799732349/100000000000000),(1037026191/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((13/8)+(1/40)*x)) := (SharedCertificates.h22 (13/8) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((13/8)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(1841281509399413/100000000000000),(169964447021483/100000000000000),(653709411621/10000000000000),(134094238281/100000000000000),(1556787113/100000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((13/8)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(2067301250235743/50000000000000),(190827807714067/50000000000000),(14679062131849/100000000000000),(150554483403/50000000000000),(3495769583/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((13/8)+(1/40)*x)) := (SharedCertificates.h26 (13/8) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((13/8)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(1496041226387023/50000000000000),(64444852828979/20000000000000),(7435944557189/50000000000000),(381330490111/100000000000000),(1184210939/20000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((13/8)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(710025915380507/100000000000000),(76464329348669/100000000000000),(705824578603/20000000000000),(90490330589/100000000000000),(8781723/625000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((13/8)+(1/40)*x)) := (SharedCertificates.h30 (13/8) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((13/8)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((13/8)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((13/8)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((13/8)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((13/8)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (13/8) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((13/8)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((13/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (13/8) (1/40))

def c43 : Certificate := ⟨(441/64),(21/160),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((13/8)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((13/8)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(34553503941/50000000000000),(-32908099/2500000000000),(18804627/100000000000000),(-238789/100000000000000),(2923/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((13/8)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-26128306878111/2500000000000),(368570717/160000000000),(-447547117/20000000000000),(21731181/100000000000000),(22035681/25000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((13/8)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((13/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (13/8) (1/40))

def c52 : Certificate := ⟨(30208333333333/25000000000000),(833333333333/100000000000000),0,0,(1/20000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((13/8)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (13/8) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((13/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (13/8) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((13/8)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (13/8) (1/40))

def c56 : Certificate := ⟨(23762376237623/100000000000000),(-11763552593/25000000000000),(46588327/50000000000000),(-184509/100000000000000),(369/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((13/8)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(154702970297/3125000000000),(37643368297/20000000000000),(-372706617/100000000000000),(46127/6250000000000),(811/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((13/8)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((13/8)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((13/8)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((13/8)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((13/8)+(1/40)*x)) := (SharedCertificates.h61 (13/8) (1/40)).addExact h62

def c64 : Certificate := ⟨(-35388687383583/50000000000000),(-2746847765831/100000000000000),(51777621/1562500000000),(-588231/25000000000000),(48747/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((13/8)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((13/8)+(1/40)*x)) := (SharedCertificates.h61 (13/8) (1/40)).addExact h64

def c66 : Certificate := ⟨(-36405380563537/50000000000000),(-363029160341/12500000000000),(475702399/100000000000000),(5503463/100000000000000),(31747/50000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((13/8)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((13/8)+(1/40)*x)) := (SharedCertificates.h67 (13/8) (1/40)).addExact h66

def c69 : Certificate := ⟨(-175069573295191/50000000000000),(-13455994943693/100000000000000),(1307382949/6250000000000),(-40207537/100000000000000),(130899/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((13/8)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((13/8)+(1/40)*x)) := (SharedCertificates.h67 (13/8) (1/40)).addExact h69

def c71 : Certificate := ⟨(-363868274583613/100000000000000),(-7250169055007/50000000000000),(620711427/20000000000000),(3328597/10000000000000),(189711/50000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((13/8)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((13/8)+(1/40)*x)) := (SharedCertificates.h72 (13/8) (1/40)).addExact h71

def c74 : Certificate := ⟨(250894349638971/50000000000000),(459001711551/2500000000000),(-32458235301/50000000000000),(34085213/25000000000000),(240181/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((13/8)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((13/8)+(1/40)*x)) := (SharedCertificates.h72 (13/8) (1/40)).addExact h74

def c76 : Certificate := ⟨(108928600982929/10000000000000),(21616133476933/50000000000000),(-19322680361/100000000000000),(-41066661/20000000000000),(206537/12500000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((13/8)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((13/8)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((13/8)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h57

def c81 : Certificate := ⟨(110146064111359/100000000000000),(39506901381/10000000000000),(-214029543/50000000000000),(146143/100000000000000),(3793/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((13/8)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(549639765466589/5000000000000),(883037919481/5000000000000),(-77692943193/100000000000000),(168432877/100000000000000),(1449807/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((13/8)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(227421682079/25000000000000),(-4567127/312500000000),(8777303/100000000000000),(-38369/100000000000000),(269/100000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((13/8)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(9909090264819/100000000000000),(377358490681/100000000000000),(-711997137/100000000000000),(895593/50000000000000),(16699/50000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((13/8)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((13/8)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((13/8)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (13/8) (1/40))

def c87 : Certificate := ⟨(21621621621621/100000000000000),(-29218407597/25000000000000),(631749353/100000000000000),(-1707431/50000000000000),(18563/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((13/8)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(563063063063/12500000000000),(77915753591/50000000000000),(-105291559/12500000000000),(1138287/25000000000000),(16241/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((13/8)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((13/8)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((13/8)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((13/8)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((13/8)+(1/40)*x)) := (SharedCertificates.h61 (13/8) (1/40)).addExact h91

def c93 : Certificate := ⟨(-32140248356461/50000000000000),(-1132937173837/50000000000000),(10790961939/100000000000000),(-50453801/100000000000000),(120219/20000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((13/8)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((13/8)+(1/40)*x)) := (SharedCertificates.h61 (13/8) (1/40)).addExact h93

def c95 : Certificate := ⟨(-4122411308313/6250000000000),(-1191938389729/50000000000000),(2322310831/25000000000000),(-16520819/50000000000000),(388997/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((13/8)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((13/8)+(1/40)*x)) := (SharedCertificates.h67 (13/8) (1/40)).addExact h95

def c97 : Certificate := ⟨(-63657284512903/20000000000000),(-11118371590437/100000000000000),(28111233427/50000000000000),(-144328089/50000000000000),(642797/25000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((13/8)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((13/8)+(1/40)*x)) := (SharedCertificates.h67 (13/8) (1/40)).addExact h97

def c99 : Certificate := ⟨(-82413135389231/25000000000000),(-11905023581297/100000000000000),(46850920459/100000000000000),(-164948971/100000000000000),(983811/25000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((13/8)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((13/8)+(1/40)*x)) := (SharedCertificates.h72 (13/8) (1/40)).addExact h99

def c101 : Certificate := ⟨(114530939847319/25000000000000),(239255365729/1562500000000),(-102109515013/100000000000000),(157232303/25000000000000),(4688113/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((13/8)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((13/8)+(1/40)*x)) := (SharedCertificates.h72 (13/8) (1/40)).addExact h101

def c103 : Certificate := ⟨(493609178350813/50000000000000),(17765954611623/50000000000000),(-146083813871/100000000000000),(478340201/100000000000000),(395643/3125000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((13/8)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((13/8)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((13/8)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h88

def c108 : Certificate := ⟨(54605957308659/50000000000000),(81425472221/25000000000000),(-758858083/50000000000000),(5513/80000000000),(44679/50000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((13/8)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5475354097706107/50000000000000),(2957725261207/20000000000000),(-6805111131/6250000000000),(705266727/100000000000000),(8375509/50000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((13/8)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(456591474339/50000000000000),(-1233228129/100000000000000),(85961/800000000000),(-42793/50000000000000),(853/50000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((13/8)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(4507554849809/50000000000000),(39037085237/12500000000000),(-416531033/25000000000000),(1828539/20000000000000),(2897/1562500000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((13/8)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((13/8)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-197782921637419/100000000000000),(-7164215633483/100000000000000),(26019706251/100000000000000),(-8191993/6250000000000),(19806651/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((13/8)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(61538461538461/100000000000000),(-946745562131/100000000000000),(728265817/5000000000000),(-22408179/10000000000000),(21883/625000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((13/8)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-7607035447593/6250000000000),(-2536247048889/100000000000000),(13757828073/25000000000000),(-927295197/100000000000000),(40718011/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((13/8)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((13/8)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((13/8)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((13/8)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((13/8)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((13/8)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((13/8)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((13/8)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((13/8)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((13/8)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (13/8) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((13/8)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((13/8)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(15175909577/100000000000000),(-58368883/6250000000000),(2244957/6250000000000),(-110521/10000000000000),(8691/25000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((13/8)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(66811230541981/50000000000000),(-817456207879/100000000000000),(938301699/10000000000000),(-103188789/100000000000000),(299969063/50000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((13/8)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((13/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (13/8) (1/40))

def c134 : Certificate := ⟨(1073/64),(33/160),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((13/8)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((13/8)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(3174603174603/50000000000000),(-30234315949/50000000000000),(143972933/25000000000000),(-1371171/25000000000000),(2637/5000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((13/8)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(53224206349203/50000000000000),(147864701429/50000000000000),(575891729/50000000000000),(-10969381/100000000000000),(333969/20000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((13/8)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((13/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (13/8) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((13/8)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (13/8) (1/40))

def c140 : Certificate := ⟨(12301684159141/50000000000000),(-1118828859/6250000000000),(-56695567/100000000000000),(47249/6250000000000),(51053/50000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((13/8)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(1586526726871/100000000000000),(2864201879/4000000000000),(226782267/100000000000000),(-1511969/50000000000000),(421589/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((13/8)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((13/8)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(503413411/2000000000000),(142004151/6250000000000),(1871/3200000000),(228823/100000000000000),(3563/20000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((13/8)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((13/8)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h145

def c147 : Certificate := ⟨(37656170971/12500000000000),(27156656169/100000000000000),(696401761/100000000000000),(2646099/100000000000000),(53483/25000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((13/8)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h147

def c150 : Certificate := ⟨(-111054481180103/50000000000000),(-10024060019141/100000000000000),(-991198127/3125000000000),(105986109/25000000000000),(29513763/50000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((13/8)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h150

def c153 : Certificate := ⟨(-447751301574501/100000000000000),(-4073497754231/20000000000000),(-1120057677/1562500000000),(407350173/50000000000000),(120539283/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((13/8)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h153

def c156 : Certificate := ⟨(301854547887971/50000000000000),(6731048725651/25000000000000),(35287160709/50000000000000),(-308817491/25000000000000),(16354999/10000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((13/8)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h156

def c159 : Certificate := ⟨(837715534685793/50000000000000),(76044745053497/100000000000000),(129944624201/50000000000000),(-1550697251/50000000000000),(7024739/1562500000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((13/8)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h159

def c162 : Certificate := ⟨(1719015386626311/100000000000000),(79997626141573/100000000000000),(362870717079/100000000000000),(-2657772169/100000000000000),(19209679/4000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((13/8)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h141

def c164 : Certificate := ⟨(25799556031073/25000000000000),(72741080183/50000000000000),(128008321/25000000000000),(-5819053/100000000000000),(860993/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((13/8)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((13/8)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((13/8)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((13/8)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h168

def c170 : Certificate := ⟨(1083417706489517/2000000000000),(75628008618477/100000000000000),(124364482433/50000000000000),(-3159384979/100000000000000),(114479251/25000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((13/8)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(184601007351/100000000000000),(-64430397/25000000000000),(-243901/50000000000000),(1263/10000000000000),(1597/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((13/8)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(317331972023/10000000000000),(143246149961/100000000000000),(91061291/20000000000000),(-6014589/100000000000000),(931753/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((13/8)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((13/8)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((13/8)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (13/8) (1/40))

def c175 : Certificate := ⟨(5961674946771/25000000000000),(-50451296313/100000000000000),(-44878187/50000000000000),(154811/6250000000000),(147297/50000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((13/8)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(1537733617221/100000000000000),(67268395083/100000000000000),(29918791/25000000000000),(-825659/25000000000000),(86157/20000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((13/8)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((13/8)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(945849871/4000000000000),(2068817449/100000000000000),(2446547/5000000000000),(11887/20000000000000),(907/5000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((13/8)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((13/8)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h179

def c181 : Certificate := ⟨(35378466091/12500000000000),(24730370683/100000000000000),(582826507/100000000000000),(160543/25000000000000),(108717/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((13/8)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h181

def c183 : Certificate := ⟨(-21527835419841/10000000000000),(-4708502318093/50000000000000),(-4182146551/25000000000000),(462791221/100000000000000),(30156307/50000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((13/8)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h183

def c185 : Certificate := ⟨(-43387582044499/10000000000000),(-19124773363097/100000000000000),(-40358589621/100000000000000),(916441569/100000000000000),(123159347/100000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((13/8)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h185

def c187 : Certificate := ⟨(146338897070527/25000000000000),(12656191368333/50000000000000),(6414032167/20000000000000),(-1293129271/100000000000000),(167244841/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((13/8)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h187

def c189 : Certificate := ⟨(324724301548669/20000000000000),(71414811165577/100000000000000),(17984979341/12500000000000),(-345511913/10000000000000),(14353427/3125000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((13/8)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h189

def c191 : Certificate := ⟨(1664554245564049/100000000000000),(4688282638503/6250000000000),(230049237423/100000000000000),(-1658385289/50000000000000),(490713613/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((13/8)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h176

def c193 : Certificate := ⟨(103099113481217/100000000000000),(27321121523/20000000000000),(72070317/25000000000000),(-6545837/100000000000000),(87971/10000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((13/8)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((13/8)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((13/8)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((13/8)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h196

def c198 : Certificate := ⟨(27059677585168997/50000000000000),(35517947557541/50000000000000),(134545044783/100000000000000),(-3478313119/100000000000000),(467715411/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((13/8)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(184776776599/100000000000000),(-242534001/100000000000000),(-5641/4000000000000),(12663/100000000000000),(327/20000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((13/8)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(615141935939/20000000000000),(26913722117/20000000000000),(30099907/12500000000000),(-3290787/50000000000000),(953617/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((13/8)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((13/8)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(208752671951/2500000000000),(160069920767/50000000000000),(-377256467/50000000000000),(-1451277/50000000000000),(41816463/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((13/8)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(5138527309563/100000000000000),(2359097339/2000000000000),(-2279005913/100000000000000),(16637721/50000000000000),(13619977/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((13/8)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((13/8)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((13/8)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((13/8)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((13/8)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((13/8)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (13/8) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((13/8)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((13/8)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((13/8)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (13/8) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((13/8)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(20180234721/50000000000000),(-52915991/25000000000000),(606851/20000000000000),(-6501/25000000000000),(143/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((13/8)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(47344722552471/10000000000000),(-321179019661/25000000000000),(-1111078613/50000000000000),(-49597193/100000000000000),(1631613/25000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((13/8)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((13/8)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((13/8)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((13/8)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (13/8) (1/40))

def c223 : Certificate := ⟨(841/64),(29/160),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((13/8)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(2846785/4096),(16965/1024),(7043/51200),(57/128000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((13/8)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((13/8)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(161249685059/100000000000000),(-3071422573/100000000000000),(8775493/20000000000000),(-22287/4000000000000),(213/3125000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((13/8)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(28017772502483/25000000000000),(107359566339/20000000000000),(895690423/50000000000000),(-11004777/100000000000000),(1907121/20000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((13/8)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((13/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (13/8) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((13/8)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (13/8) (1/40))

def c231 : Certificate := ⟨(24267657310681/100000000000000),(-987907953/3125000000000),(-64316081/100000000000000),(434653/50000000000000),(282373/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((13/8)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1464685378637/50000000000000),(126452217983/100000000000000),(257264321/100000000000000),(-139089/4000000000000),(59883/2500000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((13/8)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((13/8)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(17162426067/20000000000000),(7408508591/100000000000000),(34994817/20000000000000),(446911/100000000000000),(154559/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((13/8)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((13/8)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h235

def c237 : Certificate := ⟨(204943610623/20000000000000),(88251035039/100000000000000),(414051953/20000000000000),(7597/156250000000),(926023/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((13/8)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h237

def c239 : Certificate := ⟨(-51260236028421/12500000000000),(-17699429538901/100000000000000),(-35842127731/100000000000000),(61220403/12500000000000),(167693743/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((13/8)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h239

def c241 : Certificate := ⟨(-83223663095133/10000000000000),(-36443660591567/100000000000000),(-96520274297/100000000000000),(911371967/100000000000000),(138466403/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((13/8)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h241

def c243 : Certificate := ⟨(1103428445052079/100000000000000),(93128304617/200000000000),(11998615461/25000000000000),(-299780797/20000000000000),(926474109/100000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((13/8)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h243

def c245 : Certificate := ⟨(1554081402667249/50000000000000),(135534175285871/100000000000000),(20828350241/6250000000000),(-3552880383/100000000000000),(2574343679/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((13/8)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h245

def c247 : Certificate := ⟨(3257938519753571/100000000000000),(148576107487759/100000000000000),(648416333709/100000000000000),(-1267610329/50000000000000),(2844582369/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((13/8)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h232

def c249 : Certificate := ⟨(105944553644883/100000000000000),(260312944557/100000000000000),(689502727/100000000000000),(-6507539/100000000000000),(4945199/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((13/8)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((13/8)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((13/8)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((13/8)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h252

def c254 : Certificate := ⟨(55592252980849751/100000000000000),(33530381022069/25000000000000),(297334395061/100000000000000),(-3723411511/100000000000000),(1323657737/50000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((13/8)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(179881178829/100000000000000),(-86796043/20000000000000),(3397/4000000000000),(3541/25000000000000),(347/4000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((13/8)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(732552276857/12500000000000),(126560822507/50000000000000),(262177419/50000000000000),(-6786751/100000000000000),(2728739/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((13/8)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((13/8)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((13/8)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (13/8) (1/40))

def c259 : Certificate := ⟨(22924566231827/100000000000000),(-84631933217/100000000000000),(6002031/20000000000000),(533379/20000000000000),(382817/25000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((13/8)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(276724502423/10000000000000),(56421288811/50000000000000),(-20006771/50000000000000),(-3555861/100000000000000),(602843/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((13/8)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((13/8)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(76576450241/100000000000000),(1561315307/25000000000000),(125119927/100000000000000),(-2243/781250000000),(36729/25000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((13/8)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((13/8)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h263

def c265 : Certificate := ⟨(914679286873/100000000000000),(37212334847/50000000000000),(370120257/25000000000000),(-925323/25000000000000),(1760397/100000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((13/8)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h265

def c267 : Certificate := ⟨(-387388991975147/100000000000000),(-15794869206427/100000000000000),(5726481137/100000000000000),(62415803/12500000000000),(13505201/4000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((13/8)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h267

def c269 : Certificate := ⟨(-12274197021707/1562500000000),(-4058768023791/12500000000000),(-1576517991/25000000000000),(41440627/4000000000000),(347876999/50000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((13/8)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h269

def c271 : Certificate := ⟨(521825639761159/50000000000000),(20829715317847/50000000000000),(-12976384993/25000000000000),(-81657991/6250000000000),(93258393/10000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((13/8)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h271

def c273 : Certificate := ⟨(1467243831772197/50000000000000),(60407604014843/50000000000000),(392675117/12500000000000),(-3882160629/100000000000000),(161744359/6250000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((13/8)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h273

def c275 : Certificate := ⟨(61360324063073/2000000000000),(26358783041523/20000000000000),(114236623157/50000000000000),(-4246799661/100000000000000),(711430017/25000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((13/8)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h260

def c277 : Certificate := ⟨(105611066498701/100000000000000),(28991302059/12500000000000),(45092843/100000000000000),(-3699413/50000000000000),(248483/5000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((13/8)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((13/8)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((13/8)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((13/8)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h280

def c282 : Certificate := ⟨(55420334851995319/100000000000000),(119629881961227/100000000000000),(-22524056683/100000000000000),(-969845991/25000000000000),(2657295589/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((13/8)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(180439184041/100000000000000),(-389494549/100000000000000),(457047/50000000000000),(10499/100000000000000),(8741/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((13/8)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(345993962701/6250000000000),(112929054671/50000000000000),(-73030303/100000000000000),(-7025951/100000000000000),(1091621/20000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((13/8)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((13/8)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(26977784256317/50000000000000),(1060652990811/50000000000000),(-4269990613/100000000000000),(-87490033/100000000000000),(26332651/50000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((13/8)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(6640685355401/20000000000000),(794597115197/100000000000000),(-2970451507/20000000000000),(174656249/100000000000000),(19714919/50000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((13/8)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((13/8)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((13/8)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((13/8)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((13/8)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((13/8)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (13/8) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((13/8)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(479799095462085533/50000000000000),(503245773547837/10000000000000),(-45749615777077/100000000000000),0,(124541/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((13/8)+(1/40)*x)) := (SharedCertificates.h297 (13/8) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(10421028399/100000000000000),(-54651401/100000000000000),(783441/100000000000000),(-1343/20000000000000),(19/25000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((13/8)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(9630419371903/1562500000000),(756968439691/100000000000000),(75038687/1000000000000),(-132497/4000000000000),(8452879/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((13/8)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((13/8)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (13/8) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((13/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (13/8) (1/40))

def c307 : Certificate := ⟨(2554561459137839/100000000000000),(11091229182759/50000000000000),0,0,(207/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((13/8)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (13/8) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((13/8)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (13/8) (1/40))

def c311 : Certificate := ⟨(1035219270430951/50000000000000),(2817541634481/100000000000000),0,0,(517/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((13/8)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (13/8) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4829894634707/100000000000000),(-657272793/10000000000000),(178889/2000000000000),(-3043/25000000000000),(21/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((13/8)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(123382626855191/100000000000000),(112935623991/12500000000000),(-245900233/20000000000000),(1673157/100000000000000),(1647/50000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((13/8)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((13/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (13/8) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((13/8)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (13/8) (1/40))

def c316 : Certificate := ⟨(11809648490159/50000000000000),(-25201412373/50000000000000),(22018543/12500000000000),(-307803/50000000000000),(2219/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((13/8)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(5522812078727/100000000000000),(201611298981/100000000000000),(-704593379/100000000000000),(123121/5000000000000),(4951/50000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((13/8)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((13/8)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(305014532569/100000000000000),(2783653293/12500000000000),(164322211/50000000000000),(-2569091/100000000000000),(3213/20000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((13/8)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((13/8)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h320

def c322 : Certificate := ⟨(1813241815967/50000000000000),(6588526339/2500000000000),(3821935907/100000000000000),(-6314339/20000000000000),(41017/20000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((13/8)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h322

def c324 : Certificate := ⟨(-772993407145723/100000000000000),(-7050928894861/25000000000000),(3974397119/4000000000000),(-68108917/20000000000000),(14821/1000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((13/8)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h324

def c326 : Certificate := ⟨(-99317397206323/6250000000000),(-7445905496817/12500000000000),(151358191249/100000000000000),(-82069307/25000000000000),(313923/6250000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((13/8)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h326

def c328 : Certificate := ⟨(407704167792577/20000000000000),(14225360329709/20000000000000),(-371806975913/100000000000000),(807816927/50000000000000),(893693/12500000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((13/8)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h328

def c330 : Certificate := ⟨(5911536357784959/100000000000000),(219729951866139/100000000000000),(-631320862659/100000000000000),(1474206757/100000000000000),(4666101/25000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((13/8)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h330

def c332 : Certificate := ⟨(6451918770675521/100000000000000),(129899529527933/50000000000000),(-8575181/125000000000),(-104100949/4000000000000),(39462699/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((13/8)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h317

def c334 : Certificate := ⟨(111350638690023/100000000000000),(212745912153/50000000000000),(-8441737/781250000000),(2355749/100000000000000),(35869/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((13/8)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((13/8)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((13/8)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((13/8)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h337

def c339 : Certificate := ⟨(58352100088776489/100000000000000),(53790841349091/25000000000000),(-177841871749/25000000000000),(1770941171/100000000000000),(28863689/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((13/8)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(42843359471/25000000000000),(-631910173/100000000000000),(883853/20000000000000),(-73/250000000000),(269/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((13/8)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(11056875006789/100000000000000),(101114062007/25000000000000),(-684162881/50000000000000),(1295141/25000000000000),(14577/10000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((13/8)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((13/8)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((13/8)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (13/8) (1/40))

def c344 : Certificate := ⟨(10634951696443/50000000000000),(-15327920711/12500000000000),(436904261/50000000000000),(-38917/625000000000),(44831/100000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((13/8)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(2486731071409/50000000000000),(40874455229/25000000000000),(-116507803/10000000000000),(2075573/25000000000000),(80739/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((13/8)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((13/8)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(12367662843/5000000000000),(3252600891/20000000000000),(18928243/12500000000000),(-745983/25000000000000),(769/1562500000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((13/8)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((13/8)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((13/8)+(1/40)*x)) := (SharedCertificates.h144 (13/8) (1/40)).addExact h348

def c350 : Certificate := ⟨(1471817520571/50000000000000),(3854591007/2000000000000),(350926701/20000000000000),(-713353/2000000000000),(596967/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((13/8)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((13/8)+(1/40)*x)) := (SharedCertificates.h148 (13/8) (1/40)).addExact h350

def c352 : Certificate := ⟨(-696138299420127/100000000000000),(-5718824204467/25000000000000),(163479003203/100000000000000),(-116322707/10000000000000),(11395237/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((13/8)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((13/8)+(1/40)*x)) := (SharedCertificates.h151 (13/8) (1/40)).addExact h352

def c354 : Certificate := ⟨(-713595787386179/50000000000000),(-1501726719809/3125000000000),(61012471459/20000000000000),(-1906490187/100000000000000),(29505987/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((13/8)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((13/8)+(1/40)*x)) := (SharedCertificates.h154 (13/8) (1/40)).addExact h354

def c356 : Certificate := ⟨(921901046154069/50000000000000),(11644644802173/20000000000000),(-495324280031/100000000000000),(808345153/20000000000000),(42195991/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((13/8)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((13/8)+(1/40)*x)) := (SharedCertificates.h157 (13/8) (1/40)).addExact h356

def c358 : Certificate := ⟨(5313836049008331/100000000000000),(35516599641847/20000000000000),(-1174254727621/100000000000000),(3791653869/50000000000000),(105781577/100000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((13/8)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((13/8)+(1/40)*x)) := (SharedCertificates.h160 (13/8) (1/40)).addExact h358

def c360 : Certificate := ⟨(575069849841659/10000000000000),(206712770632189/100000000000000),(-883266168113/100000000000000),(2376330071/100000000000000),(93267303/50000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((13/8)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((13/8)+(1/40)*x)) := (SharedCertificates.h41 (13/8) (1/40)).addExact h345

def c362 : Certificate := ⟨(3443571173203/3125000000000),(343258646287/100000000000000),(-544682529/25000000000000),(3405163/25000000000000),(105347/50000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((13/8)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((13/8)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((13/8)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((13/8)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((13/8)+(1/40)*x)) := (SharedCertificates.h167 (13/8) (1/40)).addExact h365

def c367 : Certificate := ⟨(11553227286496473/20000000000000),(17429825136299/10000000000000),(-1212282097123/100000000000000),(4061934793/50000000000000),(65596549/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((13/8)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(173111802477/100000000000000),(-65291463/12500000000000),(2604483/50000000000000),(-2041/4000000000000),(369/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((13/8)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4977568912813/50000000000000),(81951620433/25000000000000),(-288651549/12500000000000),(16560591/100000000000000),(66543/12500000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((13/8)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((13/8)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(16188359633917/12500000000000),(4672332499607/100000000000000),(-15546678581/100000000000000),(32083029/20000000000000),(1540111/25000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((13/8)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(39848269868103/50000000000000),(412295231723/25000000000000),(-873480027/2500000000000),(318121591/50000000000000),(22860373/100000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((13/8)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((13/8)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(915193176269531/50000000000000),(32517852783203/25000000000000),(15041/409600),(1053/2048000),(89355469/25000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((13/8)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(1369/64),(37/160),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((13/8)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(50653/512),(4107/2560),(111/12800),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((13/8)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(90541562417149519/50000000000000),(7902330603599523/50000000000000),(587834811210631/100000000000000),(1213440284729/10000000000000),(9550248697/6250000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((13/8)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(2208930293/4000000000000),(-2409901181/50000000000000),(60349619/25000000000000),(-285103/3125000000000),(110111/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((13/8)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2617847906967/50000000000000),(30700114471/50000000000000),(-560948091/20000000000000),(66586247/100000000000000),(84628569/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((13/8)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((13/8)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((13/8)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel12
