import Hf4QuadSharedCertificates

noncomputable section

namespace Hf4Quad.Panel34
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(109/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((109/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (109/40) (1/40)

def c3 : Certificate := ⟨(477523809523809/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((109/40)+(1/40)*x)) := (SharedCertificates.h2 (109/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((109/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-193047619047619/50000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((109/40)+(1/40)*x)) := (SharedCertificates.h4 (109/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(11881/1600),(109/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((109/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(224733201058201/25000000000000),(16494179894179/100000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((109/40)+(1/40)*x)) := (SharedCertificates.h8 (109/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((109/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((109/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1295029/64000),(35643/64000),(327/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((109/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(788558746412037/4000000000000),(542586293402777/100000000000000),(4977855902777/100000000000000),(608912037/4000000000000),(1/25000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((109/40)+(1/40)*x)) := (SharedCertificates.h13 (109/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((109/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((109/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(141158161/2560000),(1295029/640000),(35643/1280000),(109/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((109/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(15404164394841269/100000000000000),(17665326140873/3125000000000),(1944806547619/25000000000000),(47579365079/100000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((109/40)+(1/40)*x)) := (SharedCertificates.h18 (109/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((109/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(1878203069946289/12500000000000),(172312208251953/25000000000000),(1295029/10240000),(11881/10240000),(266601563/50000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((109/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(19577832296506799/20000000000000),(898065701674623/20000000000000),(5149459298593/6250000000000),(377941966869/50000000000000),(3473719627/100000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((109/40)+(1/40)*x)) := (SharedCertificates.h22 (109/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((109/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(409448269248291/1000000000000),(450768736787109/20000000000000),(10338732495117/20000000000000),(316169189453/50000000000000),(1091735841/25000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((109/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(91941717179351693/100000000000000),(2530505977413347/50000000000000),(58039127922323/50000000000000),(709958751343/50000000000000),(9805982879/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((109/40)+(1/40)*x)) := (SharedCertificates.h26 (109/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((109/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(111574653370159297/100000000000000),(7165344711845087/100000000000000),(197211322344357/100000000000000),(376932955551/12500000000000),(13908776863/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((109/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(13238421173681599/50000000000000),(1700347673683873/100000000000000),(584981997827/1250000000000),(178893577317/25000000000000),(6601149657/100000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((109/40)+(1/40)*x)) := (SharedCertificates.h30 (109/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((109/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((109/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((109/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((109/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((109/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (109/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((109/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((109/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (109/40) (1/40))

def c43 : Certificate := ⟨(22201/1600),(149/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((109/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((109/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(17159244221/50000000000000),(-115162713/25000000000000),(289839/6250000000000),(-41499/100000000000000),(357/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((109/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-259507964032889/25000000000000),(113043731967/100000000000000),(-192370647/25000000000000),(5261321/100000000000000),(10746463/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((109/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((109/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (109/40) (1/40))

def c52 : Certificate := ⟨(78749999999999/50000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((109/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (109/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((109/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (109/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((109/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (109/40) (1/40))

def c56 : Certificate := ⟨(21857923497267/100000000000000),(-19907034151/50000000000000),(72521071/100000000000000),(-132097/100000000000000),(49/20000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((109/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(785519125683/6250000000000),(159256273203/100000000000000),(-290084287/100000000000000),(264193/50000000000000),(1247/100000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((109/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((109/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((109/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((109/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((109/40)+(1/40)*x)) := (SharedCertificates.h61 (109/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-46358505778013/25000000000000),(-154361100871/6250000000000),(595386111/20000000000000),(-530117/20000000000000),(3453/10000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((109/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((109/40)+(1/40)*x)) := (SharedCertificates.h61 (109/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-19926219962609/10000000000000),(-283531234761/10000000000000),(1039968939/100000000000000),(19969/625000000000),(3133/6250000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((109/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((109/40)+(1/40)*x)) := (SharedCertificates.h67 (109/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-452412651889037/50000000000000),(-11821627409451/100000000000000),(16499222121/100000000000000),(-693933/2500000000000),(109107/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((109/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((109/40)+(1/40)*x)) := (SharedCertificates.h67 (109/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-496751316904049/50000000000000),(-14074708490297/100000000000000),(3088822801/50000000000000),(7656057/50000000000000),(26731/10000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((109/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((109/40)+(1/40)*x)) := (SharedCertificates.h72 (109/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(18668838748497/1562500000000),(13370740984331/100000000000000),(-24607642953/50000000000000),(2570557/2500000000000),(220663/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((109/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((109/40)+(1/40)*x)) := (SharedCertificates.h72 (109/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(1469838965233699/50000000000000),(40610374653973/100000000000000),(-37633155237/100000000000000),(-84896229/100000000000000),(275907/25000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((109/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((109/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((109/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(126716235181699/100000000000000),(358544177921/100000000000000),(-399460331/100000000000000),(53127/20000000000000),(2671/50000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((109/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2326593170549253/20000000000000),(1172615795001/10000000000000),(-29015444977/50000000000000),(2601783/2000000000000),(255753/25000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((109/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(10745325103/1250000000000),(-866512503/100000000000000),(2580843/50000000000000),(-19139/100000000000000),(67/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((109/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(25270236048789/100000000000000),(323624665753/100000000000000),(-26183071/5000000000000),(56493/5000000000000),(899/4000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((109/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((109/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((109/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (109/40) (1/40))

def c87 : Certificate := ⟨(17467248908297/100000000000000),(-76276196107/100000000000000),(13323353/4000000000000),(-290903/20000000000000),(6383/100000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((109/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(1004366812227/10000000000000),(101701594807/100000000000000),(-444111769/100000000000000),(242419/12500000000000),(1981/12500000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((109/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((109/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((109/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((109/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((109/40)+(1/40)*x)) := (SharedCertificates.h61 (109/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-146663869872799/100000000000000),(-386599293797/25000000000000),(191632289/3125000000000),(-376067/1562500000000),(11071/4000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((109/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((109/40)+(1/40)*x)) := (SharedCertificates.h61 (109/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-77670893028541/50000000000000),(-1728296822093/100000000000000),(5912106839/100000000000000),(-3861657/20000000000000),(355373/100000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((109/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((109/40)+(1/40)*x)) := (SharedCertificates.h67 (109/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-718658782005681/100000000000000),(-7450681107291/100000000000000),(15306900971/50000000000000),(-15877281/12500000000000),(312481/25000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((109/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((109/40)+(1/40)*x)) := (SharedCertificates.h67 (109/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-775236471555099/100000000000000),(-2149580190569/25000000000000),(1861047451/6250000000000),(-98225179/100000000000000),(1762051/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((109/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((109/40)+(1/40)*x)) := (SharedCertificates.h72 (109/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(976722974472559/100000000000000),(4513326399093/50000000000000),(-24471384903/50000000000000),(123600789/50000000000000),(2121231/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((109/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((109/40)+(1/40)*x)) := (SharedCertificates.h72 (109/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(92214717349467/4000000000000),(12578617346219/50000000000000),(-46704876941/50000000000000),(63015263/20000000000000),(1340683/25000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((109/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((109/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((109/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(121096088938043/100000000000000),(13989520683/6250000000000),(-874001619/100000000000000),(336493/10000000000000),(40849/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((109/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(11438027963885989/100000000000000),(8210443579837/100000000000000),(-49986180771/100000000000000),(53789977/20000000000000),(7107611/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((109/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(218569145651/25000000000000),(-627573091/100000000000000),(170849/4000000000000),(-26367/100000000000000),(3/500000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((109/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(20155291987521/100000000000000),(102737971473/50000000000000),(-219018047/25000000000000),(1903759/50000000000000),(73543/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((109/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((109/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-47153145183287/10000000000000),(-1360220539281/25000000000000),(14778254297/100000000000000),(-27257611/50000000000000),(10918407/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((109/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(18348623853211/50000000000000),(-336671997307/100000000000000),(19304587/625000000000),(-28337009/100000000000000),(262381/100000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((109/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-173039064892797/100000000000000),(-204569822899/50000000000000),(9176787319/100000000000000),(-104196293/100000000000000),(7483049/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((109/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((109/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((109/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((109/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((109/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((109/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((109/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((109/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((109/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((109/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (109/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((109/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((109/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(479780037/25000000000000),(-17606607/25000000000000),(323057/20000000000000),(-29639/100000000000000),(67/12500000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((109/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(54954410612221/50000000000000),(-175967857127/50000000000000),(2831010523/100000000000000),(-5488379/25000000000000),(60306193/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((109/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((109/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (109/40) (1/40))

def c134 : Certificate := ⟨(43281/1600),(209/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((109/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((109/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(559284116331/12500000000000),(-30028677387/100000000000000),(201534747/100000000000000),(-1352583/100000000000000),(4571/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((109/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(12103187919461/10000000000000),(35660931189/10000000000000),(403069479/100000000000000),(-2705187/100000000000000),(238971/50000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((109/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((109/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (109/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((109/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (109/40) (1/40))

def c140 : Certificate := ⟨(7600374599/32000000000),(-10058488479/50000000000000),(-356189/6250000000000),(17669/10000000000000),(27283/100000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((109/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(2497658756249/50000000000000),(80467907829/100000000000000),(11398047/50000000000000),(-706761/100000000000000),(60301/50000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((109/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((109/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(124765985253/50000000000000),(8039254983/100000000000000),(16757079/25000000000000),(-33923/100000000000000),(6689/50000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((109/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((109/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(742363454407/25000000000000),(95266300859/100000000000000),(784591429/100000000000000),(-255849/50000000000000),(9999/6250000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((109/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-699196118103143/100000000000000),(-11258358784489/100000000000000),(-3074924609/100000000000000),(99553053/100000000000000),(16889849/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((109/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1433615969633753/100000000000000),(-23656033447961/100000000000000),(-7877631871/50000000000000),(202766923/100000000000000),(35641707/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((109/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(1851583572718647/100000000000000),(28644849755509/100000000000000),(-5686426447/50000000000000),(-134956239/50000000000000),(23433689/50000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((109/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(106751517331789/2000000000000),(87412134979387/100000000000000),(23419894309/50000000000000),(-96411237/12500000000000),(26340173/20000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((109/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(5778341112136119/100000000000000),(101814401851057/100000000000000),(21465805133/12500000000000),(-779368517/100000000000000),(77771907/50000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((109/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(55120083497751/50000000000000),(168975070641/100000000000000),(14077563/12500000000000),(-289489/20000000000000),(127291/50000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((109/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((109/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((109/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((109/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(361183975421411/625000000000),(8578740957983/10000000000000),(1574107787/5000000000000),(-98190017/12500000000000),(138145919/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((109/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(173042006991/100000000000000),(-256877841/100000000000000),(287061/100000000000000),(413/20000000000000),(17/4000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((109/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(4999478715613/50000000000000),(80669203237/50000000000000),(26103803/50000000000000),(-137817/10000000000000),(74787/25000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((109/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((109/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((109/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (109/40) (1/40))

def c175 : Certificate := ⟨(2699226463289/12500000000000),(-9977059219/20000000000000),(29429411/50000000000000),(186353/50000000000000),(8633/12500000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((109/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(4541584391583/100000000000000),(33256864063/50000000000000),(-78478431/100000000000000),(-496943/100000000000000),(24227/20000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((109/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((109/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(103129943929/50000000000000),(6041554189/100000000000000),(37112431/100000000000000),(-149537/100000000000000),(1471/12500000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((109/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((109/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(2456383720549/100000000000000),(71675503421/100000000000000),(86853/20000000000),(-1818699/100000000000000),(70499/50000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((109/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-635710256081971/100000000000000),(-372281316071/4000000000000),(11052449169/100000000000000),(69709811/100000000000000),(848221/5000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((109/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-5080136513317/390625000000),(-9734682610133/50000000000000),(839217893/5000000000000),(10007781/6250000000000),(17782481/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((109/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1689446006897717/100000000000000),(2982318337521/12500000000000),(-10345274271/25000000000000),(-75572447/50000000000000),(23457197/50000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((109/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(2422695613657819/50000000000000),(18011671022289/25000000000000),(-69738351829/100000000000000),(-583298031/100000000000000),(6580803/5000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((109/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(5208778674543947/100000000000000),(82829237145947/100000000000000),(-250053809/50000000000000),(-82878313/10000000000000),(152619767/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((109/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(6830589291939/6250000000000),(139069010441/100000000000000),(-119844431/100000000000000),(-1143423/100000000000000),(127019/50000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((109/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((109/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((109/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((109/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(28652971336293543/50000000000000),(70840999034613/100000000000000),(-15652691509/20000000000000),(-562051309/100000000000000),(137367551/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((109/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(34900394387/20000000000000),(-215717489/100000000000000),(504987/100000000000000),(99/12500000000000),(53/12500000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((109/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(1136177687601/12500000000000),(66651202797/50000000000000),(-76623097/50000000000000),(-492817/50000000000000),(291539/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((109/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((109/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(20979812275053/100000000000000),(16041088791/6250000000000),(-75950319/12500000000000),(1908303/100000000000000),(1239981/10000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((109/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(3849506839459/50000000000000),(23553056397/100000000000000),(-878113/200000000000),(945667/20000000000000),(4746399/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((109/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((109/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((109/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((109/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((109/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((109/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (109/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((109/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((109/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((109/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (109/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((109/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(35452106309/100000000000000),(-16331219/50000000000000),(378687/25000000000000),(-691/25000000000000),(69/100000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((109/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(408557828253171/100000000000000),(-440314245779/25000000000000),(-8964794267/100000000000000),(-13101051/20000000000000),(187551/10000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((109/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((109/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((109/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((109/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (109/40) (1/40))

def c223 : Certificate := ⟨(35721/1600),(189/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((109/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(4428010881/2560000),(20090889/640000),(257123/1280000),(329/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((109/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((109/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(80076473031/100000000000000),(-268712997/25000000000000),(10820657/100000000000000),(-9683/10000000000000),(13/1562500000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((109/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(69253807401049/50000000000000),(654599150929/100000000000000),(1060181623/100000000000000),(-319117/12500000000000),(2929639/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((109/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((109/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (109/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((109/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (109/40) (1/40))

def c231 : Certificate := ⟨(22804621088537/100000000000000),(-34042477481/100000000000000),(-1079151/25000000000000),(110757/50000000000000),(76667/50000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((109/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(8781515645851/100000000000000),(851061937/625000000000),(4316603/25000000000000),(-886057/100000000000000),(36571/5000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((109/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((109/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(771150170383/100000000000000),(23915563889/100000000000000),(188454949/100000000000000),(-27149/25000000000000),(519/390625000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((109/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((109/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(1823672939773/20000000000000),(280686319713/100000000000000),(1081481541/50000000000000),(-1791911/100000000000000),(158369/10000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((109/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-76788216237279/6250000000000),(-19026722406723/100000000000000),(-115223251/6250000000000),(63401799/50000000000000),(5123999/5000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((109/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-102668603536281/4000000000000),(-41471408500711/100000000000000),(-7779324201/25000000000000),(264321813/100000000000000),(22340293/10000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((109/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(3155487036579753/100000000000000),(5661062933671/12500000000000),(-13249940217/25000000000000),(-68942189/20000000000000),(141885773/50000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((109/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(9497691015963601/100000000000000),(75626123144591/50000000000000),(75689704077/100000000000000),(-1052940137/100000000000000),(817588651/100000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((109/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(5444336936633203/50000000000000),(97704439681503/50000000000000),(223311527491/50000000000000),(-1025233093/100000000000000),(1060484529/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((109/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(23666836292417/20000000000000),(296255383729/100000000000000),(222987773/100000000000000),(-188071/10000000000000),(199463/12500000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((109/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((109/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((109/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((109/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(7729749622671909/12500000000000),(72949922673891/50000000000000),(23961719517/100000000000000),(-1134990391/100000000000000),(883750939/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((109/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(32342574107/20000000000000),(-95385863/25000000000000),(418773/50000000000000),(1139/100000000000000),(467/20000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((109/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(17608387083653/100000000000000),(10978251437/4000000000000),(67874831/100000000000000),(-800667/50000000000000),(993851/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((109/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((109/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((109/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (109/40) (1/40))

def c259 : Certificate := ⟨(19397782481427/100000000000000),(-73892585441/100000000000000),(20225717/12500000000000),(127693/100000000000000),(167917/50000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((109/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(466851459881/6250000000000),(98523447253/100000000000000),(-215740983/100000000000000),(-170259/100000000000000),(353211/50000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((109/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((109/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(278976365559/50000000000000),(7359330429/50000000000000),(32419309/50000000000000),(-450547/100000000000000),(53531/50000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((109/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((109/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(3306039419177/50000000000000),(173325644707/100000000000000),(92722727/12500000000000),(-540161/10000000000000),(639137/50000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((109/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-41810134909923/4000000000000),(-13773821394571/100000000000000),(7603911841/25000000000000),(1486151/6250000000000),(3958303/4000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((109/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2169571030348957/100000000000000),(-29645237466391/100000000000000),(6420500723/12500000000000),(55455319/50000000000000),(212787891/100000000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((109/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(271374620841353/10000000000000),(671592068807/2000000000000),(-12968804589/12500000000000),(60991297/100000000000000),(1092039/400000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((109/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(8045811146663901/100000000000000),(27157891458003/25000000000000),(-51762169717/25000000000000),(-353500001/100000000000000),(195510179/25000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((109/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(2261272025879949/25000000000000),(5421295129971/4000000000000),(-781206423/1000000000000),(-1135688231/100000000000000),(975506279/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((109/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(11549719944731/10000000000000),(52941388841/25000000000000),(-91660837/25000000000000),(-158213/20000000000000),(759953/50000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((109/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((109/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((109/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((109/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(60433037479553213/100000000000000),(105449840838239/100000000000000),(-45050190693/20000000000000),(-138127437/50000000000000),(834785013/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((109/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(165472404119/100000000000000),(-144366719/50000000000000),(560287/50000000000000),(-569/25000000000000),(2303/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((109/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(598684989583/4000000000000),(198152490797/100000000000000),(-83847699/20000000000000),(-21301/6250000000000),(1829147/100000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((109/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((109/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(26617960729467/20000000000000),(42410677423/3125000000000),(-2535941291/20000000000000),(-32726733/50000000000000),(16525719/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((109/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(48840294916453/100000000000000),(49957542981/100000000000000),(-5111429369/100000000000000),(11437113/50000000000000),(1757719/25000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((109/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((109/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((109/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((109/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((109/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((109/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (109/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((109/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(546227537570400021/50000000000000),(503245773547837/50000000000000),(-45749615777077/100000000000000),0,(141173/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((109/40)+(1/40)*x)) := (SharedCertificates.h297 (109/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(1144211811/12500000000000),(-4216703/50000000000000),(195553/50000000000000),(-357/50000000000000),(1/5000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((109/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(332557296410949/50000000000000),(1506874511319/100000000000000),(10732294533/100000000000000),(53180601/100000000000000),(114833/5000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((109/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((109/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (109/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((109/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (109/40) (1/40))

def c307 : Certificate := ⟨(441323703402583/12500000000000),(11091229182759/50000000000000),0,0,(109/10000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((109/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (109/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((109/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (109/40) (1/40))

def c311 : Certificate := ⟨(2194410372779077/100000000000000),(2817541634481/100000000000000),0,0,(1089/100000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((109/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (109/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(569629097413/12500000000000),(-585106129/10000000000000),(1502509/20000000000000),(-4823/50000000000000),(17/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((109/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(10055632913447/6250000000000),(160856987197/20000000000000),(-1032672101/100000000000000),(662953/50000000000000),(699/25000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((109/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((109/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (109/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((109/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (109/40) (1/40))

def c316 : Certificate := ⟨(10848572601719/50000000000000),(-37863009063/100000000000000),(57344127/50000000000000),(-69479/20000000000000),(111/10000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((109/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(6605709593123/50000000000000),(151452036251/100000000000000),(-458753021/100000000000000),(55583/4000000000000),(5781/100000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((109/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((109/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1745415969147/100000000000000),(160071707/400000000000),(108161623/100000000000000),(-1022417/100000000000000),(3937/50000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((109/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((109/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(5120950797327/25000000000000),(232177156421/50000000000000),(145519809/12500000000000),(-600391/5000000000000),(9563/10000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((109/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-369378496993963/20000000000000),(-2111091414333/10000000000000),(8123566099/12500000000000),(-49052341/25000000000000),(83811/10000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((109/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1971599040128759/50000000000000),(-23996388893829/50000000000000),(113536518569/100000000000000),(-30674199/12500000000000),(2729133/100000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((109/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(1141360989744471/25000000000000),(45996453118023/100000000000000),(-27027078323/12500000000000),(839894391/100000000000000),(981831/25000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((109/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(14475150084692013/100000000000000),(172015880135547/100000000000000),(-115384376043/25000000000000),(136872673/12500000000000),(1954287/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((109/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(17696735656612109/100000000000000),(248321935154093/100000000000000),(-215409251141/100000000000000),(-165121389/20000000000000),(454601/2000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((109/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(128168254341639/100000000000000),(85730499813/25000000000000),(-809344419/100000000000000),(1756733/100000000000000),(4859/25000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((109/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((109/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((109/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((109/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(66583656738083863/100000000000000),(80996103081203/50000000000000),(-507351624193/100000000000000),(1310593067/100000000000000),(14448927/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((109/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(37546751297/25000000000000),(-45673979/12500000000000),(406671/20000000000000),(-167/1562500000000),(21/25000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((109/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(13289098649351/50000000000000),(77071212753/25000000000000),(-54439207/6250000000000),(676243/25000000000000),(9651/12500000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((109/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((109/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((109/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (109/40) (1/40))

def c344 : Certificate := ⟨(17162362024739/100000000000000),(-71069834953/100000000000000),(38555327/10000000000000),(-2091623/100000000000000),(2877/25000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((109/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(5225091983507/50000000000000),(2961243123/3125000000000),(-514071027/100000000000000),(278883/10000000000000),(7339/25000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((109/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((109/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(273015862361/25000000000000),(990257133/5000000000000),(-8824289/50000000000000),(-39139/10000000000000),(14151/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((109/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((109/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((109/40)+(1/40)*x)) := (SharedCertificates.h144 (109/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(12876516114321/100000000000000),(231452690391/100000000000000),(-117200487/50000000000000),(-2219359/50000000000000),(42021/25000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((109/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((109/40)+(1/40)*x)) := (SharedCertificates.h148 (109/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-91355008484967/6250000000000),(-2645996040153/20000000000000),(18024644517/25000000000000),(-3919529/1000000000000),(4127327/100000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((109/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((109/40)+(1/40)*x)) := (SharedCertificates.h151 (109/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-615759954792017/20000000000000),(-14650190265937/50000000000000),(146451695567/100000000000000),(-29050561/4000000000000),(5101487/50000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((109/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((109/40)+(1/40)*x)) := (SharedCertificates.h154 (109/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(3701580586945549/100000000000000),(30503107716269/100000000000000),(-194550632281/100000000000000),(1201343203/100000000000000),(13748893/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((109/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((109/40)+(1/40)*x)) := (SharedCertificates.h157 (109/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(5679757573193893/50000000000000),(106193009423149/100000000000000),(-275114776463/50000000000000),(1407940737/50000000000000),(4546271/12500000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((109/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((109/40)+(1/40)*x)) := (SharedCertificates.h160 (109/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(6673436813240693/50000000000000),(71610500865741/50000000000000),(-570310007671/100000000000000),(403157721/20000000000000),(62203349/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((109/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((109/40)+(1/40)*x)) := (SharedCertificates.h41 (109/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(7624526961467/6250000000000),(52331175633/25000000000000),(-130723829/12500000000000),(518627/10000000000000),(72863/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((109/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((109/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((109/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((109/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((109/40)+(1/40)*x)) := (SharedCertificates.h167 (109/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(63626372528741311/100000000000000),(101564747733673/100000000000000),(-551719607031/100000000000000),(2932232723/100000000000000),(21789437/50000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((109/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(31433506587/20000000000000),(-250881517/100000000000000),(1763311/100000000000000),(-6117/50000000000000),(79/50000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((109/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(5244238000673/25000000000000),(191612076039/100000000000000),(-1020310301/100000000000000),(2745771/50000000000000),(151981/100000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((109/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((109/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(79074059410453/25000000000000),(2020741917263/50000000000000),(57015601/100000000000000),(104956651/100000000000000),(2818061/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((109/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(29018003453377/25000000000000),(83646494619/20000000000000),(-3816072011/100000000000000),(14705207/20000000000000),(846081/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((109/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((109/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(5134903805908203/25000000000000),(222899278564453/25000000000000),(1580173/10240000),(109/81920),(286132813/50000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((109/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(52441/1600),(229/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((109/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(12008989/64000),(157323/64000),(687/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((109/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(963515676893902263/25000000000000),(43557918198066851/20000000000000),(1061545889218591/20000000000000),(7279145441809/10000000000000),(123423603661/20000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((109/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(129733229/5000000000000),(-29324429/20000000000000),(471217/10000000000000),(-113361/100000000000000),(1697/50000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((109/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(5467292688631/100000000000000),(-1696073377/10000000000000),(-13638951/10000000000000),(3665731/100000000000000),(13595723/100000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((109/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((109/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((109/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel34

namespace Hf4Quad.Panel35
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(111/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((111/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (111/40) (1/40)

def c3 : Certificate := ⟨(243142857142857/50000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((111/40)+(1/40)*x)) := (SharedCertificates.h2 (111/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((111/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-394857142857143/100000000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((111/40)+(1/40)*x)) := (SharedCertificates.h4 (111/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(12321/1600),(111/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((111/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(932223809523809/100000000000000),(671873015873/4000000000000),(75661375661/100000000000000),0,(1/50000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((111/40)+(1/40)*x)) := (SharedCertificates.h8 (111/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((111/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((111/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1367631/64000),(36963/64000),(333/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((111/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(266485433/1280000),(7202309/1280000),(5069192708333/100000000000000),(608912037/4000000000000),(1/50000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((111/40)+(1/40)*x)) := (SharedCertificates.h13 (111/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((111/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((111/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(151807041/2560000),(1367631/640000),(36963/1280000),(111/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((111/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(4141561138392857/25000000000000),(119396357142857/20000000000000),(8067321428571/100000000000000),(6056547619/12500000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((111/40)+(1/40)*x)) := (SharedCertificates.h18 (111/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((111/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(16455646045898437/100000000000000),(185311329345703/25000000000000),(1367631/10240000),(12321/10240000),(542968751/100000000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((111/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(21441097329433593/20000000000000),(1207268993774413/25000000000000),(87010377929687/100000000000000),(156775455729/20000000000000),(1768670433/50000000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((111/40)+(1/40)*x)) := (SharedCertificates.h22 (111/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((111/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(22832208888684081/50000000000000),(617086726721191/25000000000000),(5559339880371/10000000000000),(333894287109/50000000000000),(2264184573/50000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((111/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(102539570924418243/100000000000000),(5542679509428009/100000000000000),(62417562043107/50000000000000),(749760505021/50000000000000),(101684649/1000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((111/40)+(1/40)*x)) := (SharedCertificates.h26 (111/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((111/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(126718759332196649/100000000000000),(124863642359991/1562500000000),(107990177176207/50000000000000),(3242948263547/100000000000000),(14687073983/50000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((111/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(30070562730418093/100000000000000),(1896341793810149/100000000000000),(51252480913787/100000000000000),(192389192619/25000000000000),(348526597/5000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((111/40)+(1/40)*x)) := (SharedCertificates.h30 (111/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((111/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((111/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((111/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((111/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((111/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (111/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((111/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((111/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (111/40) (1/40))

def c43 : Certificate := ⟨(22801/1600),(151/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((111/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((111/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(33415409933/100000000000000),(-110647053/25000000000000),(4396571/100000000000000),(-19411/50000000000000),(331/100000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((111/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-51890440267383/5000000000000),(27506864823/25000000000000),(-184724273/25000000000000),(4967137/100000000000000),(20415583/100000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((111/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((111/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (111/40) (1/40))

def c52 : Certificate := ⟨(31833333333333/20000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((111/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (111/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((111/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (111/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((111/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (111/40) (1/40))

def c56 : Certificate := ⟨(10889292196007/50000000000000),(-3952556151/10000000000000),(71734231/100000000000000),(-13019/10000000000000),(239/100000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((111/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(12885662431941/100000000000000),(158102246039/100000000000000),(-143468463/50000000000000),(130189/25000000000000),(77/6250000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((111/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((111/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((111/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((111/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((111/40)+(1/40)*x)) := (SharedCertificates.h61 (111/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-190361691825771/100000000000000),(-2457901705209/100000000000000),(592204487/20000000000000),(-1325987/50000000000000),(34017/100000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((111/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((111/40)+(1/40)*x)) := (SharedCertificates.h61 (111/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-8197145562223/4000000000000),(-2831114471563/100000000000000),(132360563/12500000000000),(1555221/50000000000000),(1983/4000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((111/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((111/40)+(1/40)*x)) := (SharedCertificates.h67 (111/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-928402782890943/100000000000000),(-5877980928861/50000000000000),(510437171/3125000000000),(-5464333/20000000000000),(108137/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((111/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((111/40)+(1/40)*x)) := (SharedCertificates.h67 (111/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-127703402355993/12500000000000),(-14049816435383/100000000000000),(626781823/10000000000000),(14748389/100000000000000),(263379/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((111/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((111/40)+(1/40)*x)) := (SharedCertificates.h72 (111/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(1221351120620231/100000000000000),(13175108336779/100000000000000),(-48602376943/100000000000000),(20296659/20000000000000),(219147/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((111/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((111/40)+(1/40)*x)) := (SharedCertificates.h72 (111/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(3020747475731313/100000000000000),(1618353549851/4000000000000),(-38130961239/100000000000000),(-81058533/100000000000000),(542217/50000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((111/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((111/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((111/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(127431727826981/100000000000000),(356949535521/100000000000000),(-198929049/50000000000000),(26841/10000000000000),(5261/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((111/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(91063961582349/781250000000),(2299117788673/20000000000000),(-57255239669/100000000000000),(128463073/100000000000000),(1007311/100000000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((111/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(428956738991/50000000000000),(-423046603/50000000000000),(504851/10000000000000),(-18591/100000000000000),(13/10000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((111/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(25915399730099/100000000000000),(80385872869/25000000000000),(-129236851/25000000000000),(34631/3125000000000),(1103/5000000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((111/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((111/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((111/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (111/40) (1/40))

def c87 : Certificate := ⟨(17316017316017/100000000000000),(-74961113923/100000000000000),(162253493/50000000000000),(-1404793/100000000000000),(191/3125000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((111/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(10245310245309/100000000000000),(19989630379/20000000000000),(-432675983/100000000000000),(374611/20000000000000),(7689/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((111/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((111/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((111/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((111/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((111/40)+(1/40)*x)) := (SharedCertificates.h61 (111/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-29946465271137/20000000000000),(-380538526371/25000000000000),(5990033739/100000000000000),(-11668077/50000000000000),(134091/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((111/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((111/40)+(1/40)*x)) := (SharedCertificates.h61 (111/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-31754976961397/20000000000000),(-1704878230031/100000000000000),(5797652219/100000000000000),(-18845277/100000000000000),(172133/50000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((111/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((111/40)+(1/40)*x)) := (SharedCertificates.h67 (111/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-366719348355869/50000000000000),(-366486662983/5000000000000),(29864292777/100000000000000),(-15355913/12500000000000),(1212803/100000000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((111/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((111/40)+(1/40)*x)) := (SharedCertificates.h67 (111/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-792314787108899/100000000000000),(-4240191483951/50000000000000),(912327763/3125000000000),(-23968711/25000000000000),(1706237/100000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((111/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((111/40)+(1/40)*x)) := (SharedCertificates.h72 (111/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(497291233849339/50000000000000),(1104226302127/12500000000000),(-47487742559/100000000000000),(11893977/5000000000000),(2052629/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((111/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((111/40)+(1/40)*x)) := (SharedCertificates.h72 (111/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(2355311270437249/100000000000000),(12393674028217/50000000000000),(-1430322937/1562500000000),(153986451/50000000000000),(1036789/20000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((111/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((111/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((111/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(30385071077711/25000000000000),(110188150141/50000000000000),(-854113629/100000000000000),(3265007/100000000000000),(9893/25000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((111/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5727125518283789/50000000000000),(8013683646607/100000000000000),(-2420215651/5000000000000),(258422497/100000000000000),(6866871/100000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((111/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(109129789107/12500000000000),(-610799679/100000000000000),(4116687/100000000000000),(-25159/100000000000000),(9/1562500000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((111/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(5140692444483/25000000000000),(101008405797/50000000000000),(-853625353/100000000000000),(229731/6250000000000),(70923/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((111/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((111/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-482354535718757/100000000000000),(-5382416177531/100000000000000),(3614139753/25000000000000),(-10543111/20000000000000),(10602549/100000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((111/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(9009009009009/25000000000000),(-162324486649/50000000000000),(116990621/4000000000000),(-26349239/100000000000000),(11977/5000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((111/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-86910727156533/50000000000000),(-186825192739/50000000000000),(1715158101/20000000000000),(-96255971/100000000000000),(7041387/100000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((111/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((111/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((111/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((111/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((111/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((111/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((111/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((111/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((111/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((111/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (111/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((111/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((111/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(1784498723/100000000000000),(-64306261/100000000000000),(1448339/100000000000000),(-26097/100000000000000),(29/6250000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((111/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(13652012647663/12500000000000),(-340869491441/100000000000000),(2703346169/100000000000000),(-2070441/10000000000000),(55737593/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((111/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((111/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (111/40) (1/40))

def c134 : Certificate := ⟨(44121/1600),(211/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((111/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((111/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(4415011037527/100000000000000),(-29238483693/100000000000000),(96816171/50000000000000),(-641167/50000000000000),(1069/12500000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((111/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(24349337748341/20000000000000),(17909484963/5000000000000),(15490587/4000000000000),(-641171/25000000000000),(456087/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((111/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((111/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (111/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((111/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (111/40) (1/40))

def c140 : Certificate := ⟨(5927728816221/25000000000000),(-314651463/1562500000000),(-4669357/100000000000000),(33329/20000000000000),(6487/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((111/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(5156338940463/100000000000000),(3222030981/4000000000000),(1167339/6250000000000),(-333291/50000000000000),(28767/25000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((111/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((111/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(265878312689/100000000000000),(8306941907/100000000000000),(13362083/20000000000000),(-38653/100000000000000),(3281/25000000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((111/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((111/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(126524823133/4000000000000),(98398300643/100000000000000),(390676553/50000000000000),(-567041/100000000000000),(156937/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((111/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-721724350446707/100000000000000),(-11269486765483/100000000000000),(-2494698763/100000000000000),(2347973/2500000000000),(4028797/25000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((111/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-23140460266477/1562500000000),(-237166643557/1000000000000),(-3642693059/25000000000000),(192182273/100000000000000),(34056767/100000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((111/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(238603207/12500000),(14298094057141/50000000000000),(-6470538837/50000000000000),(-15813689/6250000000000),(1397443/3125000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((111/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(2756290704046013/50000000000000),(43795201742357/50000000000000),(10583744961/25000000000000),(-365382307/50000000000000),(1965461/1562500000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((111/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(1196530130205299/20000000000000),(10249208345831/10000000000000),(167145878541/100000000000000),(-373921341/50000000000000),(149214507/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((111/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(22115711238723/20000000000000),(169408490957/100000000000000),(104165263/100000000000000),(-1371817/100000000000000),(12163/5000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((111/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((111/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((111/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((111/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(57961130615835791/100000000000000),(42952040470461/50000000000000),(26895065903/100000000000000),(-743969469/100000000000000),(132127479/100000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((111/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(86264707863/50000000000000),(-127852759/50000000000000),(298923/100000000000000),(189/10000000000000),(403/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((111/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(10321832213143/100000000000000),(80765512459/50000000000000),(44181413/100000000000000),(-649103/50000000000000),(143349/50000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((111/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((111/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((111/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (111/40) (1/40))

def c175 : Certificate := ⟨(21494279461221/100000000000000),(-49645527471/100000000000000),(60991359/100000000000000),(33857/10000000000000),(6527/10000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((111/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(4674294051703/100000000000000),(33097018313/50000000000000),(-40660907/50000000000000),(-112857/25000000000000),(57707/50000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((111/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((111/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(218490248817/100000000000000),(6188207833/100000000000000),(36214063/100000000000000),(-149863/100000000000000),(11477/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((111/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((111/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(520291446479/20000000000000),(9173841113/12500000000000),(423346163/100000000000000),(-455063/25000000000000),(137501/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((111/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-654279567477749/100000000000000),(-2315503154903/25000000000000),(5725653569/50000000000000),(63323639/100000000000000),(3232689/20000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((111/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1339385285380961/100000000000000),(-485008950419/2500000000000),(708261907/4000000000000),(147425493/100000000000000),(16961257/50000000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((111/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(1736996403181707/100000000000000),(4738256226771/20000000000000),(-21116954983/50000000000000),(-66682459/50000000000000),(44690053/100000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((111/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(4989201073840367/100000000000000),(35880463318713/50000000000000),(-14618476703/20000000000000),(-267648533/50000000000000),(125496577/100000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((111/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(2687214306166097/50000000000000),(16563495816029/20000000000000),(-2666360041/50000000000000),(-97820949/12500000000000),(146004719/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((111/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(109567078352223/100000000000000),(27715256217/20000000000000),(-25285913/20000000000000),(-1052719/100000000000000),(48461/20000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((111/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((111/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((111/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((111/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(14361826804887847/25000000000000),(17630349525233/25000000000000),(-16297708421/20000000000000),(-256786653/50000000000000),(131114679/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((111/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(17407256291/10000000000000),(-106844351/50000000000000),(509241/100000000000000),(627/100000000000000),(201/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((111/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(4677702813627/50000000000000),(13267796163/10000000000000),(-31777121/20000000000000),(-447701/50000000000000),(17411/6250000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((111/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((111/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(21490711989453/100000000000000),(63562470969/25000000000000),(-149050067/25000000000000),(1874649/100000000000000),(11807559/100000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((111/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(7744400716919/100000000000000),(10926101973/50000000000000),(-205856823/50000000000000),(4384681/100000000000000),(4436479/100000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((111/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((111/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((111/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((111/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((111/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((111/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (111/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((111/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((111/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((111/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (111/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((111/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(8848204843/25000000000000),(-13317253/50000000000000),(749869/50000000000000),(-2243/100000000000000),(33/50000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((111/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(40499892604819/10000000000000),(-898956193543/50000000000000),(-4682770923/50000000000000),(-8516071/12500000000000),(183687/10000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((111/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((111/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((111/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((111/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (111/40) (1/40))

def c223 : Certificate := ⟨(36481/1600),(191/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((111/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(4590805521/2560000),(20609091/640000),(261083/1280000),(331/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((111/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((111/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(15593857969/20000000000000),(-516352913/50000000000000),(10258667/100000000000000),(-18117/20000000000000),(767/100000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((111/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(139821033706591/100000000000000),(26352392983/4000000000000),(261322649/25000000000000),(-2415407/100000000000000),(2803011/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((111/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((111/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (111/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((111/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (111/40) (1/40))

def c231 : Certificate := ⟨(22736520615499/100000000000000),(-34057132357/100000000000000),(-1510953/50000000000000),(210331/100000000000000),(29167/20000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((111/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(9053917538003/100000000000000),(68114264713/50000000000000),(12087623/100000000000000),(-841329/100000000000000),(699479/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((111/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((111/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(819734227849/100000000000000),(12334018717/50000000000000),(187770929/100000000000000),(-119413/100000000000000),(6543/5000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((111/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((111/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(9688374612147/100000000000000),(57863235581/20000000000000),(430368383/20000000000000),(-1915099/100000000000000),(1559497/100000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((111/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-158333909734033/12500000000000),(-19032601341209/100000000000000),(-1102138959/100000000000000),(120497551/100000000000000),(49004727/50000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((111/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-662445070904241/25000000000000),(-41592751924557/100000000000000),(-369565807/1250000000000),(63334181/25000000000000),(42835751/20000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((111/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(3245849330314213/100000000000000),(22536226827291/50000000000000),(-13751142391/25000000000000),(-161992649/50000000000000),(67857757/25000000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((111/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(9800489936677621/100000000000000),(151542551493611/100000000000000),(69505822599/100000000000000),(-252380203/25000000000000),(391622617/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((111/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(5640634984638649/50000000000000),(49295789456573/25000000000000),(220267837567/50000000000000),(-502548619/50000000000000),(1022926751/100000000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((111/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(23785513860771/20000000000000),(148562548143/50000000000000),(8477847/4000000000000),(-1802071/100000000000000),(764909/50000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((111/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((111/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((111/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((111/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(15532470884266281/25000000000000),(36495566130003/25000000000000),(8646733929/50000000000000),(-544455767/50000000000000),(848597151/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((111/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(40238285631/25000000000000),(-378180401/100000000000000),(843783/100000000000000),(943/100000000000000),(2221/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((111/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(2269694816521/12500000000000),(274708937041/100000000000000),(29268697/50000000000000),(-60543/4000000000000),(23933/1250000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((111/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((111/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((111/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (111/40) (1/40))

def c259 : Certificate := ⟨(19250645480773/100000000000000),(-14648795279/20000000000000),(40615973/25000000000000),(23139/25000000000000),(316381/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((111/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(3832903012817/50000000000000),(97658635193/100000000000000),(-8664741/4000000000000),(-123409/100000000000000),(168453/25000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((111/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((111/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(293822910113/50000000000000),(7486321541/50000000000000),(31080489/50000000000000),(-221007/50000000000000),(13107/12500000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((111/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((111/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(6961654265319/100000000000000),(176228395657/100000000000000),(709703197/100000000000000),(-2645747/50000000000000),(78231/6250000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((111/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-536339588338303/50000000000000),(-2730380188701/20000000000000),(30538019983/100000000000000),(2146797/12500000000000),(94392077/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((111/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-2228655192138917/100000000000000),(-29438509943123/100000000000000),(51985534047/100000000000000),(6036901/6250000000000),(12709269/6250000000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((111/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(2780490935859499/100000000000000),(33165401236427/100000000000000),(-103334588951/100000000000000),(77179959/100000000000000),(10416201/4000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((111/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(516390210538689/6250000000000),(107799351778683/100000000000000),(-104502530323/50000000000000),(-299851913/100000000000000),(746937397/100000000000000)⟩
theorem h273 : c273.Valid (fun x => f273 ((111/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(1863166285384797/20000000000000),(67603266790687/50000000000000),(-42368822181/50000000000000),(-1071193997/100000000000000),(936337389/100000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((111/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(57959628935747/50000000000000),(52572478367/25000000000000),(-46384509/12500000000000),(-10763/1562500000000),(4539/312500000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((111/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((111/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((111/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((111/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(60643034060312917/100000000000000),(20909148906371/20000000000000),(-45348786601/20000000000000),(-111318553/50000000000000),(798687751/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((111/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(82449700571/50000000000000),(-284278829/100000000000000),(1106641/100000000000000),(-1183/50000000000000),(2189/100000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((111/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(3072350046879/20000000000000),(24558978461/12500000000000),(-421002609/100000000000000),(-249663/100000000000000),(438669/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((111/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((111/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(33938210130839/25000000000000),(652814616259/50000000000000),(-3269665613/25000000000000),(-13517829/20000000000000),(987947/6250000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((111/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(48919942530939/100000000000000),(5955363549/20000000000000),(-2490645567/50000000000000),(1282503/6250000000000),(6585001/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((111/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((111/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((111/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((111/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((111/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((111/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (111/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((111/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(547142529885941543/50000000000000),(823493083987369/100000000000000),(-45749615777077/100000000000000),0,(70693/50000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((111/40)+(1/40)*x)) := (SharedCertificates.h297 (111/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(4569193333/50000000000000),(-6877/100000000000),(38723/10000000000000),(-579/100000000000000),(19/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((111/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(133634340686501/20000000000000),(155045543011/10000000000000),(11061329991/100000000000000),(56490823/100000000000000),(273771/12500000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((111/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((111/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (111/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((111/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (111/40) (1/40))

def c307 : Certificate := ⟨(1787477271975851/50000000000000),(11091229182759/50000000000000),0,0,(273/25000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((111/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (111/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((111/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (111/40) (1/40))

def c311 : Certificate := ⟨(2200045456048039/100000000000000),(2817541634481/100000000000000),0,0,(273/25000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((111/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (111/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(227268031497/5000000000000),(-5821126461/100000000000000),(3727483/50000000000000),(-2387/25000000000000),(17/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((111/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(162494576379031/100000000000000),(200042526093/25000000000000),(-256189327/25000000000000),(656179/50000000000000),(2781/100000000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((111/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((111/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (111/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((111/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (111/40) (1/40))

def c316 : Certificate := ⟨(21621875175903/100000000000000),(-37408391363/100000000000000),(11262889/10000000000000),(-169551/50000000000000),(1079/100000000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((111/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(13512499296383/100000000000000),(149633565449/100000000000000),(-450515563/100000000000000),(1356403/100000000000000),(1413/25000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((111/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((111/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1825876372347/100000000000000),(10109617239/25000000000000),(51075107/50000000000000),(-490839/50000000000000),(7649/100000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((111/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((111/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(21417073404231/100000000000000),(117217220993/25000000000000),(546814571/50000000000000),(-11505709/100000000000000),(9273/10000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((111/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-236106989950071/12500000000000),(-20853296127663/100000000000000),(63825053429/100000000000000),(-191636519/100000000000000),(818619/100000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((111/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-1009682861458239/25000000000000),(-5942695284617/12500000000000),(56037388453/50000000000000),(-9674287/4000000000000),(665307/25000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((111/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(4656578670906477/100000000000000),(22570785784197/50000000000000),(-211247409309/100000000000000),(816636353/100000000000000),(1914161/50000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((111/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(3704336105335977/25000000000000),(8509140147761/5000000000000),(-18200712577/4000000000000),(269566567/25000000000000),(380637/4000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((111/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(1137031961409727/6250000000000),(123725292675129/50000000000000),(-220217592693/100000000000000),(-388764191/50000000000000),(22194653/100000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((111/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(128850874965113/100000000000000),(169852799927/50000000000000),(-49930057/6250000000000),(216391/12500000000000),(18953/100000000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((111/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((111/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((111/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((111/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(66905622186995957/100000000000000),(159978443436343/100000000000000),(-249775280513/50000000000000),(644891779/50000000000000),(14046567/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((111/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(18683033789/12500000000000),(-178692467/50000000000000),(1970519/100000000000000),(-5131/50000000000000),(81/100000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((111/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(6797826097341/25000000000000),(304832916979/100000000000000),(-213752709/25000000000000),(1317021/50000000000000),(75153/100000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((111/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((111/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((111/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (111/40) (1/40))

def c344 : Certificate := ⟨(4255437003629/25000000000000),(-69552363121/100000000000000),(373271013/100000000000000),(-400651/20000000000000),(2727/25000000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((111/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(10637669313977/100000000000000),(92736484159/100000000000000),(-99538937/20000000000000),(1335503/50000000000000),(1127/4000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((111/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((111/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(226320016867/20000000000000),(4932500259/25000000000000),(-795427/4000000000000),(-44353/12500000000000),(13507/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((111/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((111/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((111/40)+(1/40)*x)) := (SharedCertificates.h144 (111/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(13338449262163/100000000000000),(115231787817/50000000000000),(-259727347/100000000000000),(-501197/12500000000000),(160483/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((111/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((111/40)+(1/40)*x)) := (SharedCertificates.h148 (111/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-1487854803832659/100000000000000),(-3236555555077/25000000000000),(69796966027/100000000000000),(-187699481/50000000000000),(1980887/50000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((111/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((111/40)+(1/40)*x)) := (SharedCertificates.h151 (111/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-15684102409087/500000000000),(-5744635221487/20000000000000),(142178385197/100000000000000),(-272811/39062500000),(9782053/100000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((111/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((111/40)+(1/40)*x)) := (SharedCertificates.h154 (111/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(3761818096052309/100000000000000),(29739092881217/100000000000000),(-187513062117/100000000000000),(1145064529/100000000000000),(13151187/100000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((111/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((111/40)+(1/40)*x)) := (SharedCertificates.h157 (111/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(289243063723181/2500000000000),(52012716283683/50000000000000),(-133417454571/25000000000000),(2704939959/100000000000000),(8715881/25000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((111/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((111/40)+(1/40)*x)) := (SharedCertificates.h160 (111/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(13631050430274871/100000000000000),(140963779242503/100000000000000),(-69793026381/12500000000000),(493206513/25000000000000),(59586209/100000000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((111/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((111/40)+(1/40)*x)) := (SharedCertificates.h41 (111/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(122406938712289/100000000000000),(102601484677/50000000000000),(-203055009/20000000000000),(1246797/25000000000000),(69857/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((111/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((111/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((111/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((111/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((111/40)+(1/40)*x)) := (SharedCertificates.h167 (111/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(3989207397632261/6250000000000),(99392574226993/100000000000000),(-534486116967/100000000000000),(703315773/25000000000000),(8358423/20000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((111/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(15667272661/10000000000000),(-9758897/4000000000000),(422971/25000000000000),(-181/1562500000000),(37/25000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((111/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(4271227674939/20000000000000),(23449474023/12500000000000),(-988064289/100000000000000),(5259009/100000000000000),(72287/50000000000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((111/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((111/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(324380275289533/100000000000000),(50537196959/1250000000000),(21561689/3125000000000),(106057089/100000000000000),(1371271/50000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((111/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(14611724112141/12500000000000),(403830967311/100000000000000),(-3389477527/100000000000000),(17188651/25000000000000),(794093/25000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((111/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((111/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(22385608584960937/100000000000000),(238734415283203/25000000000000),(332667/2048000),(14097/10240000),(582031251/100000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((111/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(53361/1600),(231/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((111/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(12326391/64000),(160083/64000),(693/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((111/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(2155732532743634603/50000000000000),(119956956022303479/50000000000000),(1151894739968591/20000000000000),(19458561297821/25000000000000),(650459089597/100000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((111/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(2319397199/100000000000000),(-129064169/100000000000000),(102087/2500000000000),(-96689/100000000000000),(2847/100000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((111/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(1086570832929/20000000000000),(-17463949383/100000000000000),(-23124111/20000000000000),(3264927/100000000000000),(633241/5000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((111/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((111/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((111/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel35

namespace Hf4Quad.Panel36
open Hf4Quad.CompactDag Hf4Quad.RationalModel

def c0 : Certificate := ⟨(113/40),(1/40),0,0,0⟩
theorem h0 : c0.Valid (fun x => f0 ((113/40)+(1/40)*x)) := by
  simpa [Certificate.Valid,Certificate.cubic,c0,f0] using variableModel (113/40) (1/40)

def c3 : Certificate := ⟨(495047619047619/100000000000000),(547619047619/12500000000000),0,0,(1/100000000000000)⟩
theorem h3 : c3.Valid (fun x => f3 ((113/40)+(1/40)*x)) := (SharedCertificates.h2 (113/40) (1/40)).mul h0 (by decide +kernel)

def c5 : Certificate := RationalModel.neg c3
theorem h5 : c5.Valid (fun x => f5 ((113/40)+(1/40)*x)) := h3.neg

def c6 : Certificate := ⟨(-50452380952381/12500000000000),(-547619047619/12500000000000),0,0,(1/50000000000000)⟩
theorem h6 : c6.Valid (fun x => f6 ((113/40)+(1/40)*x)) := (SharedCertificates.h4 (113/40) (1/40)).add h5 (by decide +kernel)

def c7 : Certificate := ⟨(12769/1600),(113/800),(1/1600),0,0⟩
theorem h7 : c7.Valid (fun x => f7 ((113/40)+(1/40)*x)) := h0.mul h0 (by decide +kernel)

def c9 : Certificate := ⟨(193224021164021/20000000000000),(1709947089947/10000000000000),(75661375661/100000000000000),0,(3/100000000000000)⟩
theorem h9 : c9.Valid (fun x => f9 ((113/40)+(1/40)*x)) := (SharedCertificates.h8 (113/40) (1/40)).mul h7 (by decide +kernel)

def c10 : Certificate := RationalModel.neg c9
theorem h10 : c10.Valid (fun x => f10 ((113/40)+(1/40)*x)) := h9.neg

def c11 : Certificate := RationalModel.addExact c6 c10
theorem h11 : c11.Valid (fun x => f11 ((113/40)+(1/40)*x)) := h6.addExact h10

def c12 : Certificate := ⟨(1442897/64000),(38307/64000),(339/64000),(1/64000),0⟩
theorem h12 : c12.Valid (fun x => f12 ((113/40)+(1/40)*x)) := h7.mul h0 (by decide +kernel)

def c14 : Certificate := ⟨(1098246689380787/5000000000000),(145784958767361/25000000000000),(161266547309/3125000000000),(608912037/4000000000000),(3/100000000000000)⟩
theorem h14 : c14.Valid (fun x => f14 ((113/40)+(1/40)*x)) := (SharedCertificates.h13 (113/40) (1/40)).mul h12 (by decide +kernel)

def c15 : Certificate := RationalModel.neg c14
theorem h15 : c15.Valid (fun x => f15 ((113/40)+(1/40)*x)) := h14.neg

def c16 : Certificate := RationalModel.addExact c11 c15
theorem h16 : c16.Valid (fun x => f16 ((113/40)+(1/40)*x)) := h11.addExact h15

def c17 : Certificate := ⟨(163047361/2560000),(1442897/640000),(38307/1280000),(113/640000),(1/2560000)⟩
theorem h17 : c17.Valid (fun x => f17 ((113/40)+(1/40)*x)) := h12.mul h0 (by decide +kernel)

def c19 : Certificate := ⟨(355857335515873/2000000000000),(157458998015873/25000000000000),(522540922619/6250000000000),(1973015873/4000000000000),(109126987/100000000000000)⟩
theorem h19 : c19.Valid (fun x => f19 ((113/40)+(1/40)*x)) := (SharedCertificates.h18 (113/40) (1/40)).mul h17 (by decide +kernel)

def c20 : Certificate := RationalModel.addExact c16 c19
theorem h20 : c20.Valid (fun x => f20 ((113/40)+(1/40)*x)) := h16.addExact h19

def c21 : Certificate := ⟨(8996265523925781/50000000000000),(199032423095703/25000000000000),(1442897/10240000),(12769/10240000),(69091797/12500000000000)⟩
theorem h21 : c21.Valid (fun x => f21 ((113/40)+(1/40)*x)) := h17.mul h0 (by decide +kernel)

def c23 : Certificate := ⟨(117218007826558879/100000000000000),(162082422326547/3125000000000),(91798894061053/100000000000000),(40618979673/5000000000000),(450120263/12500000000000)⟩
theorem h23 : c23.Valid (fun x => f23 ((113/40)+(1/40)*x)) := (SharedCertificates.h22 (113/40) (1/40)).mul h21 (by decide +kernel)

def c24 : Certificate := RationalModel.addExact c20 c23
theorem h24 : c24.Valid (fun x => f24 ((113/40)+(1/40)*x)) := h20.addExact h23

def c25 : Certificate := ⟨(25414450105090331/50000000000000),(674719914294433/25000000000000),(5970972692871/10000000000000),(704539550781/100000000000000),(938544923/20000000000000)⟩
theorem h25 : c25.Valid (fun x => f25 ((113/40)+(1/40)*x)) := h21.mul h0 (by decide +kernel)

def c27 : Certificate := ⟨(2282728597799013/2000000000000),(606034141008587/10000000000000),(67039174890329/50000000000000),(1582045425139/100000000000000),(10537525541/100000000000000)⟩
theorem h27 : c27.Valid (fun x => f27 ((113/40)+(1/40)*x)) := (SharedCertificates.h26 (113/40) (1/40)).mul h25 (by decide +kernel)

def c28 : Certificate := RationalModel.addExact c24 c27
theorem h28 : c28.Valid (fun x => f28 ((113/40)+(1/40)*x)) := h24.addExact h27

def c29 : Certificate := ⟨(14359164309376037/10000000000000),(8895057536781609/100000000000000),(236151970003049/100000000000000),(1741533702087/50000000000000),(30987753923/100000000000000)⟩
theorem h29 : c29.Valid (fun x => f29 ((113/40)+(1/40)*x)) := h25.mul h0 (by decide +kernel)

def c31 : Certificate := ⟨(34074524829392341/100000000000000),(2110811272617223/100000000000000),(1400980933153/2500000000000),(103317177961/12500000000000),(1470688639/20000000000000)⟩
theorem h31 : c31.Valid (fun x => f31 ((113/40)+(1/40)*x)) := (SharedCertificates.h30 (113/40) (1/40)).mul h29 (by decide +kernel)

def c32 : Certificate := RationalModel.addExact c28 c31
theorem h32 : c32.Valid (fun x => f32 ((113/40)+(1/40)*x)) := h28.addExact h31

def c34 : Certificate := RationalModel.scale (2145) c7
theorem h34 : c34.Valid (fun x => f34 ((113/40)+(1/40)*x)) := h7.scale (2145)

def c36 : Certificate := RationalModel.scale (4418) c0
theorem h36 : c36.Valid (fun x => f36 ((113/40)+(1/40)*x)) := h0.scale (4418)

def c37 : Certificate := RationalModel.addExact c34 c36
theorem h37 : c37.Valid (fun x => f37 ((113/40)+(1/40)*x)) := h34.addExact h36

def c39 : Certificate := RationalModel.addExact c37 SharedCertificates.c38
theorem h39 : c39.Valid (fun x => f39 ((113/40)+(1/40)*x)) := h37.addExact (SharedCertificates.h38 (113/40) (1/40))

def c40 : Certificate := RationalModel.neg c39
theorem h40 : c40.Valid (fun x => f40 ((113/40)+(1/40)*x)) := h39.neg

def c42 : Certificate := RationalModel.addExact c0 SharedCertificates.c41
theorem h42 : c42.Valid (fun x => f42 ((113/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h41 (113/40) (1/40))

def c43 : Certificate := ⟨(23409/1600),(153/800),(1/1600),0,0⟩
theorem h43 : c43.Valid (fun x => f43 ((113/40)+(1/40)*x)) := h42.mul h42 (by decide +kernel)

def c45 : Certificate := RationalModel.scale (210) c43
theorem h45 : c45.Valid (fun x => f45 ((113/40)+(1/40)*x)) := h43.scale (210)

def c46 : Certificate := ⟨(6509502857/20000000000000),(-53182213/12500000000000),(4171153/100000000000000),(-727/2000000000000),(61/20000000000000)⟩
theorem h46 : c46.Valid (fun x => f46 ((113/40)+(1/40)*x)) := h45.inv (by decide +kernel)

def c47 : Certificate := ⟨(-207518333402571/20000000000000),(5356513961/5000000000000),(-4436873/625000000000),(4706449/100000000000000),(9667349/50000000000000)⟩
theorem h47 : c47.Valid (fun x => f47 ((113/40)+(1/40)*x)) := h40.mul h46 (by decide +kernel)

def c49 : Certificate := RationalModel.addExact c0 SharedCertificates.c48
theorem h49 : c49.Valid (fun x => f49 ((113/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h48 (113/40) (1/40))

def c52 : Certificate := ⟨(160833333333331/100000000000000),(833333333333/100000000000000),0,0,(3/50000000000000)⟩
theorem h52 : c52.Valid (fun x => f52 ((113/40)+(1/40)*x)) := h49.mul (SharedCertificates.h51 (113/40) (1/40)) (by decide +kernel)

def c54 : Certificate := RationalModel.addExact c52 SharedCertificates.c53
theorem h54 : c54.Valid (fun x => f54 ((113/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h53 (113/40) (1/40))

def c55 : Certificate := RationalModel.addExact c52 SharedCertificates.c50
theorem h55 : c55.Valid (fun x => f55 ((113/40)+(1/40)*x)) := h52.addExact (SharedCertificates.h50 (113/40) (1/40))

def c56 : Certificate := ⟨(21699819168173/100000000000000),(-306563901/781250000000),(17739683/25000000000000),(-32079/25000000000000),(47/20000000000000)⟩
theorem h56 : c56.Valid (fun x => f56 ((113/40)+(1/40)*x)) := h55.inv (by decide +kernel)

def c57 : Certificate := ⟨(1650090415913/12500000000000),(15696071731/10000000000000),(-283834933/100000000000000),(513263/100000000000000),(609/50000000000000)⟩
theorem h57 : c57.Valid (fun x => f57 ((113/40)+(1/40)*x)) := h54.mul h56 (by decide +kernel)

def c58 : Certificate := RationalModel.scale (2) c57
theorem h58 : c58.Valid (fun x => f58 ((113/40)+(1/40)*x)) := h57.scale (2)

def c60 : Certificate := RationalModel.scale (6) c57
theorem h60 : c60.Valid (fun x => f60 ((113/40)+(1/40)*x)) := h57.scale (6)

def c62 : Certificate := RationalModel.neg c60
theorem h62 : c62.Valid (fun x => f62 ((113/40)+(1/40)*x)) := h60.neg

def c63 : Certificate := RationalModel.addExact SharedCertificates.c61 c62
theorem h63 : c63.Valid (fun x => f63 ((113/40)+(1/40)*x)) := (SharedCertificates.h61 (113/40) (1/40)).addExact h62

def c64 : Certificate := ⟨(-97632836182049/50000000000000),(-611522360659/25000000000000),(117804329/4000000000000),(-2652623/100000000000000),(1341/4000000000000)⟩
theorem h64 : c64.Valid (fun x => f64 ((113/40)+(1/40)*x)) := h57.mul h63 (by decide +kernel)

def c65 : Certificate := RationalModel.addExact SharedCertificates.c61 c64
theorem h65 : c65.Valid (fun x => f65 ((113/40)+(1/40)*x)) := (SharedCertificates.h61 (113/40) (1/40)).addExact h64

def c66 : Certificate := ⟨(-210586607744241/100000000000000),(-706710485501/25000000000000),(215459461/20000000000000),(605489/20000000000000),(49041/100000000000000)⟩
theorem h66 : c66.Valid (fun x => f66 ((113/40)+(1/40)*x)) := h57.mul h65 (by decide +kernel)

def c68 : Certificate := RationalModel.addExact SharedCertificates.c67 c66
theorem h68 : c68.Valid (fun x => f68 ((113/40)+(1/40)*x)) := (SharedCertificates.h67 (113/40) (1/40)).addExact h66

def c69 : Certificate := ⟨(-951849588363953/100000000000000),(-11690952045439/100000000000000),(8085671657/50000000000000),(-2689513/10000000000000),(107231/100000000000000)⟩
theorem h69 : c69.Valid (fun x => f69 ((113/40)+(1/40)*x)) := h57.mul h68 (by decide +kernel)

def c70 : Certificate := RationalModel.addExact SharedCertificates.c67 c69
theorem h70 : c70.Valid (fun x => f70 ((113/40)+(1/40)*x)) := (SharedCertificates.h67 (113/40) (1/40)).addExact h69

def c71 : Certificate := ⟨(-131212707945411/12500000000000),(-2804914077431/20000000000000),(6354659049/100000000000000),(221897/1562500000000),(259603/100000000000000)⟩
theorem h71 : c71.Valid (fun x => f71 ((113/40)+(1/40)*x)) := h57.mul h70 (by decide +kernel)

def c73 : Certificate := RationalModel.addExact SharedCertificates.c72 c71
theorem h73 : c73.Valid (fun x => f73 ((113/40)+(1/40)*x)) := (SharedCertificates.h72 (113/40) (1/40)).addExact h71

def c74 : Certificate := ⟨(623753868498911/50000000000000),(6490955661077/50000000000000),(-5999681659/12500000000000),(100160521/100000000000000),(217693/100000000000000)⟩
theorem h74 : c74.Valid (fun x => f74 ((113/40)+(1/40)*x)) := h57.mul h73 (by decide +kernel)

def c75 : Certificate := RationalModel.addExact SharedCertificates.c72 c74
theorem h75 : c75.Valid (fun x => f75 ((113/40)+(1/40)*x)) := (SharedCertificates.h72 (113/40) (1/40)).addExact h74

def c76 : Certificate := ⟨(3101511988429427/100000000000000),(20152678606273/50000000000000),(-38606081187/100000000000000),(-15466729/20000000000000),(213173/20000000000000)⟩
theorem h76 : c76.Valid (fun x => f76 ((113/40)+(1/40)*x)) := h58.mul h75 (by decide +kernel)

def c77 : Certificate := RationalModel.neg c57
theorem h77 : c77.Valid (fun x => f77 ((113/40)+(1/40)*x)) := h57.neg

def c78 : Certificate := RationalModel.addExact SharedCertificates.c41 c77
theorem h78 : c78.Valid (fun x => f78 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h77

def c79 : Certificate := RationalModel.scale (105) c78
theorem h79 : c79.Valid (fun x => f79 ((113/40)+(1/40)*x)) := h78.scale (105)

def c80 : Certificate := RationalModel.addExact SharedCertificates.c41 c57
theorem h80 : c80.Valid (fun x => f80 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h57

def c81 : Certificate := ⟨(16018004702281/12500000000000),(355361334669/100000000000000),(-396239727/100000000000000),(33877/12500000000000),(5183/100000000000000)⟩
theorem h81 : c81.Valid (fun x => f81 ((113/40)+(1/40)*x)) := h80.mul h80 (by decide +kernel)

def c82 : Certificate := ⟨(2335790052788361/20000000000000),(1126810308031/10000000000000),(-56489304223/100000000000000),(126850953/100000000000000),(124017/12500000000000)⟩
theorem h82 : c82.Valid (fun x => f82 ((113/40)+(1/40)*x)) := h79.mul h81 (by decide +kernel)

def c83 : Certificate := ⟨(428120668981/50000000000000),(-826120109/100000000000000),(4938567/100000000000000),(-18061/100000000000000),(63/50000000000000)⟩
theorem h83 : c83.Valid (fun x => f83 ((113/40)+(1/40)*x)) := h82.inv (by decide +kernel)

def c84 : Certificate := ⟨(26556427746779/100000000000000),(319488915647/100000000000000),(-12759041/2500000000000),(135889/12500000000000),(1353/6250000000000)⟩
theorem h84 : c84.Valid (fun x => f84 ((113/40)+(1/40)*x)) := h76.mul h83 (by decide +kernel)

def c85 : Certificate := RationalModel.scale (3) c52
theorem h85 : c85.Valid (fun x => f85 ((113/40)+(1/40)*x)) := h52.scale (3)

def c86 : Certificate := RationalModel.addExact c85 SharedCertificates.c41
theorem h86 : c86.Valid (fun x => f86 ((113/40)+(1/40)*x)) := h85.addExact (SharedCertificates.h41 (113/40) (1/40))

def c87 : Certificate := ⟨(17167381974249/100000000000000),(-73679750963/100000000000000),(316222107/100000000000000),(-1357177/100000000000000),(1463/25000000000000)⟩
theorem h87 : c87.Valid (fun x => f87 ((113/40)+(1/40)*x)) := h86.inv (by decide +kernel)

def c88 : Certificate := ⟨(10443490701001/100000000000000),(98239667949/100000000000000),(-421629477/100000000000000),(56549/3125000000000),(7461/50000000000000)⟩
theorem h88 : c88.Valid (fun x => f88 ((113/40)+(1/40)*x)) := h54.mul h87 (by decide +kernel)

def c89 : Certificate := RationalModel.scale (2) c88
theorem h89 : c89.Valid (fun x => f89 ((113/40)+(1/40)*x)) := h88.scale (2)

def c90 : Certificate := RationalModel.scale (6) c88
theorem h90 : c90.Valid (fun x => f90 ((113/40)+(1/40)*x)) := h88.scale (6)

def c91 : Certificate := RationalModel.neg c90
theorem h91 : c91.Valid (fun x => f91 ((113/40)+(1/40)*x)) := h90.neg

def c92 : Certificate := RationalModel.addExact SharedCertificates.c61 c91
theorem h92 : c92.Valid (fun x => f92 ((113/40)+(1/40)*x)) := (SharedCertificates.h61 (113/40) (1/40)).addExact h91

def c93 : Certificate := ⟨(-4773526865479/3125000000000),(-149847115833/10000000000000),(5852144759/100000000000000),(-22631249/100000000000000),(129939/50000000000000)⟩
theorem h93 : c93.Valid (fun x => f93 ((113/40)+(1/40)*x)) := h88.mul h92 (by decide +kernel)

def c94 : Certificate := RationalModel.addExact SharedCertificates.c61 c93
theorem h94 : c94.Valid (fun x => f94 ((113/40)+(1/40)*x)) := (SharedCertificates.h61 (113/40) (1/40)).addExact h93

def c95 : Certificate := ⟨(-162161600511809/100000000000000),(-1681911949511/100000000000000),(355371179/6250000000000),(-2299311/12500000000000),(6671/2000000000000)⟩
theorem h95 : c95.Valid (fun x => f95 ((113/40)+(1/40)*x)) := h88.mul h94 (by decide +kernel)

def c96 : Certificate := RationalModel.addExact SharedCertificates.c67 c95
theorem h96 : c96.Valid (fun x => f96 ((113/40)+(1/40)*x)) := (SharedCertificates.h67 (113/40) (1/40)).addExact h95

def c97 : Certificate := ⟨(-186994920185029/25000000000000),(-180293352309/2500000000000),(728482257/2500000000000),(-14855991/12500000000000),(73551/6250000000000)⟩
theorem h97 : c97.Valid (fun x => f97 ((113/40)+(1/40)*x)) := h88.mul h96 (by decide +kernel)

def c98 : Certificate := RationalModel.addExact SharedCertificates.c67 c97
theorem h98 : c98.Valid (fun x => f98 ((113/40)+(1/40)*x)) := (SharedCertificates.h67 (113/40) (1/40)).addExact h97

def c99 : Certificate := ⟨(-809159537473541/100000000000000),(-32674790197/390625000000),(28626141651/100000000000000),(-18716739/20000000000000),(330489/20000000000000)⟩
theorem h99 : c99.Valid (fun x => f99 ((113/40)+(1/40)*x)) := h88.mul h98 (by decide +kernel)

def c100 : Certificate := RationalModel.addExact SharedCertificates.c72 c99
theorem h100 : c100.Valid (fun x => f100 ((113/40)+(1/40)*x)) := (SharedCertificates.h72 (113/40) (1/40)).addExact h99

def c101 : Certificate := ⟨(1012062022552793/100000000000000),(8646677990849/100000000000000),(-46087370499/100000000000000),(45795881/20000000000000),(1986439/100000000000000)⟩
theorem h101 : c101.Valid (fun x => f101 ((113/40)+(1/40)*x)) := h88.mul h100 (by decide +kernel)

def c102 : Certificate := RationalModel.addExact SharedCertificates.c72 c101
theorem h102 : c102.Valid (fun x => f102 ((113/40)+(1/40)*x)) := (SharedCertificates.h72 (113/40) (1/40)).addExact h101

def c103 : Certificate := ⟨(2404522253637537/100000000000000),(24424853033917/100000000000000),(-89713818807/100000000000000),(15049901/5000000000000),(5012159/100000000000000)⟩
theorem h103 : c103.Valid (fun x => f103 ((113/40)+(1/40)*x)) := h89.mul h102 (by decide +kernel)

def c104 : Certificate := RationalModel.neg c88
theorem h104 : c104.Valid (fun x => f104 ((113/40)+(1/40)*x)) := h88.neg

def c105 : Certificate := RationalModel.addExact SharedCertificates.c41 c104
theorem h105 : c105.Valid (fun x => f105 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h104

def c106 : Certificate := RationalModel.scale (105) c105
theorem h106 : c106.Valid (fun x => f106 ((113/40)+(1/40)*x)) := h105.scale (105)

def c107 : Certificate := RationalModel.addExact SharedCertificates.c41 c88
theorem h107 : c107.Valid (fun x => f107 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h88

def c108 : Certificate := ⟨(6098882319111/5000000000000),(216998637071/100000000000000),(-834814301/100000000000000),(633737/20000000000000),(38341/100000000000000)⟩
theorem h108 : c108.Valid (fun x => f108 ((113/40)+(1/40)*x)) := h107.mul h107 (by decide +kernel)

def c109 : Certificate := ⟨(5735043416812131/50000000000000),(312925073199/4000000000000),(-11721033847/25000000000000),(3880971/1562500000000),(1327131/20000000000000)⟩
theorem h109 : c109.Valid (fun x => f109 ((113/40)+(1/40)*x)) := h106.mul h108 (by decide +kernel)

def c110 : Certificate := ⟨(435916490653/50000000000000),(-594630197/100000000000000),(1984597/50000000000000),(-12009/50000000000000),(553/100000000000000)⟩
theorem h110 : c110.Valid (fun x => f110 ((113/40)+(1/40)*x)) := h109.inv (by decide +kernel)

def c111 : Certificate := ⟨(10481709025027/50000000000000),(198645908971/100000000000000),(-41597603/5000000000000),(3549617/100000000000000),(68413/100000000000000)⟩
theorem h111 : c111.Valid (fun x => f111 ((113/40)+(1/40)*x)) := h103.mul h110 (by decide +kernel)

def c112 : Certificate := RationalModel.addExact c84 c111
theorem h112 : c112.Valid (fun x => f112 ((113/40)+(1/40)*x)) := h84.addExact h111

def c113 : Certificate := ⟨(-246530980082649/50000000000000),(-5325215620641/100000000000000),(14145471147/100000000000000),(-50990079/100000000000000),(5130901/50000000000000)⟩
theorem h113 : c113.Valid (fun x => f113 ((113/40)+(1/40)*x)) := h47.mul h112 (by decide +kernel)

def c114 : Certificate := ⟨(7079646017699/20000000000000),(-6265173467/2000000000000),(2772200649/100000000000000),(-98131/400000000000),(43809/20000000000000)⟩
theorem h114 : c114.Valid (fun x => f114 ((113/40)+(1/40)*x)) := h0.inv (by decide +kernel)

def c115 : Certificate := ⟨(-43633801784539/25000000000000),(-21279545181/6250000000000),(802027937/10000000000000),(-17805101/20000000000000),(1654961/25000000000000)⟩
theorem h115 : c115.Valid (fun x => f115 ((113/40)+(1/40)*x)) := h113.mul h114 (by decide +kernel)

def c117 : Certificate := RationalModel.scale (10) c17
theorem h117 : c117.Valid (fun x => f117 ((113/40)+(1/40)*x)) := h17.scale (10)

def c119 : Certificate := RationalModel.scale (18) c12
theorem h119 : c119.Valid (fun x => f119 ((113/40)+(1/40)*x)) := h12.scale (18)

def c120 : Certificate := RationalModel.addExact c117 c119
theorem h120 : c120.Valid (fun x => f120 ((113/40)+(1/40)*x)) := h117.addExact h119

def c121 : Certificate := RationalModel.neg c7
theorem h121 : c121.Valid (fun x => f121 ((113/40)+(1/40)*x)) := h7.neg

def c122 : Certificate := RationalModel.addExact c120 c121
theorem h122 : c122.Valid (fun x => f122 ((113/40)+(1/40)*x)) := h120.addExact h121

def c123 : Certificate := RationalModel.scale (6) c0
theorem h123 : c123.Valid (fun x => f123 ((113/40)+(1/40)*x)) := h0.scale (6)

def c124 : Certificate := RationalModel.neg c123
theorem h124 : c124.Valid (fun x => f124 ((113/40)+(1/40)*x)) := h123.neg

def c125 : Certificate := RationalModel.addExact c122 c124
theorem h125 : c125.Valid (fun x => f125 ((113/40)+(1/40)*x)) := h122.addExact h124

def c126 : Certificate := RationalModel.addExact c125 SharedCertificates.c50
theorem h126 : c126.Valid (fun x => f126 ((113/40)+(1/40)*x)) := h125.addExact (SharedCertificates.h50 (113/40) (1/40))

def c128 : Certificate := RationalModel.scale (64) c126
theorem h128 : c128.Valid (fun x => f128 ((113/40)+(1/40)*x)) := h126.scale (64)

def c130 : Certificate := RationalModel.scale (945) c17
theorem h130 : c130.Valid (fun x => f130 ((113/40)+(1/40)*x)) := h17.scale (945)

def c131 : Certificate := ⟨(415369297/25000000000000),(-7351669/12500000000000),(65059/5000000000000),(-2303/10000000000000),(401/100000000000000)⟩
theorem h131 : c131.Valid (fun x => f131 ((113/40)+(1/40)*x)) := h130.inv (by decide +kernel)

def c132 : Certificate := ⟨(108545012896691/100000000000000),(-33029912047/10000000000000),(2582958431/100000000000000),(-19502119/100000000000000),(51474041/100000000000000)⟩
theorem h132 : c132.Valid (fun x => f132 ((113/40)+(1/40)*x)) := h128.mul h131 (by decide +kernel)

def c133 : Certificate := RationalModel.addExact c0 SharedCertificates.c50
theorem h133 : c133.Valid (fun x => f133 ((113/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h50 (113/40) (1/40))

def c134 : Certificate := ⟨(44969/1600),(213/800),(1/1600),0,0⟩
theorem h134 : c134.Valid (fun x => f134 ((113/40)+(1/40)*x)) := h133.mul h49 (by decide +kernel)

def c135 : Certificate := RationalModel.scale (6) c42
theorem h135 : c135.Valid (fun x => f135 ((113/40)+(1/40)*x)) := h42.scale (6)

def c136 : Certificate := ⟨(871459694989/20000000000000),(-1139163/4000000000),(37227549/20000000000000),(-1216587/100000000000000),(4003/50000000000000)⟩
theorem h136 : c136.Valid (fun x => f136 ((113/40)+(1/40)*x)) := h135.inv (by decide +kernel)

def c137 : Certificate := ⟨(30616149237469/25000000000000),(359708516657/100000000000000),(372275487/100000000000000),(-1216593/50000000000000),(435493/100000000000000)⟩
theorem h137 : c137.Valid (fun x => f137 ((113/40)+(1/40)*x)) := h134.mul h136 (by decide +kernel)

def c138 : Certificate := RationalModel.addExact c137 SharedCertificates.c53
theorem h138 : c138.Valid (fun x => f138 ((113/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h53 (113/40) (1/40))

def c139 : Certificate := RationalModel.addExact c137 SharedCertificates.c50
theorem h139 : c139.Valid (fun x => f139 ((113/40)+(1/40)*x)) := h137.addExact (SharedCertificates.h50 (113/40) (1/40))

def c140 : Certificate := ⟨(11835311257083/50000000000000),(-5038602391/25000000000000),(-1849007/50000000000000),(157239/100000000000000),(6173/25000000000000)⟩
theorem h140 : c140.Valid (fun x => f140 ((113/40)+(1/40)*x)) := h139.inv (by decide +kernel)

def c141 : Certificate := ⟨(5317509943333/100000000000000),(80617638253/100000000000000),(14792053/100000000000000),(-3931/625000000000),(109853/100000000000000)⟩
theorem h141 : c141.Valid (fun x => f141 ((113/40)+(1/40)*x)) := h138.mul h140 (by decide +kernel)

def c142 : Certificate := RationalModel.scale (2) c141
theorem h142 : c142.Valid (fun x => f142 ((113/40)+(1/40)*x)) := h141.scale (2)

def c143 : Certificate := ⟨(141379559987/50000000000000),(428685093/5000000000000),(66565173/100000000000000),(-43041/100000000000000),(103/800000000000)⟩
theorem h143 : c143.Valid (fun x => f143 ((113/40)+(1/40)*x)) := h141.mul h141 (by decide +kernel)

def c145 : Certificate := RationalModel.neg c142
theorem h145 : c145.Valid (fun x => f145 ((113/40)+(1/40)*x)) := h142.neg

def c146 : Certificate := RationalModel.addExact SharedCertificates.c144 c145
theorem h146 : c146.Valid (fun x => f146 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h145

def c147 : Certificate := ⟨(3363037951047/100000000000000),(101516699973/100000000000000),(194448843/25000000000000),(-618221/100000000000000),(153953/100000000000000)⟩
theorem h147 : c147.Valid (fun x => f147 ((113/40)+(1/40)*x)) := h143.mul h146 (by decide +kernel)

def c149 : Certificate := RationalModel.addExact SharedCertificates.c148 c147
theorem h149 : c149.Valid (fun x => f149 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h147

def c150 : Certificate := ⟨(-93034070273647/12500000000000),(-2819589998259/25000000000000),(-973595123/50000000000000),(8864243/10000000000000),(15385179/100000000000000)⟩
theorem h150 : c150.Valid (fun x => f150 ((113/40)+(1/40)*x)) := h141.mul h149 (by decide +kernel)

def c152 : Certificate := RationalModel.addExact SharedCertificates.c151 c150
theorem h152 : c152.Valid (fun x => f152 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h150

def c153 : Certificate := ⟨(-1528479551633149/100000000000000),(-23772681586717/100000000000000),(-13447757527/100000000000000),(91132733/50000000000000),(3256149/10000000000000)⟩
theorem h153 : c153.Valid (fun x => f153 ((113/40)+(1/40)*x)) := h141.mul h152 (by decide +kernel)

def c155 : Certificate := RationalModel.addExact SharedCertificates.c154 c153
theorem h155 : c155.Valid (fun x => f155 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h153

def c156 : Certificate := ⟨(19659642760433/1000000000000),(28541451904527/100000000000000),(-14411213389/100000000000000),(-237201823/100000000000000),(8538551/20000000000000)⟩
theorem h156 : c156.Valid (fun x => f156 ((113/40)+(1/40)*x)) := h141.mul h155 (by decide +kernel)

def c158 : Certificate := RationalModel.addExact SharedCertificates.c157 c156
theorem h158 : c158.Valid (fun x => f158 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h156

def c159 : Certificate := ⟨(5687925786360627/100000000000000),(10968891084611/12500000000000),(38065588871/100000000000000),(-692782473/100000000000000),(60107119/50000000000000)⟩
theorem h159 : c159.Valid (fun x => f159 ((113/40)+(1/40)*x)) := h141.mul h158 (by decide +kernel)

def c161 : Certificate := RationalModel.addExact SharedCertificates.c160 c159
theorem h161 : c161.Valid (fun x => f161 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h159

def c162 : Certificate := ⟨(3094148739508953/50000000000000),(20630362604061/20000000000000),(162748435549/100000000000000),(-359149783/50000000000000),(143224199/100000000000000)⟩
theorem h162 : c162.Valid (fun x => f162 ((113/40)+(1/40)*x)) := h142.mul h161 (by decide +kernel)

def c163 : Certificate := RationalModel.addExact SharedCertificates.c41 c141
theorem h163 : c163.Valid (fun x => f163 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h141

def c164 : Certificate := ⟨(1386472237583/1250000000000),(84904489183/50000000000000),(96149279/100000000000000),(-1300961/100000000000000),(232581/100000000000000)⟩
theorem h164 : c164.Valid (fun x => f164 ((113/40)+(1/40)*x)) := h163.mul h163 (by decide +kernel)

def c165 : Certificate := RationalModel.scale (105) c164
theorem h165 : c165.Valid (fun x => f165 ((113/40)+(1/40)*x)) := h164.scale (105)

def c166 : Certificate := RationalModel.scale (3) c143
theorem h166 : c166.Valid (fun x => f166 ((113/40)+(1/40)*x)) := h143.scale (3)

def c168 : Certificate := RationalModel.neg c166
theorem h168 : c168.Valid (fun x => f168 ((113/40)+(1/40)*x)) := h166.neg

def c169 : Certificate := RationalModel.addExact SharedCertificates.c167 c168
theorem h169 : c169.Valid (fun x => f169 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h168

def c170 : Certificate := ⟨(58133040485704627/100000000000000),(43001445987471/50000000000000),(2818675143/12500000000000),(-176252487/25000000000000),(63223891/50000000000000)⟩
theorem h170 : c170.Valid (fun x => f170 ((113/40)+(1/40)*x)) := h165.mul h169 (by decide +kernel)

def c171 : Certificate := ⟨(172019215173/100000000000000),(-254487807/100000000000000),(38721/12500000000000),(863/50000000000000),(383/100000000000000)⟩
theorem h171 : c171.Valid (fun x => f171 ((113/40)+(1/40)*x)) := h170.inv (by decide +kernel)

def c172 : Certificate := ⟨(10645060755977/100000000000000),(161692476649/100000000000000),(915479/2500000000000),(-1223447/100000000000000),(274949/100000000000000)⟩
theorem h172 : c172.Valid (fun x => f172 ((113/40)+(1/40)*x)) := h162.mul h171 (by decide +kernel)

def c173 : Certificate := RationalModel.scale (3) c137
theorem h173 : c173.Valid (fun x => f173 ((113/40)+(1/40)*x)) := h137.scale (3)

def c174 : Certificate := RationalModel.addExact c173 SharedCertificates.c41
theorem h174 : c174.Valid (fun x => f174 ((113/40)+(1/40)*x)) := h173.addExact (SharedCertificates.h41 (113/40) (1/40))

def c175 : Certificate := ⟨(21395235015471/100000000000000),(-24698814153/50000000000000),(15731637/25000000000000),(30689/10000000000000),(61719/100000000000000)⟩
theorem h175 : c175.Valid (fun x => f175 ((113/40)+(1/40)*x)) := h174.inv (by decide +kernel)

def c176 : Certificate := ⟨(75099270511/1562500000000),(65863504407/100000000000000),(-41951033/50000000000000),(-102297/25000000000000),(110021/100000000000000)⟩
theorem h176 : c176.Valid (fun x => f176 ((113/40)+(1/40)*x)) := h138.mul h175 (by decide +kernel)

def c177 : Certificate := RationalModel.scale (2) c176
theorem h177 : c177.Valid (fun x => f177 ((113/40)+(1/40)*x)) := h176.scale (2)

def c178 : Certificate := ⟨(46202064333/20000000000000),(6331265451/100000000000000),(551793/1562500000000),(-4683/3125000000000),(11193/100000000000000)⟩
theorem h178 : c178.Valid (fun x => f178 ((113/40)+(1/40)*x)) := h176.mul h176 (by decide +kernel)

def c179 : Certificate := RationalModel.neg c177
theorem h179 : c179.Valid (fun x => f179 ((113/40)+(1/40)*x)) := h177.neg

def c180 : Certificate := RationalModel.addExact SharedCertificates.c144 c179
theorem h180 : c180.Valid (fun x => f180 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h179

def c181 : Certificate := ⟨(2749917515483/100000000000000),(75062276451/100000000000000),(206214989/50000000000000),(-113617/6250000000000),(134089/100000000000000)⟩
theorem h181 : c181.Valid (fun x => f181 ((113/40)+(1/40)*x)) := h178.mul h180 (by decide +kernel)

def c182 : Certificate := RationalModel.addExact SharedCertificates.c148 c181
theorem h182 : c182.Valid (fun x => f182 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h181

def c183 : Certificate := ⟨(-336378646513479/50000000000000),(-4607735833363/50000000000000),(1181324349/10000000000000),(14349089/25000000000000),(15408383/100000000000000)⟩
theorem h183 : c183.Valid (fun x => f183 ((113/40)+(1/40)*x)) := h176.mul h182 (by decide +kernel)

def c184 : Certificate := RationalModel.addExact SharedCertificates.c151 c183
theorem h184 : c184.Valid (fun x => f184 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h183

def c185 : Certificate := ⟨(-1378114019996979/100000000000000),(-19327810891037/100000000000000),(927759469/5000000000000),(135596741/100000000000000),(4046581/12500000000000)⟩
theorem h185 : c185.Valid (fun x => f185 ((113/40)+(1/40)*x)) := h176.mul h184 (by decide +kernel)

def c186 : Certificate := RationalModel.addExact SharedCertificates.c154 c185
theorem h186 : c186.Valid (fun x => f186 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h185

def c187 : Certificate := ⟨(446052249134519/25000000000000),(11760406064683/50000000000000),(-21492087447/50000000000000),(-58471757/50000000000000),(10648367/25000000000000)⟩
theorem h187 : c187.Valid (fun x => f187 ((113/40)+(1/40)*x)) := h176.mul h186 (by decide +kernel)

def c188 : Certificate := RationalModel.addExact SharedCertificates.c157 c187
theorem h188 : c188.Valid (fun x => f188 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h187

def c189 : Certificate := ⟨(513242636654987/10000000000000),(71462315531369/100000000000000),(-76168497691/100000000000000),(-490614219/100000000000000),(59861871/50000000000000)⟩
theorem h189 : c189.Valid (fun x => f189 ((113/40)+(1/40)*x)) := h176.mul h188 (by decide +kernel)

def c190 : Certificate := RationalModel.addExact SharedCertificates.c160 c189
theorem h190 : c190.Valid (fun x => f190 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h189

def c191 : Certificate := ⟨(2770018033860363/50000000000000),(82786934099341/100000000000000),(-9896276361/100000000000000),(-369531227/50000000000000),(139744303/100000000000000)⟩
theorem h191 : c191.Valid (fun x => f191 ((113/40)+(1/40)*x)) := h177.mul h190 (by decide +kernel)

def c192 : Certificate := RationalModel.addExact SharedCertificates.c41 c176
theorem h192 : c192.Valid (fun x => f192 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h176

def c193 : Certificate := ⟨(109843716947073/100000000000000),(27611654853/20000000000000),(-6624469/5000000000000),(-121029/12500000000000),(46247/20000000000000)⟩
theorem h193 : c193.Valid (fun x => f193 ((113/40)+(1/40)*x)) := h192.mul h192 (by decide +kernel)

def c194 : Certificate := RationalModel.scale (105) c193
theorem h194 : c194.Valid (fun x => f194 ((113/40)+(1/40)*x)) := h193.scale (105)

def c195 : Certificate := RationalModel.scale (3) c178
theorem h195 : c195.Valid (fun x => f195 ((113/40)+(1/40)*x)) := h178.scale (3)

def c196 : Certificate := RationalModel.neg c195
theorem h196 : c196.Valid (fun x => f196 ((113/40)+(1/40)*x)) := h195.neg

def c197 : Certificate := RationalModel.addExact SharedCertificates.c167 c196
theorem h197 : c197.Valid (fun x => f197 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h196

def c198 : Certificate := ⟨(57588020045201133/100000000000000),(35094732373633/50000000000000),(-84433053991/100000000000000),(-468481409/100000000000000),(125211751/100000000000000)⟩
theorem h198 : c198.Valid (fun x => f198 ((113/40)+(1/40)*x)) := h194.mul h197 (by decide +kernel)

def c199 : Certificate := ⟨(86823613593/50000000000000),(-211644817/100000000000000),(512551/100000000000000),(477/100000000000000),(191/50000000000000)⟩
theorem h199 : c199.Valid (fun x => f199 ((113/40)+(1/40)*x)) := h198.inv (by decide +kernel)

def c200 : Certificate := ⟨(9620119016701/100000000000000),(66016008169/50000000000000),(-32800671/20000000000000),(-405833/50000000000000),(266353/100000000000000)⟩
theorem h200 : c200.Valid (fun x => f200 ((113/40)+(1/40)*x)) := h191.mul h199 (by decide +kernel)

def c201 : Certificate := RationalModel.addExact c172 c200
theorem h201 : c201.Valid (fun x => f201 ((113/40)+(1/40)*x)) := h172.addExact h200

def c202 : Certificate := ⟨(2199684199779/10000000000000),(125943789121/50000000000000),(-584997439/100000000000000),(1846377/100000000000000),(5612903/50000000000000)⟩
theorem h202 : c202.Valid (fun x => f202 ((113/40)+(1/40)*x)) := h132.mul h201 (by decide +kernel)

def c203 : Certificate := ⟨(389324637129/5000000000000),(20256729089/100000000000000),(-386341829/100000000000000),(2036269/50000000000000),(2070973/50000000000000)⟩
theorem h203 : c203.Valid (fun x => f203 ((113/40)+(1/40)*x)) := h202.mul h114 (by decide +kernel)

def c204 : Certificate := RationalModel.addExact c115 c203
theorem h204 : c204.Valid (fun x => f204 ((113/40)+(1/40)*x)) := h115.addExact h203

def c206 : Certificate := RationalModel.scale (-5) c7
theorem h206 : c206.Valid (fun x => f206 ((113/40)+(1/40)*x)) := by simpa only [c206,f206,f205,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-5)

def c208 : Certificate := RationalModel.scale (21) c0
theorem h208 : c208.Valid (fun x => f208 ((113/40)+(1/40)*x)) := h0.scale (21)

def c209 : Certificate := RationalModel.addExact c206 c208
theorem h209 : c209.Valid (fun x => f209 ((113/40)+(1/40)*x)) := h206.addExact h208

def c211 : Certificate := RationalModel.addExact c209 SharedCertificates.c210
theorem h211 : c211.Valid (fun x => f211 ((113/40)+(1/40)*x)) := h209.addExact (SharedCertificates.h210 (113/40) (1/40))

def c213 : Certificate := RationalModel.scale (250) c211
theorem h213 : c213.Valid (fun x => f213 ((113/40)+(1/40)*x)) := h211.scale (250)

def c214 : Certificate := RationalModel.addExact c121 c123
theorem h214 : c214.Valid (fun x => f214 ((113/40)+(1/40)*x)) := h121.addExact h123

def c215 : Certificate := RationalModel.addExact c214 SharedCertificates.c59
theorem h215 : c215.Valid (fun x => f215 ((113/40)+(1/40)*x)) := h214.addExact (SharedCertificates.h59 (113/40) (1/40))

def c217 : Certificate := RationalModel.scale (189) c215
theorem h217 : c217.Valid (fun x => f217 ((113/40)+(1/40)*x)) := h215.scale (189)

def c218 : Certificate := ⟨(17672766201/50000000000000),(-20660409/100000000000000),(74391/5000000000000),(-1733/100000000000000),(13/20000000000000)⟩
theorem h218 : c218.Valid (fun x => f218 ((113/40)+(1/40)*x)) := h217.inv (by decide +kernel)

def c219 : Certificate := ⟨(401365088643023/100000000000000),(-14345336451/781250000000),(-9782628891/100000000000000),(-70954927/100000000000000),(1826291/100000000000000)⟩
theorem h219 : c219.Valid (fun x => f219 ((113/40)+(1/40)*x)) := h213.mul h218 (by decide +kernel)

def c220 : Certificate := RationalModel.scale (18) c0
theorem h220 : c220.Valid (fun x => f220 ((113/40)+(1/40)*x)) := h0.scale (18)

def c221 : Certificate := RationalModel.addExact c7 c220
theorem h221 : c221.Valid (fun x => f221 ((113/40)+(1/40)*x)) := h7.addExact h220

def c222 : Certificate := RationalModel.addExact c221 SharedCertificates.c207
theorem h222 : c222.Valid (fun x => f222 ((113/40)+(1/40)*x)) := h221.addExact (SharedCertificates.h207 (113/40) (1/40))

def c223 : Certificate := ⟨(37249/1600),(193/800),(1/1600),0,0⟩
theorem h223 : c223.Valid (fun x => f223 ((113/40)+(1/40)*x)) := h49.mul h49 (by decide +kernel)

def c224 : Certificate := ⟨(4757777521/2560000),(21135237/640000),(265067/1280000),(333/640000),(1/2560000)⟩
theorem h224 : c224.Valid (fun x => f224 ((113/40)+(1/40)*x)) := h222.mul h223 (by decide +kernel)

def c226 : Certificate := RationalModel.scale (90) c43
theorem h226 : c226.Valid (fun x => f226 ((113/40)+(1/40)*x)) := h43.scale (90)

def c227 : Certificate := ⟨(75944199999/100000000000000),(-992734641/100000000000000),(2433173/25000000000000),(-84817/100000000000000),(177/25000000000000)⟩
theorem h227 : c227.Valid (fun x => f227 ((113/40)+(1/40)*x)) := h226.inv (by decide +kernel)

def c228 : Certificate := ⟨(5645712618837/4000000000000),(662962540527/100000000000000),(3222483/312500000000),(-1143383/50000000000000),(2683987/100000000000000)⟩
theorem h228 : c228.Valid (fun x => f228 ((113/40)+(1/40)*x)) := h224.mul h227 (by decide +kernel)

def c229 : Certificate := RationalModel.addExact c228 SharedCertificates.c53
theorem h229 : c229.Valid (fun x => f229 ((113/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h53 (113/40) (1/40))

def c230 : Certificate := RationalModel.addExact c228 SharedCertificates.c50
theorem h230 : c230.Valid (fun x => f230 ((113/40)+(1/40)*x)) := h228.addExact (SharedCertificates.h50 (113/40) (1/40))

def c231 : Certificate := ⟨(22668395923721/100000000000000),(-17033369721/50000000000000),(-1792061/100000000000000),(24979/12500000000000),(13881/10000000000000)⟩
theorem h231 : c231.Valid (fun x => f231 ((113/40)+(1/40)*x)) := h230.inv (by decide +kernel)

def c232 : Certificate := ⟨(1865283261023/20000000000000),(136266957767/100000000000000),(7168239/100000000000000),(-199833/25000000000000),(669453/100000000000000)⟩
theorem h232 : c232.Valid (fun x => f232 ((113/40)+(1/40)*x)) := h229.mul h231 (by decide +kernel)

def c233 : Certificate := RationalModel.scale (2) c232
theorem h233 : c233.Valid (fun x => f233 ((113/40)+(1/40)*x)) := h232.scale (2)

def c234 : Certificate := ⟨(869820410963/100000000000000),(5083529507/20000000000000),(187023917/100000000000000),(-129563/100000000000000),(128877/100000000000000)⟩
theorem h234 : c234.Valid (fun x => f234 ((113/40)+(1/40)*x)) := h232.mul h232 (by decide +kernel)

def c235 : Certificate := RationalModel.neg c233
theorem h235 : c235.Valid (fun x => f235 ((113/40)+(1/40)*x)) := h233.neg

def c236 : Certificate := RationalModel.addExact SharedCertificates.c144 c235
theorem h236 : c236.Valid (fun x => f236 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h235

def c237 : Certificate := ⟨(10275598786289/100000000000000),(297900103547/100000000000000),(1070002667/50000000000000),(-2030031/100000000000000),(767781/50000000000000)⟩
theorem h237 : c237.Valid (fun x => f237 ((113/40)+(1/40)*x)) := h234.mul h236 (by decide +kernel)

def c238 : Certificate := RationalModel.addExact SharedCertificates.c148 c237
theorem h238 : c238.Valid (fun x => f238 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h237

def c239 : Certificate := ⟨(-163092492199431/12500000000000),(-4758897109423/25000000000000),(-198645833/50000000000000),(114572489/100000000000000),(93806957/100000000000000)⟩
theorem h239 : c239.Valid (fun x => f239 ((113/40)+(1/40)*x)) := h232.mul h238 (by decide +kernel)

def c240 : Certificate := RationalModel.addExact SharedCertificates.c151 c239
theorem h240 : c240.Valid (fun x => f240 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h239

def c241 : Certificate := ⟨(-54661640874229/2000000000000),(-521350197729/1250000000000),(-28076904129/100000000000000),(243021777/100000000000000),(20549383/10000000000000)⟩
theorem h241 : c241.Valid (fun x => f241 ((113/40)+(1/40)*x)) := h232.mul h240 (by decide +kernel)

def c242 : Certificate := RationalModel.addExact SharedCertificates.c154 c241
theorem h242 : c242.Valid (fun x => f242 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h241

def c243 : Certificate := ⟨(8339429170281/250000000000),(44848627798233/100000000000000),(-1777779847/3125000000000),(-38060059/12500000000000),(32478767/12500000000000)⟩
theorem h243 : c243.Valid (fun x => f243 ((113/40)+(1/40)*x)) := h232.mul h242 (by decide +kernel)

def c244 : Certificate := RationalModel.addExact SharedCertificates.c157 c243
theorem h244 : c244.Valid (fun x => f244 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h243

def c245 : Certificate := ⟨(10103845073126991/100000000000000),(30361725992227/20000000000000),(63573926951/100000000000000),(-968665599/100000000000000),(375461267/50000000000000)⟩
theorem h245 : c245.Valid (fun x => f245 ((113/40)+(1/40)*x)) := h232.mul h244 (by decide +kernel)

def c246 : Certificate := RationalModel.addExact SharedCertificates.c160 c245
theorem h246 : c246.Valid (fun x => f246 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h245

def c247 : Certificate := ⟨(5838695214529049/50000000000000),(99466659943583/50000000000000),(86912705601/20000000000000),(-123310523/12500000000000),(24685349/2500000000000)⟩
theorem h247 : c247.Valid (fun x => f247 ((113/40)+(1/40)*x)) := h233.mul h246 (by decide +kernel)

def c248 : Certificate := RationalModel.addExact SharedCertificates.c41 c232
theorem h248 : c248.Valid (fun x => f248 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h232

def c249 : Certificate := ⟨(119522653021193/100000000000000),(297951563069/100000000000000),(40272079/20000000000000),(-1728227/100000000000000),(1467783/100000000000000)⟩
theorem h249 : c249.Valid (fun x => f249 ((113/40)+(1/40)*x)) := h248.mul h248 (by decide +kernel)

def c250 : Certificate := RationalModel.scale (105) c249
theorem h250 : c250.Valid (fun x => f250 ((113/40)+(1/40)*x)) := h249.scale (105)

def c251 : Certificate := RationalModel.scale (3) c234
theorem h251 : c251.Valid (fun x => f251 ((113/40)+(1/40)*x)) := h234.scale (3)

def c252 : Certificate := RationalModel.neg c251
theorem h252 : c252.Valid (fun x => f252 ((113/40)+(1/40)*x)) := h251.neg

def c253 : Certificate := RationalModel.addExact SharedCertificates.c167 c252
theorem h253 : c253.Valid (fun x => f253 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h252

def c254 : Certificate := ⟨(1950684644379373/3125000000000),(73019275602299/50000000000000),(1361625261/12500000000000),(-261364201/25000000000000),(815468041/100000000000000)⟩
theorem h254 : c254.Valid (fun x => f254 ((113/40)+(1/40)*x)) := h250.mul h253 (by decide +kernel)

def c255 : Certificate := ⟨(160200164029/100000000000000),(-37479469/10000000000000),(848891/100000000000000),(381/50000000000000),(2113/100000000000000)⟩
theorem h255 : c255.Valid (fun x => f255 ((113/40)+(1/40)*x)) := h254.inv (by decide +kernel)

def c256 : Certificate := ⟨(18707198621657/100000000000000),(68731316377/25000000000000),(49708281/100000000000000),(-715681/50000000000000),(922707/50000000000000)⟩
theorem h256 : c256.Valid (fun x => f256 ((113/40)+(1/40)*x)) := h247.mul h255 (by decide +kernel)

def c257 : Certificate := RationalModel.scale (3) c228
theorem h257 : c257.Valid (fun x => f257 ((113/40)+(1/40)*x)) := h228.scale (3)

def c258 : Certificate := RationalModel.addExact c257 SharedCertificates.c41
theorem h258 : c258.Valid (fun x => f258 ((113/40)+(1/40)*x)) := h257.addExact (SharedCertificates.h41 (113/40) (1/40))

def c259 : Certificate := ⟨(9552404028223/50000000000000),(-36296571687/50000000000000),(16292061/10000000000000),(1887/3125000000000),(298293/100000000000000)⟩
theorem h259 : c259.Valid (fun x => f259 ((113/40)+(1/40)*x)) := h258.inv (by decide +kernel)

def c260 : Certificate := ⟨(7860255924737/100000000000000),(9679085783/10000000000000),(-217227481/100000000000000),(-80513/100000000000000),(643177/100000000000000)⟩
theorem h260 : c260.Valid (fun x => f260 ((113/40)+(1/40)*x)) := h229.mul h259 (by decide +kernel)

def c261 : Certificate := RationalModel.scale (2) c260
theorem h261 : c261.Valid (fun x => f261 ((113/40)+(1/40)*x)) := h260.scale (2)

def c262 : Certificate := ⟨(617836232023/100000000000000),(7608009137/50000000000000),(59535429/100000000000000),(-43317/10000000000000),(102677/100000000000000)⟩
theorem h262 : c262.Valid (fun x => f262 ((113/40)+(1/40)*x)) := h260.mul h260 (by decide +kernel)

def c263 : Certificate := RationalModel.neg c261
theorem h263 : c263.Valid (fun x => f263 ((113/40)+(1/40)*x)) := h261.neg

def c264 : Certificate := RationalModel.addExact SharedCertificates.c144 c263
theorem h264 : c264.Valid (fun x => f264 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h263

def c265 : Certificate := ⟨(731690776621/10000000000000),(89502082677/50000000000000),(84786833/12500000000000),(-1294523/25000000000000),(306363/25000000000000)⟩
theorem h265 : c265.Valid (fun x => f265 ((113/40)+(1/40)*x)) := h262.mul h264 (by decide +kernel)

def c266 : Certificate := RationalModel.addExact SharedCertificates.c148 c265
theorem h266 : c266.Valid (fun x => f266 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h265

def c267 : Certificate := ⟨(-1099860701786979/100000000000000),(-6764783906447/50000000000000),(30622528369/100000000000000),(5563299/50000000000000),(90103029/100000000000000)⟩
theorem h267 : c267.Valid (fun x => f267 ((113/40)+(1/40)*x)) := h260.mul h266 (by decide +kernel)

def c268 : Certificate := RationalModel.addExact SharedCertificates.c151 c267
theorem h268 : c268.Valid (fun x => f268 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h267

def c269 : Certificate := ⟨(-91492940996097/4000000000000),(-29229463456199/100000000000000),(5252451873/10000000000000),(83333497/100000000000000),(3038523/1562500000000)⟩
theorem h269 : c269.Valid (fun x => f269 ((113/40)+(1/40)*x)) := h260.mul h268 (by decide +kernel)

def c270 : Certificate := RationalModel.addExact SharedCertificates.c154 c269
theorem h270 : c270.Valid (fun x => f270 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h269

def c271 : Certificate := ⟨(1423204524069849/50000000000000),(8188262392591/25000000000000),(-102826771733/100000000000000),(91727673/100000000000000),(124292103/50000000000000)⟩
theorem h271 : c271.Valid (fun x => f271 ((113/40)+(1/40)*x)) := h260.mul h270 (by decide +kernel)

def c272 : Certificate := RationalModel.addExact SharedCertificates.c157 c271
theorem h272 : c272.Valid (fun x => f272 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h271

def c273 : Certificate := ⟨(3390801502729/40000000000),(106959937975931/100000000000000),(-210652527497/100000000000000),(-250295889/100000000000000),(1394377/195312500000)⟩
theorem h273 : c273.Valid (fun x => f273 ((113/40)+(1/40)*x)) := h260.mul h272 (by decide +kernel)

def c274 : Certificate := RationalModel.addExact SharedCertificates.c160 c273
theorem h274 : c274.Valid (fun x => f274 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h273

def c275 : Certificate := ⟨(9585897101045487/100000000000000),(26970995950843/20000000000000),(-18195678209/20000000000000),(-12625177/1250000000000),(179927151/20000000000000)⟩
theorem h275 : c275.Valid (fun x => f275 ((113/40)+(1/40)*x)) := h261.mul h274 (by decide +kernel)

def c276 : Certificate := RationalModel.addExact SharedCertificates.c41 c260
theorem h276 : c276.Valid (fun x => f276 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h260

def c277 : Certificate := ⟨(116338348081497/100000000000000),(104398866967/50000000000000),(-374919533/100000000000000),(-148549/25000000000000),(1389031/100000000000000)⟩
theorem h277 : c277.Valid (fun x => f277 ((113/40)+(1/40)*x)) := h276.mul h276 (by decide +kernel)

def c278 : Certificate := RationalModel.scale (105) c277
theorem h278 : c278.Valid (fun x => f278 ((113/40)+(1/40)*x)) := h277.scale (105)

def c279 : Certificate := RationalModel.scale (3) c262
theorem h279 : c279.Valid (fun x => f279 ((113/40)+(1/40)*x)) := h262.scale (3)

def c280 : Certificate := RationalModel.neg c279
theorem h280 : c280.Valid (fun x => f280 ((113/40)+(1/40)*x)) := h279.neg

def c281 : Certificate := RationalModel.addExact SharedCertificates.c167 c280
theorem h281 : c281.Valid (fun x => f281 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h280

def c282 : Certificate := ⟨(304256084479689/500000000000),(25909075305831/25000000000000),(-227928561711/100000000000000),(-173241649/100000000000000),(764684161/100000000000000)⟩
theorem h282 : c282.Valid (fun x => f282 ((113/40)+(1/40)*x)) := h278.mul h281 (by decide +kernel)

def c283 : Certificate := ⟨(164335250963/100000000000000),(-27988097/10000000000000),(1092213/100000000000000),(-2441/100000000000000),(1041/50000000000000)⟩
theorem h283 : c283.Valid (fun x => f283 ((113/40)+(1/40)*x)) := h282.inv (by decide +kernel)

def c284 : Certificate := ⟨(7876504029029/50000000000000),(1558281341/800000000000),(-422244579/100000000000000),(-166267/100000000000000),(421201/25000000000000)⟩
theorem h284 : c284.Valid (fun x => f284 ((113/40)+(1/40)*x)) := h275.mul h283 (by decide +kernel)

def c285 : Certificate := RationalModel.addExact c256 c284
theorem h285 : c285.Valid (fun x => f285 ((113/40)+(1/40)*x)) := h256.addExact h284

def c286 : Certificate := ⟨(138311239086607/100000000000000),(782808953/62500000000),(-13491182151/100000000000000),(-34986523/50000000000000),(15140089/100000000000000)⟩
theorem h286 : c286.Valid (fun x => f286 ((113/40)+(1/40)*x)) := h219.mul h285 (by decide +kernel)

def c287 : Certificate := ⟨(391677845201/800000000000),(10088870281/100000000000000),(-2432460869/50000000000000),(18283183/100000000000000),(6176379/100000000000000)⟩
theorem h287 : c287.Valid (fun x => f287 ((113/40)+(1/40)*x)) := h286.mul h114 (by decide +kernel)

def c288 : Certificate := RationalModel.addExact c204 c287
theorem h288 : c288.Valid (fun x => f288 ((113/40)+(1/40)*x)) := h204.addExact h287

def c290 : Certificate := RationalModel.scale (-11) c7
theorem h290 : c290.Valid (fun x => f290 ((113/40)+(1/40)*x)) := by simpa only [c290,f290,f289,Rat.cast_neg,Rat.cast_ofNat] using h7.scale (-11)

def c292 : Certificate := RationalModel.scale (97) c0
theorem h292 : c292.Valid (fun x => f292 ((113/40)+(1/40)*x)) := h0.scale (97)

def c293 : Certificate := RationalModel.addExact c290 c292
theorem h293 : c293.Valid (fun x => f293 ((113/40)+(1/40)*x)) := h290.addExact h292

def c295 : Certificate := RationalModel.addExact c293 SharedCertificates.c294
theorem h295 : c295.Valid (fun x => f295 ((113/40)+(1/40)*x)) := h293.addExact (SharedCertificates.h294 (113/40) (1/40))

def c296 : Certificate := RationalModel.scale (250) c295
theorem h296 : c296.Valid (fun x => f296 ((113/40)+(1/40)*x)) := h295.scale (250)

def c298 : Certificate := ⟨(1095749047476749521/100000000000000),(128098924175813/20000000000000),(-45749615777077/100000000000000),0,(141551/100000000000000)⟩
theorem h298 : c298.Valid (fun x => f298 ((113/40)+(1/40)*x)) := (SharedCertificates.h297 (113/40) (1/40)).mul h215 (by decide +kernel)

def c299 : Certificate := ⟨(9126177223/100000000000000),(-1066899/20000000000000),(384153/100000000000000),(-7/1562500000000),(19/100000000000000)⟩
theorem h299 : c299.Valid (fun x => f299 ((113/40)+(1/40)*x)) := h298.inv (by decide +kernel)

def c300 : Certificate := ⟨(335658659314153/50000000000000),(1595392524729/100000000000000),(5705288907/50000000000000),(29943659/50000000000000),(2160417/100000000000000)⟩
theorem h300 : c300.Valid (fun x => f300 ((113/40)+(1/40)*x)) := h296.mul h299 (by decide +kernel)

def c302 : Certificate := RationalModel.addExact c0 SharedCertificates.c301
theorem h302 : c302.Valid (fun x => f302 ((113/40)+(1/40)*x)) := h0.addExact (SharedCertificates.h301 (113/40) (1/40))

def c305 : Certificate := RationalModel.addExact c302 SharedCertificates.c304
theorem h305 : c305.Valid (fun x => f305 ((113/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h304 (113/40) (1/40))

def c307 : Certificate := ⟨(3619319460682739/100000000000000),(11091229182759/50000000000000),0,0,(219/20000000000000)⟩
theorem h307 : c307.Valid (fun x => f307 ((113/40)+(1/40)*x)) := h305.mul (SharedCertificates.h306 (113/40) (1/40)) (by decide +kernel)

def c308 : Certificate := RationalModel.addExact c302 SharedCertificates.c303
theorem h308 : c308.Valid (fun x => f308 ((113/40)+(1/40)*x)) := h302.addExact (SharedCertificates.h303 (113/40) (1/40))

def c311 : Certificate := ⟨(1102840269658501/50000000000000),(2817541634481/100000000000000),0,0,(547/50000000000000)⟩
theorem h311 : c311.Valid (fun x => f311 ((113/40)+(1/40)*x)) := h308.mul (SharedCertificates.h310 (113/40) (1/40)) (by decide +kernel)

def c312 : Certificate := ⟨(4533748120703/100000000000000),(-1447855193/25000000000000),(3698987/50000000000000),(-9451/100000000000000),(17/100000000000000)⟩
theorem h312 : c312.Valid (fun x => f312 ((113/40)+(1/40)*x)) := h311.inv (by decide +kernel)

def c313 : Certificate := ⟨(164090828030941/100000000000000),(796086770221/100000000000000),(-1016923189/100000000000000),(129899/10000000000000),(173/6250000000000)⟩
theorem h313 : c313.Valid (fun x => f313 ((113/40)+(1/40)*x)) := h307.mul h312 (by decide +kernel)

def c314 : Certificate := RationalModel.addExact c313 SharedCertificates.c53
theorem h314 : c314.Valid (fun x => f314 ((113/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h53 (113/40) (1/40))

def c315 : Certificate := RationalModel.addExact c313 SharedCertificates.c50
theorem h315 : c315.Valid (fun x => f315 ((113/40)+(1/40)*x)) := h313.addExact (SharedCertificates.h50 (113/40) (1/40))

def c316 : Certificate := ⟨(21547506212153/100000000000000),(-18480956303/50000000000000),(13827317/12500000000000),(-66211/20000000000000),(131/12500000000000)⟩
theorem h316 : c316.Valid (fun x => f316 ((113/40)+(1/40)*x)) := h315.inv (by decide +kernel)

def c317 : Certificate := ⟨(13809975151387/100000000000000),(73923825211/50000000000000),(-110618537/25000000000000),(1324217/100000000000000),(221/4000000000000)⟩
theorem h317 : c317.Valid (fun x => f317 ((113/40)+(1/40)*x)) := h314.mul h316 (by decide +kernel)

def c318 : Certificate := RationalModel.scale (2) c317
theorem h318 : c318.Valid (fun x => f318 ((113/40)+(1/40)*x)) := h317.scale (2)

def c319 : Certificate := ⟨(1907154136819/100000000000000),(4083544757/10000000000000),(96378137/100000000000000),(-235657/25000000000000),(743/10000000000000)⟩
theorem h319 : c319.Valid (fun x => f319 ((113/40)+(1/40)*x)) := h317.mul h317 (by decide +kernel)

def c320 : Certificate := RationalModel.neg c318
theorem h320 : c320.Valid (fun x => f320 ((113/40)+(1/40)*x)) := h318.neg

def c321 : Certificate := RationalModel.addExact SharedCertificates.c144 c320
theorem h321 : c321.Valid (fun x => f321 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h320

def c322 : Certificate := ⟨(22359094617041/100000000000000),(59138409419/12500000000000),(513023439/50000000000000),(-5512653/50000000000000),(44959/50000000000000)⟩
theorem h322 : c322.Valid (fun x => f322 ((113/40)+(1/40)*x)) := h319.mul h321 (by decide +kernel)

def c323 : Certificate := RationalModel.addExact SharedCertificates.c148 c322
theorem h323 : c323.Valid (fun x => f323 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h322

def c324 : Certificate := ⟨(-482577183945873/25000000000000),(-5150069416467/25000000000000),(15672155579/25000000000000),(-187193281/100000000000000),(399741/50000000000000)⟩
theorem h324 : c324.Valid (fun x => f324 ((113/40)+(1/40)*x)) := h317.mul h323 (by decide +kernel)

def c325 : Certificate := RationalModel.addExact SharedCertificates.c151 c324
theorem h325 : c325.Valid (fun x => f325 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h324

def c326 : Certificate := ⟨(-4133368199145113/100000000000000),(-1177403786417/2500000000000),(110634135227/100000000000000),(-14897439/6250000000000),(1297491/50000000000000)⟩
theorem h326 : c326.Valid (fun x => f326 ((113/40)+(1/40)*x)) := h317.mul h325 (by decide +kernel)

def c327 : Certificate := RationalModel.addExact SharedCertificates.c154 c326
theorem h327 : c327.Valid (fun x => f327 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h326

def c328 : Certificate := ⟨(2373011656033361/50000000000000),(11076572708329/25000000000000),(-103207734021/50000000000000),(794129723/100000000000000),(746339/20000000000000)⟩
theorem h328 : c328.Valid (fun x => f328 ((113/40)+(1/40)*x)) := h317.mul h327 (by decide +kernel)

def c329 : Certificate := RationalModel.addExact SharedCertificates.c157 c328
theorem h329 : c329.Valid (fun x => f329 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h328

def c330 : Certificate := ⟨(7577949274515899/50000000000000),(168375604653053/100000000000000),(-448597896473/100000000000000),(132715039/12500000000000),(1853443/20000000000000)⟩
theorem h330 : c330.Valid (fun x => f330 ((113/40)+(1/40)*x)) := h317.mul h329 (by decide +kernel)

def c331 : Certificate := RationalModel.addExact SharedCertificates.c160 c330
theorem h331 : c331.Valid (fun x => f331 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h330

def c332 : Certificate := ⟨(9343262778068889/50000000000000),(246560571080439/100000000000000),(-56185871673/25000000000000),(-365725751/50000000000000),(10835829/50000000000000)⟩
theorem h332 : c332.Valid (fun x => f332 ((113/40)+(1/40)*x)) := h318.mul h331 (by decide +kernel)

def c333 : Certificate := RationalModel.addExact SharedCertificates.c41 c317
theorem h333 : c333.Valid (fun x => f333 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h317

def c334 : Certificate := ⟨(129527104439593/100000000000000),(168265374207/50000000000000),(-788570159/100000000000000),(852903/50000000000000),(231/1250000000000)⟩
theorem h334 : c334.Valid (fun x => f334 ((113/40)+(1/40)*x)) := h333.mul h333 (by decide +kernel)

def c335 : Certificate := RationalModel.scale (105) c334
theorem h335 : c335.Valid (fun x => f335 ((113/40)+(1/40)*x)) := h334.scale (105)

def c336 : Certificate := RationalModel.scale (3) c319
theorem h336 : c336.Valid (fun x => f336 ((113/40)+(1/40)*x)) := h319.scale (3)

def c337 : Certificate := RationalModel.neg c336
theorem h337 : c337.Valid (fun x => f337 ((113/40)+(1/40)*x)) := h336.neg

def c338 : Certificate := RationalModel.addExact SharedCertificates.c167 c337
theorem h338 : c338.Valid (fun x => f338 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h337

def c339 : Certificate := ⟨(16805897787160133/25000000000000),(157995636049939/100000000000000),(-491873759187/100000000000000),(253833961/20000000000000),(13654877/100000000000000)⟩
theorem h339 : c339.Valid (fun x => f339 ((113/40)+(1/40)*x)) := h335.mul h338 (by decide +kernel)

def c340 : Certificate := ⟨(29751460251/20000000000000),(-10925761/3125000000000),(59693/3125000000000),(-9857/100000000000000),(39/50000000000000)⟩
theorem h340 : c340.Valid (fun x => f340 ((113/40)+(1/40)*x)) := h339.inv (by decide +kernel)

def c341 : Certificate := ⟨(6949392778909/25000000000000),(301444207611/100000000000000),(-839412619/100000000000000),(64137/2500000000000),(18283/25000000000000)⟩
theorem h341 : c341.Valid (fun x => f341 ((113/40)+(1/40)*x)) := h332.mul h340 (by decide +kernel)

def c342 : Certificate := RationalModel.scale (3) c313
theorem h342 : c342.Valid (fun x => f342 ((113/40)+(1/40)*x)) := h313.scale (3)

def c343 : Certificate := RationalModel.addExact c342 SharedCertificates.c41
theorem h343 : c343.Valid (fun x => f343 ((113/40)+(1/40)*x)) := h342.addExact (SharedCertificates.h41 (113/40) (1/40))

def c344 : Certificate := ⟨(16884120516449/100000000000000),(-13616595737/20000000000000),(361504953/100000000000000),(-959753/50000000000000),(1293/12500000000000)⟩
theorem h344 : c344.Valid (fun x => f344 ((113/40)+(1/40)*x)) := h343.inv (by decide +kernel)

def c345 : Certificate := ⟨(5410586322367/50000000000000),(5673581557/6250000000000),(-241003303/50000000000000),(127967/5000000000000),(27049/100000000000000)⟩
theorem h345 : c345.Valid (fun x => f345 ((113/40)+(1/40)*x)) := h314.mul h344 (by decide +kernel)

def c346 : Certificate := RationalModel.scale (2) c345
theorem h346 : c346.Valid (fun x => f346 ((113/40)+(1/40)*x)) := h345.scale (2)

def c347 : Certificate := ⟨(1170977774071/100000000000000),(19646337773/100000000000000),(-2739043/12500000000000),(-64241/20000000000000),(12901/100000000000000)⟩
theorem h347 : c347.Valid (fun x => f347 ((113/40)+(1/40)*x)) := h345.mul h345 (by decide +kernel)

def c348 : Certificate := RationalModel.neg c346
theorem h348 : c348.Valid (fun x => f348 ((113/40)+(1/40)*x)) := h346.neg

def c349 : Certificate := RationalModel.addExact SharedCertificates.c144 c348
theorem h349 : c349.Valid (fun x => f349 ((113/40)+(1/40)*x)) := (SharedCertificates.h144 (113/40) (1/40)).addExact h348

def c350 : Certificate := ⟨(3449576558931/25000000000000),(229378160889/100000000000000),(-56517247/20000000000000),(-3615707/100000000000000),(153327/100000000000000)⟩
theorem h350 : c350.Valid (fun x => f350 ((113/40)+(1/40)*x)) := h347.mul h349 (by decide +kernel)

def c351 : Certificate := RationalModel.addExact SharedCertificates.c148 c350
theorem h351 : c351.Valid (fun x => f351 ((113/40)+(1/40)*x)) := (SharedCertificates.h148 (113/40) (1/40)).addExact h350

def c352 : Certificate := ⟨(-23647984870671/1562500000000),(-12671475550357/100000000000000),(3379603013/5000000000000),(-359707859/100000000000000),(760777/20000000000000)⟩
theorem h352 : c352.Valid (fun x => f352 ((113/40)+(1/40)*x)) := h345.mul h351 (by decide +kernel)

def c353 : Certificate := RationalModel.addExact SharedCertificates.c151 c352
theorem h353 : c353.Valid (fun x => f353 ((113/40)+(1/40)*x)) := (SharedCertificates.h151 (113/40) (1/40)).addExact h352

def c354 : Certificate := ⟨(-3193703653796297/100000000000000),(-14081367917261/50000000000000),(13806830957/10000000000000),(-671839079/100000000000000),(4690877/50000000000000)⟩
theorem h354 : c354.Valid (fun x => f354 ((113/40)+(1/40)*x)) := h345.mul h353 (by decide +kernel)

def c355 : Certificate := RationalModel.addExact SharedCertificates.c154 c354
theorem h355 : c355.Valid (fun x => f355 ((113/40)+(1/40)*x)) := (SharedCertificates.h154 (113/40) (1/40)).addExact h354

def c356 : Certificate := ⟨(1910277641042057/50000000000000),(29002566021193/100000000000000),(-180803443157/100000000000000),(218397647/20000000000000),(6292191/50000000000000)⟩
theorem h356 : c356.Valid (fun x => f356 ((113/40)+(1/40)*x)) := h345.mul h355 (by decide +kernel)

def c357 : Certificate := RationalModel.addExact SharedCertificates.c157 c356
theorem h357 : c357.Valid (fun x => f357 ((113/40)+(1/40)*x)) := (SharedCertificates.h157 (113/40) (1/40)).addExact h356

def c358 : Certificate := ⟨(5887830080016263/50000000000000),(20384557003181/20000000000000),(-64719946261/12500000000000),(1299665577/50000000000000),(6686197/20000000000000)⟩
theorem h358 : c358.Valid (fun x => f358 ((113/40)+(1/40)*x)) := h345.mul h357 (by decide +kernel)

def c359 : Certificate := RationalModel.addExact SharedCertificates.c160 c358
theorem h359 : c359.Valid (fun x => f359 ((113/40)+(1/40)*x)) := (SharedCertificates.h160 (113/40) (1/40)).addExact h358

def c360 : Certificate := ⟨(13910760308919259/100000000000000),(138753905077131/100000000000000),(-273317827657/50000000000000),(241257013/12500000000000),(7137851/12500000000000)⟩
theorem h360 : c360.Valid (fun x => f360 ((113/40)+(1/40)*x)) := h346.mul h359 (by decide +kernel)

def c361 : Certificate := RationalModel.addExact SharedCertificates.c41 c345
theorem h361 : c361.Valid (fun x => f361 ((113/40)+(1/40)*x)) := (SharedCertificates.h41 (113/40) (1/40)).addExact h345

def c362 : Certificate := ⟨(122813323063539/100000000000000),(201200947597/100000000000000),(-246481389/25000000000000),(191899/4000000000000),(66999/100000000000000)⟩
theorem h362 : c362.Valid (fun x => f362 ((113/40)+(1/40)*x)) := h361.mul h361 (by decide +kernel)

def c363 : Certificate := RationalModel.scale (105) c362
theorem h363 : c363.Valid (fun x => f363 ((113/40)+(1/40)*x)) := h362.scale (105)

def c364 : Certificate := RationalModel.scale (3) c347
theorem h364 : c364.Valid (fun x => f364 ((113/40)+(1/40)*x)) := h347.scale (3)

def c365 : Certificate := RationalModel.neg c364
theorem h365 : c365.Valid (fun x => f365 ((113/40)+(1/40)*x)) := h364.neg

def c366 : Certificate := RationalModel.addExact SharedCertificates.c167 c365
theorem h366 : c366.Valid (fun x => f366 ((113/40)+(1/40)*x)) := (SharedCertificates.h167 (113/40) (1/40)).addExact h365

def c367 : Certificate := ⟨(64023987842606277/100000000000000),(6080495675719/6250000000000),(-258974356853/50000000000000),(2700143127/100000000000000),(40092667/100000000000000)⟩
theorem h367 : c367.Valid (fun x => f367 ((113/40)+(1/40)*x)) := h363.mul h366 (by decide +kernel)

def c368 : Certificate := ⟨(156191457873/100000000000000),(-118670707/50000000000000),(1624229/100000000000000),(-343/3125000000000),(141/100000000000000)⟩
theorem h368 : c368.Valid (fun x => f368 ((113/40)+(1/40)*x)) := h367.inv (by decide +kernel)

def c369 : Certificate := ⟨(21727419327719/100000000000000),(9185287599/5000000000000),(-957176077/100000000000000),(5038811/100000000000000),(431/312500000000)⟩
theorem h369 : c369.Valid (fun x => f369 ((113/40)+(1/40)*x)) := h360.mul h368 (by decide +kernel)

def c370 : Certificate := RationalModel.addExact c341 c369
theorem h370 : c370.Valid (fun x => f370 ((113/40)+(1/40)*x)) := h341.addExact h369

def c371 : Certificate := ⟨(66493967579051/20000000000000),(2023506847729/50000000000000),(13303227/1000000000000),(53701941/50000000000000),(2707763/100000000000000)⟩
theorem h371 : c371.Valid (fun x => f371 ((113/40)+(1/40)*x)) := h300.mul h370 (by decide +kernel)

def c372 : Certificate := ⟨(7355527387063/6250000000000),(391080616151/100000000000000),(-2989979719/100000000000000),(64479067/100000000000000),(1499641/50000000000000)⟩
theorem h372 : c372.Valid (fun x => f372 ((113/40)+(1/40)*x)) := h371.mul h114 (by decide +kernel)

def c373 : Certificate := RationalModel.addExact c288 c372
theorem h373 : c373.Valid (fun x => f373 ((113/40)+(1/40)*x)) := h288.addExact h372

def c374 : Certificate := ⟨(12180784293457031/50000000000000),(255395587158203/25000000000000),(1749353/10240000),(14577/10240000),(147949219/25000000000000)⟩
theorem h374 : c374.Valid (fun x => f374 ((113/40)+(1/40)*x)) := h17.mul h42 (by decide +kernel)

def c375 : Certificate := ⟨(54289/1600),(233/800),(1/1600),0,0⟩
theorem h375 : c375.Valid (fun x => f375 ((113/40)+(1/40)*x)) := h133.mul h133 (by decide +kernel)

def c376 : Certificate := ⟨(12649337/64000),(162867/64000),(699/64000),(1/64000),0⟩
theorem h376 : c376.Valid (fun x => f376 ((113/40)+(1/40)*x)) := h375.mul h133 (by decide +kernel)

def c377 : Certificate := ⟨(601870490047831563/12500000000000),(263906796752388449/100000000000000),(6242282166111021/100000000000000),(83147933630493/100000000000000),(68510975269/10000000000000)⟩
theorem h377 : c377.Valid (fun x => f377 ((113/40)+(1/40)*x)) := h374.mul h376 (by decide +kernel)

def c378 : Certificate := ⟨(51921469/2500000000000),(-28458009/25000000000000),(3546591/100000000000000),(-82677/100000000000000),(599/25000000000000)⟩
theorem h378 : c378.Valid (fun x => f378 ((113/40)+(1/40)*x)) := h377.inv (by decide +kernel)

def c379 : Certificate := ⟨(2698744586703/50000000000000),(-3577742077/20000000000000),(-19423159/20000000000000),(2908771/100000000000000),(1181211/10000000000000)⟩
theorem h379 : c379.Valid (fun x => f379 ((113/40)+(1/40)*x)) := h32.mul h378 (by decide +kernel)

def c380 : Certificate := RationalModel.addExact c373 c379
theorem h380 : c380.Valid (fun x => f380 ((113/40)+(1/40)*x)) := h373.addExact h379

theorem compact_model : c380.Valid (fun x => compactKernel ((113/40)+(1/40)*x)) := by
  simpa only [compact_kernel_dag] using h380

end Hf4Quad.Panel36
