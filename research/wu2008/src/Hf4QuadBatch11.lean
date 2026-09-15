import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel34
open Hf4Quad.Dag

def p0 : Cubic := ⟨(109/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((109/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((109/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((109/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((109/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(477523809523809/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((109/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-477523809523809/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((109/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-193047619047619/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((109/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((109/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(11881/1600),(109/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((109/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(224733201058201/25000000000000),(16494179894179/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((109/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-224733201058201/25000000000000),(-16494179894179/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((109/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-642514021164021/50000000000000),(-20875132275131/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((109/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((109/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1295029/64000),(35643/64000),(327/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((109/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(788558746412037/4000000000000),(542586293402777/100000000000000),(4977855902777/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/25000000000000)
theorem h14 : Model (fun x => f14 ((109/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-788558746412037/4000000000000),(-542586293402777/100000000000000),(-4977855902777/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/25000000000000)
theorem h15 : Model (fun x => f15 ((109/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-20998996702628967/100000000000000),(-140865356419477/25000000000000),(-2526758639219/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/12500000000000)
theorem h16 : Model (fun x => f16 ((109/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((109/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(141158161/2560000),(1295029/640000),(35643/1280000),(109/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((109/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(15404164394841269/100000000000000),(17665326140873/3125000000000),(1944806547619/25000000000000),(47579365079/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((109/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2797416153893849/50000000000000),(457252707507/25000000000000),(1362854456019/50000000000000),(16178282077/50000000000000)⟩
def e20 : ℝ := (21825399/20000000000000)
theorem h20 : Model (fun x => f20 ((109/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((109/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1878203069946289/12500000000000),(172312208251953/25000000000000),(1295029/10240000),(11881/10240000)⟩
def e22 : ℝ := (266601563/50000000000000)
theorem h22 : Model (fun x => f22 ((109/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(19577832296506799/20000000000000),(898065701674623/20000000000000),(5149459298593/6250000000000),(377941966869/50000000000000)⟩
def e23 : ℝ := (3473719627/100000000000000)
theorem h23 : Model (fun x => f23 ((109/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(92294329174746297/100000000000000),(4492157519203143/100000000000000),(42558528844763/50000000000000),(197060124473/25000000000000)⟩
def e24 : ℝ := (1791423311/50000000000000)
theorem h24 : Model (fun x => f24 ((109/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((109/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(409448269248291/1000000000000),(450768736787109/20000000000000),(10338732495117/20000000000000),(316169189453/50000000000000)⟩
def e26 : ℝ := (1091735841/25000000000000)
theorem h26 : Model (fun x => f26 ((109/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(91941717179351693/100000000000000),(2530505977413347/50000000000000),(58039127922323/50000000000000),(709958751343/50000000000000)⟩
def e27 : ℝ := (9805982879/100000000000000)
theorem h27 : Model (fun x => f27 ((109/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(18423604635409799/10000000000000),(9553169474029837/100000000000000),(50298828383543/25000000000000),(1104079000289/50000000000000)⟩
def e28 : ℝ := (13388829501/100000000000000)
theorem h28 : Model (fun x => f28 ((109/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((109/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(111574653370159297/100000000000000),(7165344711845087/100000000000000),(197211322344357/100000000000000),(376932955551/12500000000000)⟩
def e30 : ℝ := (13908776863/50000000000000)
theorem h30 : Model (fun x => f30 ((109/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(13238421173681599/50000000000000),(1700347673683873/100000000000000),(584981997827/1250000000000),(178893577317/25000000000000)⟩
def e31 : ℝ := (6601149657/100000000000000)
theorem h31 : Model (fun x => f31 ((109/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(52678222175365297/25000000000000),(1125351714771371/10000000000000),(61998468340083/25000000000000),(1461866154923/50000000000000)⟩
def e32 : ℝ := (9994989579/50000000000000)
theorem h32 : Model (fun x => f32 ((109/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((109/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(5096949/320),(46761/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((109/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((109/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(240781/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((109/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1789889/64),(64433/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((109/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((109/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1935809/64),(64433/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((109/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1935809/64),(-64433/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((109/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((109/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(149/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((109/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(22201/1600),(149/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((109/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((109/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(466221/160),(3129/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((109/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(17159244221/50000000000000),(-115162713/25000000000000),(289839/6250000000000),(-41499/100000000000000)⟩
def e46 : ℝ := (357/100000000000000)
theorem h46 : Model (fun x => f46 ((109/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (229971/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-259507964032889/25000000000000),(113043731967/100000000000000),(-192370647/25000000000000),(5261321/100000000000000)⟩
def e47 : ℝ := (10746463/50000000000000)
theorem h47 : Model (fun x => f47 ((109/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((109/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(189/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((109/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((109/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((109/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(78749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((109/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(128749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((109/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((109/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(128749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((109/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((109/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2703749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((109/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((109/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(28749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((109/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(388664062499983/50000000000000),(13781249999977/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (27/20000000000000)
theorem h60 : Model (fun x => f60 ((109/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(165765624999997/100000000000000),(134114583333/12500000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((109/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((109/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(128749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((109/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1453265624999987/100000000000000),(1309895833331/25000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((109/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1553265624999987/100000000000000),(1309895833331/25000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((109/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(6036985279540701/50000000000000),(254788173827691/100000000000000),(650935058589/50000000000000),(2149522569/100000000000000)⟩
def e66 : ℝ := (25419/4000000000000)
theorem h66 : Model (fun x => f66 ((109/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(228749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((109/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(104653124999999/20000000000000),(476562499999/25000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((109/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1196970117187483/100000000000000),(6540820312487/100000000000000),(11914062499/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (69/100000000000000)
theorem h69 : Model (fun x => f69 ((109/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(144521819550218853/100000000000000),(3839475021697257/100000000000000),(3368673329327/10000000000000),(35527789137/25000000000000)⟩
def e70 : ℝ := (80534977/25000000000000)
theorem h70 : Model (fun x => f70 ((109/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((109/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3481078124999937/12500000000000),(2816406249993/1562500000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((109/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1000809960937447/12500000000000),(167857812499681/100000000000000),(208723958331/25000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1713/100000000000000)
theorem h73 : Model (fun x => f73 ((109/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(95835169298055697/100000000000000),(506579460940179/20000000000000),(4385325704909/20000000000000),(89733405183/100000000000000)⟩
def e74 : ℝ := (19133317/10000000000000)
theorem h74 : Model (fun x => f74 ((109/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(4807139776965491/2000000000000),(796546540799769/12500000000000),(11122672363563/20000000000000),(231844561731/100000000000000)⟩
def e75 : ℝ := (256736539/50000000000000)
theorem h75 : Model (fun x => f75 ((109/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((109/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1160359374999979/12500000000000),(938802083331/1562500000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((109/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(8265624999999/100000000000000),(59895833333/25000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((109/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(2376367187499/100000000000000),(103320312499/100000000000000),(1497395833/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((109/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(220595195556543/100000000000000),(172170251209/1562500000000),(203390028179/100000000000000),(1671639873/100000000000000)⟩
def e80 : ℝ := (2904767/50000000000000)
theorem h80 : Model (fun x => f80 ((109/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(504611509835589/100000000000000),(6531217856287/25000000000000),(15973961139/3125000000000),(233566733/5000000000000)⟩
def e81 : ℝ := (20278693/100000000000000)
theorem h81 : Model (fun x => f81 ((109/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(240861600358110139/100000000000000),(63984971978233/1000000000000),(56124528574263/100000000000000),(236515896391/100000000000000)⟩
def e82 : ℝ := (533751771/100000000000000)
theorem h82 : Model (fun x => f82 ((109/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(136641113281/20000000000000),(39606119791/100000000000000),(215250651/25000000000000),(1663773/20000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((109/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(196421600341/100000000000000),(14233449299/100000000000000),(412563747/100000000000000),(373699/6250000000000)⟩
def e84 : ℝ := (43457/100000000000000)
theorem h84 : Model (fun x => f84 ((109/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(28235605049/50000000000000),(613817501/12500000000000),(44479529/25000000000000),(3438031/100000000000000)⟩
def e85 : ℝ := (37589/100000000000000)
theorem h85 : Model (fun x => f85 ((109/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(16235472903/100000000000000),(1647076961/100000000000000),(71612041/100000000000000),(1729759/100000000000000)⟩
def e86 : ℝ := (2529/10000000000000)
theorem h86 : Model (fun x => f86 ((109/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(48706418709/100000000000000),(4941230883/100000000000000),(214836123/100000000000000),(5189277/100000000000000)⟩
def e87 : ℝ := (7587/10000000000000)
theorem h87 : Model (fun x => f87 ((109/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-48706418709/100000000000000),(-4941230883/100000000000000),(-214836123/100000000000000),(-5189277/100000000000000)⟩
def e88 : ℝ := (7587/10000000000000)
theorem h88 : Model (fun x => f88 ((109/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(24086155165169143/10000000000000),(6398492256592417/100000000000000),(2806215686907/5000000000000),(118255353557/50000000000000)⟩
def e89 : ℝ := (533827641/100000000000000)
theorem h89 : Model (fun x => f89 ((109/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3481078124999937/10000000000000),(2816406249993/1250000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((109/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(547613828613271/20000000000000),(19949501953087/100000000000000),(10901367187/20000000000000),(13237847/20000000000000)⟩
def e91 : ℝ := (30349/100000000000000)
theorem h91 : Model (fun x => f91 ((109/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(953143259866561131/100000000000000),(2622757904661903/20000000000000),(7390552076169/10000000000000),(218584263721/100000000000000)⟩
def e92 : ℝ := (71759899/20000000000000)
theorem h92 : Model (fun x => f92 ((109/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(10491602281/100000000000000),(-72174179/50000000000000),(586253/50000000000000),(-3673/50000000000000)⟩
def e93 : ℝ := (51/100000000000000)
theorem h93 : Model (fun x => f93 ((109/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (93995534587942671/10000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(1263511802357/5000000000000),(323624664679/100000000000000),(-65457823/12500000000000),(1128253/100000000000000)⟩
def e94 : ℝ := (337657/100000000000000)
theorem h94 : Model (fun x => f94 ((109/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(78749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((109/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(3883495145631/10000000000000),(-15709931819/12500000000000),(203364813/50000000000000),(-658139/50000000000000)⟩
def e96 : ℝ := (2139/50000000000000)
theorem h96 : Model (fun x => f96 ((109/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (256666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(61165048543687/50000000000000),(251358909099/100000000000000),(-406729627/50000000000000),(2632551/100000000000000)⟩
def e97 : ℝ := (8873/25000000000000)
theorem h97 : Model (fun x => f97 ((109/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1284466019417427/50000000000000),(5278537091079/100000000000000),(-8541322167/50000000000000),(55283571/100000000000000)⟩
def e98 : ℝ := (186333/25000000000000)
theorem h98 : Model (fun x => f98 ((109/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(11165048543687/50000000000000),(251358909099/100000000000000),(-406729627/50000000000000),(2632551/100000000000000)⟩
def e99 : ℝ := (8873/25000000000000)
theorem h99 : Model (fun x => f99 ((109/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(573645018380479/100000000000000),(381797100277/5000000000000),(-178808019/1562500000000),(-369011/6250000000000)⟩
def e100 : ℝ := (749871/50000000000000)
theorem h100 : Model (fun x => f100 ((109/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(149646526534063/100000000000000),(614975195077/100000000000000),(-1358397979/100000000000000),(2351399/100000000000000)⟩
def e101 : ℝ := (106911/100000000000000)
theorem h101 : Model (fun x => f101 ((109/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(61165048543687/5000000000000),(251358909099/10000000000000),(-406729627/5000000000000),(2632551/10000000000000)⟩
def e102 : ℝ := (8873/2500000000000)
theorem h102 : Model (fun x => f102 ((109/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1372947497407803/100000000000000),(3128564286067/100000000000000),(-9492990519/100000000000000),(28676909/100000000000000)⟩
def e103 : ℝ := (461831/100000000000000)
theorem h103 : Model (fun x => f103 ((109/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1472947497407803/100000000000000),(3128564286067/100000000000000),(-9492990519/100000000000000),(28676909/100000000000000)⟩
def e104 : ℝ := (461831/100000000000000)
theorem h104 : Model (fun x => f104 ((109/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(2112372485559949/25000000000000),(65210134923983/50000000000000),(992462491/6250000000000),(-1005364929/100000000000000)⟩
def e105 : ℝ := (13958089/50000000000000)
theorem h105 : Model (fun x => f105 ((109/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(111165048543687/50000000000000),(251358909099/100000000000000),(-406729627/50000000000000),(2632551/100000000000000)⟩
def e106 : ℝ := (8873/25000000000000)
theorem h106 : Model (fun x => f106 ((109/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(494306720708811/100000000000000),(44707720531/4000000000000),(-2985316487/100000000000000),(7616501/100000000000000)⟩
def e107 : ℝ := (35579/20000000000000)
theorem h107 : Model (fun x => f107 ((109/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(549496306030657/50000000000000),(3727451942329/100000000000000),(-3924409921/50000000000000),(6675407/50000000000000)⟩
def e108 : ℝ := (161199/25000000000000)
theorem h108 : Model (fun x => f108 ((109/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(18571854044415829/20000000000000),(874129903614243/50000000000000),(4372681069761/100000000000000),(-4891341407/25000000000000)⟩
def e109 : ℝ := (384552357/100000000000000)
theorem h109 : Model (fun x => f109 ((109/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(3142577057215323/12500000000000),(12914479096617/12500000000000),(-28526357559/12500000000000),(49379379/12500000000000)⟩
def e110 : ℝ := (2245131/12500000000000)
theorem h110 : Model (fun x => f110 ((109/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(5613924063373779/100000000000000),(2156592625843/2500000000000),(4225172389/100000000000000),(-166002319/25000000000000)⟩
def e111 : ℝ := (2324263/12500000000000)
theorem h111 : Model (fun x => f111 ((109/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(1233932214064203/2000000000000),(1157288066752047/100000000000000),(564249139081/20000000000000),(-6580549927/50000000000000)⟩
def e112 : ℝ := (25541511/10000000000000)
theorem h112 : Model (fun x => f112 ((109/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(30911176185057859/20000000000000),(2905547873980533/100000000000000),(3596963382583/50000000000000),(-16363232741/50000000000000)⟩
def e113 : ℝ := (639967467/100000000000000)
theorem h113 : Model (fun x => f113 ((109/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(1047525685738441/12500000000000),(4304826365539/12500000000000),(-9508785853/12500000000000),(16459793/12500000000000)⟩
def e114 : ℝ := (748377/12500000000000)
theorem h114 : Model (fun x => f114 ((109/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(997266471863/20000000000000),(112257376879/100000000000000),(268520529/100000000000000),(-2913703/100000000000000)⟩
def e115 : ℝ := (35927/100000000000000)
theorem h115 : Model (fun x => f115 ((109/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(556726428467/50000000000000),(37600771867/100000000000000),(30156803/10000000000000),(-757583/100000000000000)⟩
def e116 : ℝ := (16509/100000000000000)
theorem h116 : Model (fun x => f116 ((109/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(93309637399777/100000000000000),(3534479643967/100000000000000),(37374197339/100000000000000),(13231989/100000000000000)⟩
def e117 : ℝ := (1899887/100000000000000)
theorem h117 : Model (fun x => f117 ((109/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(518638518557/250000000000),(8092754110617/100000000000000),(11402410353/12500000000000),(4853347/5000000000000)⟩
def e118 : ℝ := (2220897/50000000000000)
theorem h118 : Model (fun x => f118 ((109/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(30952667266542419/20000000000000),(58272812561823/2000000000000),(728514604799/10000000000000),(-16314699271/50000000000000)⟩
def e119 : ℝ := (644409261/100000000000000)
theorem h119 : Model (fun x => f119 ((109/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(9945404159/4000000000000),(5597525909/50000000000000),(76397919/50000000000000),(156147/50000000000000)⟩
def e120 : ℝ := (47/625000000000)
theorem h120 : Model (fun x => f120 ((109/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(5552046011/10000000000000),(390604053/12500000000000),(60236673/100000000000000),(369279/100000000000000)⟩
def e121 : ℝ := (1959/100000000000000)
theorem h121 : Model (fun x => f121 ((109/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2479554529/20000000000000),(104666717/12500000000000),(4170763/20000000000000),(26239/12500000000000)⟩
def e122 : ℝ := (989/100000000000000)
theorem h122 : Model (fun x => f122 ((109/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(692108667/25000000000000),(109070171/50000000000000),(6660539/100000000000000),(46403/50000000000000)⟩
def e123 : ℝ := (611/100000000000000)
theorem h123 : Model (fun x => f123 ((109/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(2076326001/25000000000000),(327210513/50000000000000),(19981617/100000000000000),(139209/50000000000000)⟩
def e124 : ℝ := (1833/100000000000000)
theorem h124 : Model (fun x => f124 ((109/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-2076326001/25000000000000),(-327210513/50000000000000),(-19981617/100000000000000),(-139209/50000000000000)⟩
def e125 : ℝ := (1833/100000000000000)
theorem h125 : Model (fun x => f125 ((109/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(154763328027408091/100000000000000),(728409993417531/25000000000000),(7285126066373/100000000000000),(-203935481/625000000000)⟩
def e126 : ℝ := (322205547/50000000000000)
theorem h126 : Model (fun x => f126 ((109/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(3142577057215323/10000000000000),(12914479096617/10000000000000),(-28526357559/10000000000000),(49379379/10000000000000)⟩
def e127 : ℝ := (2245131/10000000000000)
theorem h127 : Model (fun x => f127 ((109/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1221695670689493/50000000000000),(11049663363021/100000000000000),(-851043167/5000000000000),(1070551/12500000000000)⟩
def e128 : ℝ := (63201/3125000000000)
theorem h128 : Model (fun x => f128 ((109/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(767854557121617449/100000000000000),(6627954497767639/100000000000000),(60969427623/3125000000000),(-2421592329/6250000000000)⟩
def e129 : ℝ := (651763177/50000000000000)
theorem h129 : Model (fun x => f129 ((109/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(13023299669/100000000000000),(-112414307/100000000000000),(187449/20000000000000),(-1787/25000000000000)⟩
def e130 : ℝ := (79/100000000000000)
theorem h130 : Model (fun x => f130 ((109/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (47576538222072641/6250000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(10077645993363/50000000000000),(102737971177/50000000000000),(-876072833/100000000000000),(3806477/100000000000000)⟩
def e131 : ℝ := (78341/25000000000000)
theorem h131 : Model (fun x => f131 ((109/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(22712764016933/50000000000000),(529100607033/100000000000000),(-1399735417/100000000000000),(493473/10000000000000)⟩
def e132 : ℝ := (651021/100000000000000)
theorem h132 : Model (fun x => f132 ((109/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-188612580723/40000000000),(-5440882139833/100000000000000),(14778273073/100000000000000),(-54487737/100000000000000)⟩
def e133 : ℝ := (16680143/100000000000000)
theorem h133 : Model (fun x => f133 ((109/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(18348623853211/50000000000000),(-336671997307/100000000000000),(19304587/625000000000),(-28337009/100000000000000)⟩
def e134 : ℝ := (262381/100000000000000)
theorem h134 : Model (fun x => f134 ((109/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (27/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-173039064883487/100000000000000),(-204569819769/50000000000000),(1147099269/12500000000000),(-10418627/10000000000000)⟩
def e135 : ℝ := (9616933/100000000000000)
theorem h135 : Model (fun x => f135 ((109/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(141158161/256000),(1295029/64000),(35643/128000),(109/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((109/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((109/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(11655261/32000),(320787/32000),(2943/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((109/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(234400249/256000),(1936603/64000),(9483/25600),(127/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((109/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-11881/1600),(-109/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((109/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(232499289/256000),(1927883/64000),(9467/25600),(127/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((109/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((109/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(327/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((109/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-327/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((109/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(228313689/256000),(1918283/64000),(9467/25600),(127/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((109/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(229081689/256000),(1918283/64000),(9467/25600),(127/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((109/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((109/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(229081689/4000),(1918283/1000),(9467/400),(127/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((109/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((109/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(26678892429/512000),(244760481/128000),(6736527/256000),(20601/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((109/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(479780037/25000000000000),(-17606607/25000000000000),(323057/20000000000000),(-29639/100000000000000)⟩
def e151 : ℝ := (67/12500000000000)
theorem h151 : Model (fun x => f151 ((109/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (12843147429/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(54954410612221/50000000000000),(-175967857127/50000000000000),(2831010523/100000000000000),(-5488379/25000000000000)⟩
def e152 : ℝ := (60306193/100000000000000)
theorem h152 : Model (fun x => f152 ((109/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(229/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((109/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(43281/1600),(209/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((109/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(447/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((109/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(559284116331/12500000000000),(-30028677387/100000000000000),(201534747/100000000000000),(-1352583/100000000000000)⟩
def e156 : ℝ := (4571/50000000000000)
theorem h156 : Model (fun x => f156 ((109/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (111/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(12103187919461/10000000000000),(35660931189/10000000000000),(403069479/100000000000000),(-2705187/100000000000000)⟩
def e157 : ℝ := (238971/50000000000000)
theorem h157 : Model (fun x => f157 ((109/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(22103187919461/10000000000000),(35660931189/10000000000000),(403069479/100000000000000),(-2705187/100000000000000)⟩
def e158 : ℝ := (238971/50000000000000)
theorem h158 : Model (fun x => f158 ((109/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(22103187919461/20000000000000),(35660931189/20000000000000),(201534739/100000000000000),(-676297/50000000000000)⟩
def e159 : ℝ := (59743/25000000000000)
theorem h159 : Model (fun x => f159 ((109/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(2103187919461/20000000000000),(35660931189/20000000000000),(201534739/100000000000000),(-676297/50000000000000)⟩
def e160 : ℝ := (59743/25000000000000)
theorem h160 : Model (fun x => f160 ((109/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((109/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((109/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(203928221875979/50000000000000),(82253635927/12500000000000),(148751831/20000000000000),(-1247929/25000000000000)⟩
def e163 : ℝ := (881923/100000000000000)
theorem h163 : Model (fun x => f163 ((109/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2763570729466243/100000000000000),(82253635927/12500000000000),(148751831/20000000000000),(-1247929/25000000000000)⟩
def e164 : ℝ := (220481/25000000000000)
theorem h164 : Model (fun x => f164 ((109/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((109/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1527093079052857/50000000000000),(706850288719/12500000000000),(302592959/4000000000000),(-2012211/5000000000000)⟩
def e166 : ℝ := (7598301/100000000000000)
theorem h166 : Model (fun x => f166 ((109/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4168283555243333/50000000000000),(706850288719/12500000000000),(302592959/4000000000000),(-2012211/5000000000000)⟩
def e167 : ℝ := (3799151/50000000000000)
theorem h167 : Model (fun x => f167 ((109/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((109/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4606617736157119/50000000000000),(21113945208969/100000000000000),(7048838173/20000000000000),(-206799/156250000000)⟩
def e169 : ℝ := (1139187/4000000000000)
theorem h169 : Model (fun x => f169 ((109/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14482283091361857/100000000000000),(21113945208969/100000000000000),(7048838173/20000000000000),(-206799/156250000000)⟩
def e170 : ℝ := (7119919/25000000000000)
theorem h170 : Model (fun x => f170 ((109/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((109/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(3201046246712037/20000000000000),(9831371994557/20000000000000),(52892213739/50000000000000),(-118380937/50000000000000)⟩
def e172 : ℝ := (4164741/6250000000000)
theorem h172 : Model (fun x => f172 ((109/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(1834094551927447/10000000000000),(9831371994557/20000000000000),(52892213739/50000000000000),(-118380937/50000000000000)⟩
def e173 : ℝ := (66635857/100000000000000)
theorem h173 : Model (fun x => f173 ((109/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((109/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(20269668271655991/100000000000000),(87028925480657/100000000000000),(48304200141/20000000000000),(-22205143/10000000000000)⟩
def e175 : ℝ := (118585413/100000000000000)
theorem h175 : Model (fun x => f175 ((109/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(20672049224036943/100000000000000),(87028925480657/100000000000000),(48304200141/20000000000000),(-22205143/10000000000000)⟩
def e176 : ℝ := (59292707/50000000000000)
theorem h176 : Model (fun x => f176 ((109/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((109/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(713934669811307/3125000000000),(66520030481043/50000000000000),(231878594927/50000000000000),(16205117/20000000000000)⟩
def e178 : ℝ := (90983239/50000000000000)
theorem h178 : Model (fun x => f178 ((109/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(2853536298292847/12500000000000),(66520030481043/50000000000000),(231878594927/50000000000000),(16205117/20000000000000)⟩
def e179 : ℝ := (181966479/100000000000000)
theorem h179 : Model (fun x => f179 ((109/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((109/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(12614449807233983/50000000000000),(18773437804457/10000000000000),(99468646779/12500000000000),(875794701/100000000000000)⟩
def e181 : ℝ := (257025549/100000000000000)
theorem h181 : Model (fun x => f181 ((109/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(25232232947801299/100000000000000),(18773437804457/10000000000000),(99468646779/12500000000000),(875794701/100000000000000)⟩
def e182 : ℝ := (5140511/2000000000000)
theorem h182 : Model (fun x => f182 ((109/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(106136255033683/4000000000000),(64732279943361/100000000000000),(234635677093/50000000000000),(387004047/25000000000000)⟩
def e183 : ℝ := (88870993/100000000000000)
theorem h183 : Model (fun x => f183 ((109/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(122137729050751/100000000000000),(197055065863/50000000000000),(190845381/25000000000000),(-2270973/100000000000000)⟩
def e184 : ℝ := (533483/100000000000000)
theorem h184 : Model (fun x => f184 ((109/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(42103187919461/20000000000000),(35660931189/20000000000000),(201534739/100000000000000),(-676297/50000000000000)⟩
def e185 : ℝ := (59743/25000000000000)
theorem h185 : Model (fun x => f185 ((109/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(443169608245361/100000000000000),(23459982613/3125000000000),(583225501/50000000000000),(-4976161/100000000000000)⟩
def e186 : ℝ := (1011427/100000000000000)
theorem h186 : Model (fun x => f186 ((109/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(932942664807417/100000000000000),(1185288067851/50000000000000),(4687273721/100000000000000),(-12877101/100000000000000)⟩
def e187 : ℝ := (802143/25000000000000)
theorem h187 : Model (fun x => f187 ((109/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1963993016723469/100000000000000),(6653920834591/100000000000000),(7987254751/50000000000000),(-5318423/20000000000000)⟩
def e188 : ℝ := (9041101/100000000000000)
theorem h188 : Model (fun x => f188 ((109/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2398776469341381/100000000000000),(7933621632751/50000000000000),(60727439121/100000000000000),(18335603/50000000000000)⟩
def e189 : ℝ := (21725981/100000000000000)
theorem h189 : Model (fun x => f189 ((109/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((109/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(22103187919461/2500000000000),(35660931189/2500000000000),(201534739/12500000000000),(-676297/6250000000000)⟩
def e191 : ℝ := (59743/3125000000000)
theorem h191 : Model (fun x => f191 ((109/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(1006265245829191/100000000000000),(910273689643/50000000000000),(593914859/25000000000000),(-523669/4000000000000)⟩
def e192 : ℝ := (2445259/100000000000000)
theorem h192 : Model (fun x => f192 ((109/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1106265245829191/100000000000000),(910273689643/50000000000000),(593914859/25000000000000),(-523669/4000000000000)⟩
def e193 : ℝ := (2445259/100000000000000)
theorem h193 : Model (fun x => f193 ((109/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(3317103800681527/12500000000000),(43840931972989/20000000000000),(203532798931/20000000000000),(1574163051/100000000000000)⟩
def e194 : ℝ := (299828891/100000000000000)
theorem h194 : Model (fun x => f194 ((109/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(376834755591/100000000000000),(-194550209/6250000000000),(112617/1000000000000),(3993/100000000000000)⟩
def e195 : ℝ := (2307/50000000000000)
theorem h195 : Model (fun x => f195 ((109/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (13158303103800337/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(249973935781/2500000000000),(32267681303/20000000000000),(52207651/100000000000000),(-689063/50000000000000)⟩
def e196 : ℝ := (58819/12500000000000)
theorem h196 : Model (fun x => f196 ((109/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(12103187919461/5000000000000),(35660931189/5000000000000),(403069479/50000000000000),(-2705187/50000000000000)⟩
def e197 : ℝ := (238971/25000000000000)
theorem h197 : Model (fun x => f197 ((109/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(22621171290851/50000000000000),(-36496637307/50000000000000),(35263121/100000000000000),(157483/25000000000000)⟩
def e198 : ℝ := (801/800000000000)
theorem h198 : Model (fun x => f198 ((109/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (6896089488441/3125000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(54757657418297/50000000000000),(5839461969/4000000000000),(-17631561/25000000000000),(-1259867/100000000000000)⟩
def e199 : ℝ := (342487/50000000000000)
theorem h199 : Model (fun x => f199 ((109/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(4757657418297/50000000000000),(5839461969/4000000000000),(-17631561/25000000000000),(-1259867/100000000000000)⟩
def e200 : ℝ := (342487/50000000000000)
theorem h200 : Model (fun x => f200 ((109/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(202081830948477/50000000000000),(134689971011/25000000000000),(-10411017/4000000000000),(-464951/10000000000000)⟩
def e201 : ℝ := (2527883/100000000000000)
theorem h201 : Model (fun x => f201 ((109/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2759877947611239/100000000000000),(134689971011/25000000000000),(-10411017/4000000000000),(-464951/10000000000000)⟩
def e202 : ℝ := (631971/25000000000000)
theorem h202 : Model (fun x => f202 ((109/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(3022489023432177/100000000000000),(4619075161763/100000000000000),(-180620343/12500000000000),(-10155663/25000000000000)⟩
def e203 : ℝ := (5423413/25000000000000)
theorem h203 : Model (fun x => f203 ((109/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8304869975813129/100000000000000),(4619075161763/100000000000000),(-180620343/12500000000000),(-10155663/25000000000000)⟩
def e204 : ℝ := (21693653/100000000000000)
theorem h204 : Model (fun x => f204 ((109/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(2273776125195379/25000000000000),(2147823475157/12500000000000),(-696339927/100000000000000),(-154485453/100000000000000)⟩
def e205 : ℝ := (16164787/20000000000000)
theorem h205 : Model (fun x => f205 ((109/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(2872830423965827/20000000000000),(2147823475157/12500000000000),(-696339927/100000000000000),(-154485453/100000000000000)⟩
def e206 : ℝ := (631437/781250000000)
theorem h206 : Model (fun x => f206 ((109/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(1966368302204771/12500000000000),(39787295132787/100000000000000),(7095585581/50000000000000),(-9082231/2500000000000)⟩
def e207 : ℝ := (93791343/50000000000000)
theorem h207 : Model (fun x => f207 ((109/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(18066660703352453/100000000000000),(39787295132787/100000000000000),(7095585581/50000000000000),(-9082231/2500000000000)⟩
def e208 : ℝ := (187582687/100000000000000)
theorem h208 : Model (fun x => f208 ((109/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9892880174867823/50000000000000),(69948076050649/100000000000000),(60883867761/100000000000000),(-126563307/20000000000000)⟩
def e209 : ℝ := (165386013/50000000000000)
theorem h209 : Model (fun x => f209 ((109/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(10094070651058299/50000000000000),(69948076050649/100000000000000),(60883867761/100000000000000),(-126563307/20000000000000)⟩
def e210 : ℝ := (330772027/100000000000000)
theorem h210 : Model (fun x => f210 ((109/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(22109106506669459/100000000000000),(21215165309727/20000000000000),(9659625259/6250000000000),(-181564849/20000000000000)⟩
def e211 : ℝ := (503340567/100000000000000)
theorem h211 : Model (fun x => f211 ((109/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(22091487459050411/100000000000000),(21215165309727/20000000000000),(9659625259/6250000000000),(-181564849/20000000000000)⟩
def e212 : ℝ := (62917571/12500000000000)
theorem h212 : Model (fun x => f212 ((109/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(24193562042865737/100000000000000),(74209937812099/50000000000000),(154268223311/50000000000000),(-56085659/5000000000000)⟩
def e213 : ℝ := (353395411/50000000000000)
theorem h213 : Model (fun x => f213 ((109/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(2419689537619907/10000000000000),(74209937812099/50000000000000),(154268223311/50000000000000),(-56085659/5000000000000)⟩
def e214 : ℝ := (706790823/100000000000000)
theorem h214 : Model (fun x => f214 ((109/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(2302410775726597/100000000000000),(2472341551251/5000000000000),(57241526899/25000000000000),(-65836493/100000000000000)⟩
def e215 : ℝ := (238775059/100000000000000)
theorem h215 : Model (fun x => f215 ((109/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(119936041837583/100000000000000),(63951051601/20000000000000),(58646649/100000000000000),(-2965413/100000000000000)⟩
def e216 : ℝ := (94121/6250000000000)
theorem h216 : Model (fun x => f216 ((109/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(104757657418297/50000000000000),(5839461969/4000000000000),(-17631561/25000000000000),(-1259867/100000000000000)⟩
def e217 : ℝ := (342487/50000000000000)
theorem h217 : Model (fun x => f217 ((109/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(438966671510771/100000000000000),(122345671291/20000000000000),(-82405839/100000000000000),(-5485147/100000000000000)⟩
def e218 : ℝ := (718971/25000000000000)
theorem h218 : Model (fun x => f218 ((109/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(919702403843509/100000000000000),(1922496887957/100000000000000),(410801559/100000000000000),(-351487/2000000000000)⟩
def e219 : ℝ := (226407/2500000000000)
theorem h219 : Model (fun x => f219 ((109/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1926917386972451/100000000000000),(5370567210037/100000000000000),(3018647483/100000000000000),(-12291033/25000000000000)⟩
def e220 : ℝ := (25350591/100000000000000)
theorem h220 : Model (fun x => f220 ((109/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2311068443414939/100000000000000),(6301332699101/50000000000000),(21923189823/100000000000000),(-103304631/100000000000000)⟩
def e221 : ℝ := (29949727/50000000000000)
theorem h221 : Model (fun x => f221 ((109/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(54757657418297/6250000000000),(5839461969/500000000000),(-17631561/3125000000000),(-1259867/12500000000000)⟩
def e222 : ℝ := (342487/6250000000000)
theorem h222 : Model (fun x => f222 ((109/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(199211712106067/20000000000000),(297529530361/20000000000000),(-505563303/100000000000000),(-13044349/100000000000000)⟩
def e223 : ℝ := (3411/48828125000)
theorem h223 : Model (fun x => f223 ((109/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(219211712106067/20000000000000),(297529530361/20000000000000),(-505563303/100000000000000),(-13044349/100000000000000)⟩
def e224 : ℝ := (3411/48828125000)
theorem h224 : Model (fun x => f224 ((109/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(126653317568823/500000000000),(21564143547757/12500000000000),(4160903407/1000000000000),(-585658859/50000000000000)⟩
def e225 : ℝ := (164609063/20000000000000)
theorem h225 : Model (fun x => f225 ((109/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(24673652929/6250000000000),(-2688617799/100000000000000),(9239/78125000000),(-18121/100000000000000)⟩
def e226 : ℝ := (13203/100000000000000)
theorem h226 : Model (fun x => f226 ((109/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (25157732280678811/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(4544710750421/50000000000000),(133302405621/100000000000000),(-153246201/100000000000000),(-985609/100000000000000)⟩
def e227 : ℝ := (639783/50000000000000)
theorem h227 : Model (fun x => f227 ((109/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(9544189466041/50000000000000),(36830101517/12500000000000),(-2020771/2000000000000),(-472747/20000000000000)⟩
def e228 : ℝ := (875059/50000000000000)
theorem h228 : Model (fun x => f228 ((109/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(10489906137553/50000000000000),(25665742073/10000000000000),(-60760251/10000000000000),(1908379/100000000000000)⟩
def e229 : ℝ := (13678241/100000000000000)
theorem h229 : Model (fun x => f229 ((109/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7699013678937/100000000000000),(2944132053/12500000000000),(-87811297/20000000000000),(4728363/100000000000000)⟩
def e230 : ℝ := (5219893/100000000000000)
theorem h230 : Model (fun x => f230 ((109/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-3306801024091/2000000000000),(-192793291557/50000000000000),(8737737667/100000000000000),(-99457907/100000000000000)⟩
def e231 : ℝ := (7418413/50000000000000)
theorem h231 : Model (fun x => f231 ((109/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((109/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-11881/320),(-109/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((109/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2289/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((109/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6431/320),(-5/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((109/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((109/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14751/320),(-5/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((109/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((109/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(368775/32),(-625/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((109/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14279/1600),(11/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((109/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23879/1600),(11/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((109/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((109/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4513131/1600),(2079/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((109/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(35452106309/100000000000000),(-16331219/50000000000000),(378687/25000000000000),(-691/25000000000000)⟩
def e244 : ℝ := (69/100000000000000)
theorem h244 : Model (fun x => f244 ((109/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (281799/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(408557828253171/100000000000000),(-440314245779/25000000000000),(-8964794267/100000000000000),(-13101051/20000000000000)⟩
def e245 : ℝ := (187551/10000000000000)
theorem h245 : Model (fun x => f245 ((109/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(981/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((109/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(90361/1600),(469/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((109/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(123961/1600),(469/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((109/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(35721/1600),(189/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((109/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(4428010881/2560000),(20090889/640000),(257123/1280000),(329/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((109/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((109/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(199809/160),(1341/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((109/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(80076473031/100000000000000),(-268712997/25000000000000),(10820657/100000000000000),(-9683/10000000000000)⟩
def e253 : ℝ := (13/1562500000000)
theorem h253 : Model (fun x => f253 ((109/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (98559/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(69253807401049/50000000000000),(654599150929/100000000000000),(1060181623/100000000000000),(-319117/12500000000000)⟩
def e254 : ℝ := (2929639/100000000000000)
theorem h254 : Model (fun x => f254 ((109/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(119253807401049/50000000000000),(654599150929/100000000000000),(1060181623/100000000000000),(-319117/12500000000000)⟩
def e255 : ℝ := (2929639/100000000000000)
theorem h255 : Model (fun x => f255 ((109/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(119253807401049/100000000000000),(40912446933/12500000000000),(530090811/100000000000000),(-319117/25000000000000)⟩
def e256 : ℝ := (1464821/100000000000000)
theorem h256 : Model (fun x => f256 ((109/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(19253807401049/100000000000000),(40912446933/12500000000000),(530090811/100000000000000),(-319117/25000000000000)⟩
def e257 : ℝ := (1464821/100000000000000)
theorem h257 : Model (fun x => f257 ((109/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(110025834209301/25000000000000),(603945645201/50000000000000),(489071879/25000000000000),(-188431/4000000000000)⟩
def e258 : ℝ := (540589/10000000000000)
theorem h258 : Model (fun x => f258 ((109/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2795817622551489/100000000000000),(603945645201/50000000000000),(489071879/25000000000000),(-188431/4000000000000)⟩
def e259 : ℝ := (5405891/100000000000000)
theorem h259 : Model (fun x => f259 ((109/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3334118962882139/100000000000000),(2647788890607/25000000000000),(21106742721/100000000000000),(-5699931/20000000000000)⟩
def e260 : ℝ := (47456419/100000000000000)
theorem h260 : Model (fun x => f260 ((109/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8616499915263091/100000000000000),(2647788890607/25000000000000),(21106742721/100000000000000),(-5699931/20000000000000)⟩
def e261 : ℝ := (2372821/5000000000000)
theorem h261 : Model (fun x => f261 ((109/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2568876053414849/25000000000000),(1633284955939/4000000000000),(52755337893/50000000000000),(-18748767/100000000000000)⟩
def e262 : ℝ := (183237927/100000000000000)
theorem h262 : Model (fun x => f262 ((109/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(3108910366541403/20000000000000),(1633284955939/4000000000000),(52755337893/50000000000000),(-18748767/100000000000000)⟩
def e263 : ℝ := (22904741/12500000000000)
theorem h263 : Model (fun x => f263 ((109/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(1158591868995791/6250000000000),(24892778636969/25000000000000),(170934553569/50000000000000),(170501741/50000000000000)⟩
def e264 : ℝ := (223721581/50000000000000)
theorem h264 : Model (fun x => f264 ((109/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(20873184189646941/100000000000000),(24892778636969/25000000000000),(170934553569/50000000000000),(170501741/50000000000000)⟩
def e265 : ℝ := (447443163/100000000000000)
theorem h265 : Model (fun x => f265 ((109/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(24892066871987773/100000000000000),(37412037681707/20000000000000),(422117296571/50000000000000),(1786973583/100000000000000)⟩
def e266 : ℝ := (843938097/100000000000000)
theorem h266 : Model (fun x => f266 ((109/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(1011777912974749/4000000000000),(37412037681707/20000000000000),(422117296571/50000000000000),(1786973583/100000000000000)⟩
def e267 : ℝ := (421969049/50000000000000)
theorem h267 : Model (fun x => f267 ((109/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(7541148022907877/25000000000000),(2446920137231/800000000000),(438278160463/25000000000000),(5562923611/100000000000000)⟩
def e268 : ℝ := (695201711/50000000000000)
theorem h268 : Model (fun x => f268 ((109/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(1507348652200623/5000000000000),(2446920137231/800000000000),(438278160463/25000000000000),(5562923611/100000000000000)⟩
def e269 : ℝ := (1390403423/100000000000000)
theorem h269 : Model (fun x => f269 ((109/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(17975706585576389/50000000000000),(231713296626083/50000000000000),(406444351247/12500000000000),(13608474329/100000000000000)⟩
def e270 : ℝ := (213237597/10000000000000)
theorem h270 : Model (fun x => f270 ((109/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(35954746504486111/100000000000000),(231713296626083/50000000000000),(406444351247/12500000000000),(13608474329/100000000000000)⟩
def e271 : ℝ := (2132375971/100000000000000)
theorem h271 : Model (fun x => f271 ((109/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(6922657643509153/100000000000000),(41381399275671/20000000000000),(583358545073/25000000000000),(15260105479/100000000000000)⟩
def e272 : ℝ := (503477523/50000000000000)
theorem h272 : Model (fun x => f272 ((109/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(8888419112279/6250000000000),(97579301337/12500000000000),(233555707/10000000000000),(53187/12500000000000)⟩
def e273 : ℝ := (877219/25000000000000)
theorem h273 : Model (fun x => f273 ((109/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(219253807401049/100000000000000),(40912446933/12500000000000),(530090811/100000000000000),(-319117/25000000000000)⟩
def e274 : ℝ := (1464821/100000000000000)
theorem h274 : Model (fun x => f274 ((109/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(240361160299281/50000000000000),(179404195203/12500000000000),(848934673/25000000000000),(-26593/1250000000000)⟩
def e275 : ℝ := (3219259/50000000000000)
theorem h275 : Model (fun x => f275 ((109/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(65875124433689/6250000000000),(2360103171719/50000000000000),(14691064573/100000000000000),(7921519/100000000000000)⟩
def e276 : ℝ := (10603969/50000000000000)
theorem h276 : Model (fun x => f276 ((109/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(2310939495216669/100000000000000),(13798976166899/100000000000000),(6655887681/12500000000000),(15403881/20000000000000)⟩
def e277 : ℝ := (31060519/50000000000000)
theorem h277 : Model (fun x => f277 ((109/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(821623951064169/25000000000000),(7532832453741/20000000000000),(47483615143/20000000000000),(171462807/20000000000000)⟩
def e278 : ℝ := (172311303/100000000000000)
theorem h278 : Model (fun x => f278 ((109/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(119253807401049/12500000000000),(40912446933/1562500000000),(530090811/12500000000000),(-319117/3125000000000)⟩
def e279 : ℝ := (1464821/12500000000000)
theorem h279 : Model (fun x => f279 ((109/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(137030645625607/12500000000000),(424878876801/12500000000000),(3288141779/50000000000000),(-1223281/12500000000000)⟩
def e280 : ℝ := (3806861/25000000000000)
theorem h280 : Model (fun x => f280 ((109/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(149530645625607/12500000000000),(424878876801/12500000000000),(3288141779/50000000000000),(-1223281/12500000000000)⟩
def e281 : ℝ := (3806861/25000000000000)
theorem h281 : Model (fun x => f281 ((109/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(39314547156507943/100000000000000),(140566182938217/25000000000000),(1084112022907/25000000000000),(51201923/250000000000)⟩
def e282 : ℝ := (130722789/5000000000000)
theorem h282 : Model (fun x => f282 ((109/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(15897423351/6250000000000),(-3637762049/100000000000000),(479401/2000000000000),(-7407/10000000000000)⟩
def e283 : ℝ := (17731/100000000000000)
theorem h283 : Model (fun x => f283 ((109/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (38747922881438467/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1100524192729/6250000000000),(10978251439/4000000000000),(67874871/100000000000000),(-400317/25000000000000)⟩
def e284 : ℝ := (4013711/100000000000000)
theorem h284 : Model (fun x => f284 ((109/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(69253807401049/25000000000000),(654599150929/50000000000000),(1060181623/50000000000000),(-319117/6250000000000)⟩
def e285 : ℝ := (2929639/50000000000000)
theorem h285 : Model (fun x => f285 ((109/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(163778837973/390625000000),(-57536169279/50000000000000),(12945337/10000000000000),(9453/1562500000000)⟩
def e286 : ℝ := (521323/100000000000000)
theorem h286 : Model (fun x => f286 ((109/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (237851949986971/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(116145234957821/100000000000000),(28768084639/12500000000000),(-32363343/12500000000000),(-1209989/100000000000000)⟩
def e287 : ℝ := (1965461/50000000000000)
theorem h287 : Model (fun x => f287 ((109/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(16145234957821/100000000000000),(28768084639/12500000000000),(-32363343/12500000000000),(-1209989/100000000000000)⟩
def e288 : ℝ := (1965461/50000000000000)
theorem h288 : Model (fun x => f288 ((109/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(428631224249101/100000000000000),(424671725623/50000000000000),(-38219567/4000000000000),(-1116359/25000000000000)⟩
def e289 : ℝ := (14506977/100000000000000)
theorem h289 : Model (fun x => f289 ((109/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1392172754981693/50000000000000),(424671725623/50000000000000),(-38219567/4000000000000),(-1116359/25000000000000)⟩
def e290 : ℝ := (7253489/50000000000000)
theorem h290 : Model (fun x => f290 ((109/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3233884634584513/100000000000000),(1848623732659/25000000000000),(-3181947353/50000000000000),(-43274681/100000000000000)⟩
def e291 : ℝ := (12638457/10000000000000)
theorem h291 : Model (fun x => f291 ((109/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1703253117393093/20000000000000),(1848623732659/25000000000000),(-3181947353/50000000000000),(-43274681/100000000000000)⟩
def e292 : ℝ := (126384571/100000000000000)
theorem h292 : Model (fun x => f292 ((109/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9891236675613093/100000000000000),(28188085448253/100000000000000),(-12422509919/100000000000000),(-730853/390625000000)⟩
def e293 : ℝ := (482312321/100000000000000)
theorem h293 : Model (fun x => f293 ((109/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1895035536832589/12500000000000),(28188085448253/100000000000000),(-12422509919/100000000000000),(-730853/390625000000)⟩
def e294 : ℝ := (241156161/50000000000000)
theorem h294 : Model (fun x => f294 ((109/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(440198695357683/2500000000000),(8453713176649/12500000000000),(11194226457/100000000000000),(-125578553/25000000000000)⟩
def e295 : ℝ := (579540857/50000000000000)
theorem h295 : Model (fun x => f295 ((109/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3988732420004321/20000000000000),(8453713176649/12500000000000),(11194226457/100000000000000),(-125578553/25000000000000)⟩
def e296 : ℝ := (231816343/20000000000000)
theorem h296 : Model (fun x => f296 ((109/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(2316361320526399/10000000000000),(124447956997837/100000000000000),(117012241597/100000000000000),(-243516273/25000000000000)⟩
def e297 : ℝ := (2137522057/100000000000000)
theorem h297 : Model (fun x => f297 ((109/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(11782997078822471/50000000000000),(124447956997837/100000000000000),(117012241597/100000000000000),(-243516273/25000000000000)⟩
def e298 : ℝ := (1068761029/50000000000000)
theorem h298 : Model (fun x => f298 ((109/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(27370779284543087/100000000000000),(19877625321769/10000000000000),(90325135893/25000000000000),(-293876567/20000000000000)⟩
def e299 : ℝ := (855716033/25000000000000)
theorem h299 : Model (fun x => f299 ((109/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(27353160236924039/100000000000000),(19877625321769/10000000000000),(90325135893/25000000000000),(-293876567/20000000000000)⟩
def e300 : ℝ := (3422864133/100000000000000)
theorem h300 : Model (fun x => f300 ((109/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(7942348056391173/25000000000000),(73455247161809/25000000000000),(201571788707/25000000000000),(-430179883/25000000000000)⟩
def e301 : ℝ := (634145307/12500000000000)
theorem h301 : Model (fun x => f301 ((109/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(1270909022355921/4000000000000),(73455247161809/25000000000000),(201571788707/25000000000000),(-430179883/25000000000000)⟩
def e302 : ℝ := (5073162457/100000000000000)
theorem h302 : Model (fun x => f302 ((109/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(5129781193987731/100000000000000),(7535082851231/6250000000000),(362064295983/50000000000000),(216321959/50000000000000)⟩
def e303 : ℝ := (420182781/20000000000000)
theorem h303 : Model (fun x => f303 ((109/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(67448578017037/50000000000000),(534604151949/100000000000000),(-71749969/100000000000000),(-400241/10000000000000)⟩
def e304 : ℝ := (9154179/100000000000000)
theorem h304 : Model (fun x => f304 ((109/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(216145234957821/100000000000000),(28768084639/12500000000000),(-32363343/12500000000000),(-1209989/100000000000000)⟩
def e305 : ℝ := (1965461/50000000000000)
theorem h305 : Model (fun x => f305 ((109/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(116796906487429/25000000000000),(994893506173/100000000000000),(-589563457/100000000000000),(-1605597/25000000000000)⟩
def e306 : ℝ := (17016023/100000000000000)
theorem h306 : Model (fun x => f306 ((109/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(1009803791802879/100000000000000),(1612811179873/50000000000000),(-194199143/100000000000000),(-234673/1000000000000)⟩
def e307 : ℝ := (55247761/100000000000000)
theorem h307 : Model (fun x => f307 ((109/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1091321389202659/50000000000000),(4648019352217/50000000000000),(1097348963/25000000000000),(-71740259/100000000000000)⟩
def e308 : ℝ := (31891341/20000000000000)
theorem h308 : Model (fun x => f308 ((109/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2944323034451869/100000000000000),(12104295375839/50000000000000),(10810426707/20000000000000),(-33467579/20000000000000)⟩
def e309 : ℝ := (10434211/2500000000000)
theorem h309 : Model (fun x => f309 ((109/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(116145234957821/12500000000000),(28768084639/1562500000000),(-32363343/1562500000000),(-1209989/12500000000000)⟩
def e310 : ℝ := (1965461/6250000000000)
theorem h310 : Model (fun x => f310 ((109/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(532029517848321/50000000000000),(475152313769/20000000000000),(-2143003921/100000000000000),(-6841161/50000000000000)⟩
def e311 : ℝ := (8120311/20000000000000)
theorem h311 : Model (fun x => f311 ((109/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(582029517848321/50000000000000),(475152313769/20000000000000),(-2143003921/100000000000000),(-6841161/50000000000000)⟩
def e312 : ℝ := (8120311/20000000000000)
theorem h312 : Model (fun x => f312 ((109/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(17136829161317267/50000000000000),(351752383174887/100000000000000),(1141240181763/100000000000000),(-1585404879/100000000000000)⟩
def e313 : ℝ := (6082081923/100000000000000)
theorem h313 : Model (fun x => f313 ((109/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(5835385243/2000000000000),(-1497221749/50000000000000),(4203367/20000000000000),(-25623/25000000000000)⟩
def e314 : ℝ := (26539/50000000000000)
theorem h314 : Model (fun x => f314 ((109/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (16960378515895541/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(14967124739607/100000000000000),(198152490773/100000000000000),(-419238477/100000000000000),(-340741/100000000000000)⟩
def e315 : ℝ := (449833/5000000000000)
theorem h315 : Model (fun x => f315 ((109/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(32575511823271/100000000000000),(118152194187/25000000000000),(-175681803/50000000000000),(-1942009/100000000000000)⟩
def e316 : ℝ := (13010371/100000000000000)
theorem h316 : Model (fun x => f316 ((109/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(13308980364751/10000000000000),(678570838821/50000000000000),(-6339853109/50000000000000),(-65452891/100000000000000)⟩
def e317 : ℝ := (54249327/100000000000000)
theorem h317 : Model (fun x => f317 ((109/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(48840294916517/100000000000000),(49957543019/100000000000000),(-5111429283/100000000000000),(5718609/25000000000000)⟩
def e318 : ℝ := (10501293/50000000000000)
theorem h318 : Model (fun x => f318 ((109/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-116499756288033/100000000000000),(-67125808019/20000000000000),(113322137/3125000000000),(-76583471/100000000000000)⟩
def e319 : ℝ := (8959853/25000000000000)
theorem h319 : Model (fun x => f319 ((109/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((109/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-130691/1600),(-1199/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((109/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((109/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(10573/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((109/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(292229/1600),(741/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((109/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((109/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(465029/1600),(741/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((109/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2325145/32),(3705/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((109/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((109/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(546227537570400021/50000000000000),(503245773547837/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (141173/100000000000000)
theorem h329 : Model (fun x => f329 ((109/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(1144211811/12500000000000),(-4216703/50000000000000),(195553/50000000000000),(-357/50000000000000)⟩
def e330 : ℝ := (1/5000000000000)
theorem h330 : Model (fun x => f330 ((109/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (545701416988893059/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(332557296410949/50000000000000),(1506874511319/100000000000000),(10732294533/100000000000000),(53180601/100000000000000)⟩
def e331 : ℝ := (114833/5000000000000)
theorem h331 : Model (fun x => f331 ((109/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((109/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(469/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((109/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((109/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((109/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(795806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((109/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((109/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((109/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(441323703402583/12500000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (109/10000000000000)
theorem h339 : Model (fun x => f339 ((109/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3894193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((109/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((109/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((109/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2194410372779077/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1089/100000000000000)
theorem h343 : Model (fun x => f343 ((109/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(569629097413/12500000000000),(-585106129/10000000000000),(1502509/20000000000000),(-4823/50000000000000)⟩
def e344 : ℝ := (17/100000000000000)
theorem h344 : Model (fun x => f344 ((109/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2191592831143507/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(10055632913447/6250000000000),(160856987197/20000000000000),(-1032672101/100000000000000),(662953/50000000000000)⟩
def e345 : ℝ := (699/25000000000000)
theorem h345 : Model (fun x => f345 ((109/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(16305632913447/6250000000000),(160856987197/20000000000000),(-1032672101/100000000000000),(662953/50000000000000)⟩
def e346 : ℝ := (699/25000000000000)
theorem h346 : Model (fun x => f346 ((109/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(16305632913447/12500000000000),(50267808499/12500000000000),(-516336051/100000000000000),(662953/100000000000000)⟩
def e347 : ℝ := (1399/100000000000000)
theorem h347 : Model (fun x => f347 ((109/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(3805632913447/12500000000000),(50267808499/12500000000000),(-516336051/100000000000000),(662953/100000000000000)⟩
def e348 : ℝ := (1399/100000000000000)
theorem h348 : Model (fun x => f348 ((109/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(60175550037721/12500000000000),(1484097203303/100000000000000),(-1905525903/100000000000000),(611653/25000000000000)⟩
def e349 : ℝ := (2583/50000000000000)
theorem h349 : Model (fun x => f349 ((109/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2837118686016053/100000000000000),(1484097203303/100000000000000),(-1905525903/100000000000000),(611653/25000000000000)⟩
def e350 : ℝ := (5167/100000000000000)
theorem h350 : Model (fun x => f350 ((109/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(925220316521177/25000000000000),(13345190640201/100000000000000),(-697909121/6250000000000),(667439/10000000000000)⟩
def e351 : ℝ := (38009/50000000000000)
theorem h351 : Model (fun x => f351 ((109/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(449163110923283/5000000000000),(13345190640201/100000000000000),(-697909121/6250000000000),(667439/10000000000000)⟩
def e352 : ℝ := (76019/100000000000000)
theorem h352 : Model (fun x => f352 ((109/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5859111043981543/50000000000000),(53533654770657/100000000000000),(-7283350307/100000000000000),(-11387559/25000000000000)⟩
def e353 : ℝ := (398413/100000000000000)
theorem h353 : Model (fun x => f353 ((109/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3397453941402141/20000000000000),(53533654770657/100000000000000),(-7283350307/100000000000000),(-11387559/25000000000000)⟩
def e354 : ℝ := (199207/50000000000000)
theorem h354 : Model (fun x => f354 ((109/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(11079527361769397/50000000000000),(1079258089849/781250000000),(29517348001/25000000000000),(-1972683/781250000000)⟩
def e355 : ℝ := (969239/100000000000000)
theorem h355 : Model (fun x => f355 ((109/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(24494769009253079/100000000000000),(1079258089849/781250000000),(29517348001/25000000000000),(-1972683/781250000000)⟩
def e356 : ℝ := (24231/2500000000000)
theorem h356 : Model (fun x => f356 ((109/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(6390443388232937/20000000000000),(139353623818937/50000000000000),(583080225313/100000000000000),(-4054749/1000000000000)⟩
def e357 : ℝ := (2324157/100000000000000)
theorem h357 : Model (fun x => f357 ((109/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(32354597893545637/100000000000000),(139353623818937/50000000000000),(583080225313/100000000000000),(-4054749/1000000000000)⟩
def e358 : ℝ := (1162079/50000000000000)
theorem h358 : Model (fun x => f358 ((109/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(42204975705147257/100000000000000),(493671424102019/100000000000000),(857170560043/50000000000000),(591320999/100000000000000)⟩
def e359 : ℝ := (3148581/50000000000000)
theorem h359 : Model (fun x => f359 ((109/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(42187356657528209/100000000000000),(493671424102019/100000000000000),(857170560043/50000000000000),(591320999/100000000000000)⟩
def e360 : ℝ := (6297163/100000000000000)
theorem h360 : Model (fun x => f360 ((109/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(1100626481994111/2000000000000),(813623278944461/100000000000000),(31278963099/781250000000),(337257597/6250000000000)⟩
def e361 : ℝ := (12046143/100000000000000)
theorem h361 : Model (fun x => f361 ((109/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(55034657433038883/100000000000000),(813623278944461/100000000000000),(31278963099/781250000000),(337257597/6250000000000)⟩
def e362 : ℝ := (188221/1562500000000)
theorem h362 : Model (fun x => f362 ((109/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(4188834074149067/25000000000000),(234512926005991/50000000000000),(2103346086133/50000000000000),(347682087/2500000000000)⟩
def e363 : ℝ := (682509/6250000000000)
theorem h363 : Model (fun x => f363 ((109/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(6806365816527/4000000000000),(1049149993917/100000000000000),(67528967/25000000000000),(-484647/20000000000000)⟩
def e364 : ℝ := (11669/100000000000000)
theorem h364 : Model (fun x => f364 ((109/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(28805632913447/12500000000000),(50267808499/12500000000000),(-516336051/100000000000000),(662953/100000000000000)⟩
def e365 : ℝ := (1399/100000000000000)
theorem h365 : Model (fun x => f365 ((109/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(531049272028327/100000000000000),(1853434929901/100000000000000),(-381278117/50000000000000),(-1097329/100000000000000)⟩
def e366 : ℝ := (14467/100000000000000)
theorem h366 : Model (fun x => f366 ((109/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1223776831120099/100000000000000),(6406723946363/100000000000000),(2954176933/100000000000000),(-11644649/100000000000000)⟩
def e367 : ℝ := (52667/100000000000000)
theorem h367 : Model (fun x => f367 ((109/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2820133293218159/100000000000000),(9842652702759/50000000000000),(5250622347/20000000000000),(-39921679/100000000000000)⟩
def e368 : ℝ := (158481/100000000000000)
theorem h368 : Model (fun x => f368 ((109/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(149959834726639/3125000000000),(15770943931063/25000000000000),(1617612991/625000000000),(24042351/12500000000000)⟩
def e369 : ℝ := (178551/12500000000000)
theorem h369 : Model (fun x => f369 ((109/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(16305632913447/1562500000000),(50267808499/1562500000000),(-516336051/12500000000000),(662953/12500000000000)⟩
def e370 : ℝ := (1399/12500000000000)
theorem h370 : Model (fun x => f370 ((109/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1213719651873783/100000000000000),(4266289737853/100000000000000),(-193028627/5000000000000),(2880389/100000000000000)⟩
def e371 : ℝ := (22861/100000000000000)
theorem h371 : Model (fun x => f371 ((109/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1313719651873783/100000000000000),(4266289737853/100000000000000),(-193028627/5000000000000),(2880389/100000000000000)⟩
def e372 : ℝ := (22861/100000000000000)
theorem h372 : Model (fun x => f372 ((109/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(6304165819908167/10000000000000),(516735516054243/50000000000000),(5906222748203/100000000000000),(2817887143/25000000000000)⟩
def e373 : ℝ := (9984377/50000000000000)
theorem h373 : Model (fun x => f373 ((109/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(79312634579/50000000000000),(-2600417333/100000000000000),(27768619/100000000000000),(-239959/100000000000000)⟩
def e374 : ℝ := (1899/100000000000000)
theorem h374 : Model (fun x => f374 ((109/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (12400453930541531/20000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(26578197298803/100000000000000),(61656970183/20000000000000),(-871027273/100000000000000),(2704977/100000000000000)⟩
def e375 : ℝ := (335013/50000000000000)
theorem h375 : Model (fun x => f375 ((109/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(10055632913447/3125000000000),(160856987197/10000000000000),(-1032672101/50000000000000),(662953/25000000000000)⟩
def e376 : ℝ := (699/12500000000000)
theorem h376 : Model (fun x => f376 ((109/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(7666062437657/20000000000000),(-11816657489/10000000000000),(516011249/100000000000000),(-563331/25000000000000)⟩
def e377 : ℝ := (5023/50000000000000)
theorem h377 : Model (fun x => f377 ((109/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (65021201919591/25000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(123339375623429/100000000000000),(118166574889/50000000000000),(-412809/40000000000),(1126661/25000000000000)⟩
def e378 : ℝ := (42369/50000000000000)
theorem h378 : Model (fun x => f378 ((109/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(23339375623429/100000000000000),(118166574889/50000000000000),(-412809/40000000000),(1126661/25000000000000)⟩
def e379 : ℝ := (42369/50000000000000)
theorem h379 : Model (fun x => f379 ((109/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(1778050894869/390625000000),(34887274491/4000000000000),(-761730893/20000000000000),(8315831/50000000000000)⟩
def e380 : ℝ := (156363/50000000000000)
theorem h380 : Model (fun x => f380 ((109/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2810895314800749/100000000000000),(34887274491/4000000000000),(-761730893/20000000000000),(8315831/50000000000000)⟩
def e381 : ℝ := (312727/100000000000000)
theorem h381 : Model (fun x => f381 ((109/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1733470365351731/50000000000000),(7718821097661/100000000000000),(-31645387871/100000000000000),(64594103/50000000000000)⟩
def e382 : ℝ := (2887363/100000000000000)
theorem h382 : Model (fun x => f382 ((109/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4374660841542207/50000000000000),(7718821097661/100000000000000),(-31645387871/100000000000000),(64594103/50000000000000)⟩
def e383 : ℝ := (721841/25000000000000)
theorem h383 : Model (fun x => f383 ((109/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2158271747040321/20000000000000),(30197893265187/100000000000000),(-22216811831/20000000000000),(199596097/50000000000000)⟩
def e384 : ℝ := (1496401/12500000000000)
theorem h384 : Model (fun x => f384 ((109/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(2007550794281153/12500000000000),(30197893265187/100000000000000),(-22216811831/20000000000000),(199596097/50000000000000)⟩
def e385 : ℝ := (11971209/100000000000000)
theorem h385 : Model (fun x => f385 ((109/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(19808804919916509/100000000000000),(37600978604427/50000000000000),(-231389759827/100000000000000),(64196899/10000000000000)⟩
def e386 : ℝ := (1275539/4000000000000)
theorem h386 : Model (fun x => f386 ((109/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(11072259602815397/50000000000000),(37600978604427/50000000000000),(-231389759827/100000000000000),(64196899/10000000000000)⟩
def e387 : ℝ := (7972119/25000000000000)
theorem h387 : Model (fun x => f387 ((109/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(1365645586151767/5000000000000),(7254423210993/5000000000000),(-16810197579/5000000000000),(466823363/100000000000000)⟩
def e388 : ℝ := (32773417/50000000000000)
theorem h388 : Model (fun x => f388 ((109/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(6928823168854073/25000000000000),(7254423210993/5000000000000),(-16810197579/5000000000000),(466823363/100000000000000)⟩
def e389 : ℝ := (13109367/20000000000000)
theorem h389 : Model (fun x => f389 ((109/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(6836773787612881/20000000000000),(611129075051/250000000000),(-89451943399/25000000000000),(-467100389/100000000000000)⟩
def e390 : ℝ := (3616901/3125000000000)
theorem h390 : Model (fun x => f390 ((109/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(34166249890445357/100000000000000),(611129075051/250000000000),(-89451943399/25000000000000),(-467100389/100000000000000)⟩
def e391 : ℝ := (115740833/100000000000000)
theorem h391 : Model (fun x => f391 ((109/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(21070219644407899/50000000000000),(23890705543473/6250000000000),(-216201023251/100000000000000),(-1202390829/50000000000000)⟩
def e392 : ℝ := (92902317/50000000000000)
theorem h392 : Model (fun x => f392 ((109/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(42143772622149131/100000000000000),(23890705543473/6250000000000),(-216201023251/100000000000000),(-1202390829/50000000000000)⟩
def e393 : ℝ := (37160927/20000000000000)
theorem h393 : Model (fun x => f393 ((109/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(4918046697083609/50000000000000),(9440738468363/5000000000000),(417993325913/100000000000000),(-1558932609/50000000000000)⟩
def e394 : ℝ := (9363241/10000000000000)
theorem h394 : Model (fun x => f394 ((109/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(152126015791773/100000000000000),(291491831327/50000000000000),(-1987246639/100000000000000),(623891/10000000000000)⟩
def e395 : ℝ := (6037/2500000000000)
theorem h395 : Model (fun x => f395 ((109/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(223339375623429/100000000000000),(118166574889/50000000000000),(-412809/40000000000),(1126661/25000000000000)⟩
def e396 : ℝ := (42369/50000000000000)
theorem h396 : Model (fun x => f396 ((109/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(498804767038631/100000000000000),(105564996221/10000000000000),(-4051291639/100000000000000),(7626099/50000000000000)⟩
def e397 : ℝ := (102739/25000000000000)
theorem h397 : Model (fun x => f397 ((109/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(557013726141989/50000000000000),(3536523051553/100000000000000),(-1462632009/12500000000000),(9018607/25000000000000)⟩
def e398 : ℝ := (1468151/100000000000000)
theorem h398 : Model (fun x => f398 ((109/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2488061956204629/100000000000000),(10531264669491/100000000000000),(-1829506451/6250000000000),(13324493/20000000000000)⟩
def e399 : ℝ := (4595751/100000000000000)
theorem h399 : Model (fun x => f399 ((109/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(75699790488099/2000000000000),(6105157615113/20000000000000),(-8144714867/25000000000000),(-24671147/20000000000000)⟩
def e400 : ℝ := (1468219/10000000000000)
theorem h400 : Model (fun x => f400 ((109/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(123339375623429/12500000000000),(118166574889/6250000000000),(-412809/5000000000),(1126661/3125000000000)⟩
def e401 : ℝ := (42369/6250000000000)
theorem h401 : Model (fun x => f401 ((109/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(227768204155841/20000000000000),(1236824430439/50000000000000),(-10243426639/100000000000000),(21146031/50000000000000)⟩
def e402 : ℝ := (114923/12500000000000)
theorem h402 : Model (fun x => f402 ((109/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(247768204155841/20000000000000),(1236824430439/50000000000000),(-10243426639/100000000000000),(21146031/50000000000000)⟩
def e403 : ℝ := (114923/12500000000000)
theorem h403 : Model (fun x => f403 ((109/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(46890002860524259/100000000000000),(23589666742551/5000000000000),(-36212091413/100000000000000),(-241262789/6250000000000)⟩
def e404 : ℝ := (57632553/25000000000000)
theorem h404 : Model (fun x => f404 ((109/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(106632537747/50000000000000),(-2145810089/100000000000000),(10877603/50000000000000),(-40599/20000000000000)⟩
def e405 : ℝ := (93/3125000000000)
theorem h405 : Model (fun x => f405 ((109/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (4641816922284699/10000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(20976952002731/100000000000000),(191612076019/100000000000000),(-1020310209/100000000000000),(5491603/100000000000000)⟩
def e406 : ℝ := (14541/2000000000000)
theorem h406 : Model (fun x => f406 ((109/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(23777574650767/50000000000000),(249948463467/50000000000000),(-945668741/50000000000000),(409829/5000000000000)⟩
def e407 : ℝ := (349269/25000000000000)
theorem h407 : Model (fun x => f407 ((109/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(316296237642743/100000000000000),(3233187067/80000000000),(57016471/100000000000000),(26239273/25000000000000)⟩
def e408 : ℝ := (10603573/100000000000000)
theorem h408 : Model (fun x => f408 ((109/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(2321440276277/2000000000000),(418232472807/100000000000000),(-3816071689/100000000000000),(36763097/50000000000000)⟩
def e409 : ℝ := (783481/12500000000000)
theorem h409 : Model (fun x => f409 ((109/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-427742474183/100000000000000),(10325429089/12500000000000),(-37952661/20000000000000),(-3057277/100000000000000)⟩
def e410 : ℝ := (2105363/5000000000000)
theorem h410 : Model (fun x => f410 ((109/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(5134903805908203/25000000000000),(222899278564453/25000000000000),(1580173/10240000),(109/81920)⟩
def e411 : ℝ := (286132813/50000000000000)
theorem h411 : Model (fun x => f411 ((109/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(52441/1600),(229/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((109/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(12008989/64000),(157323/64000),(687/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((109/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(963515676893902263/25000000000000),(43557918198066851/20000000000000),(1061545889218591/20000000000000),(7279145441809/10000000000000)⟩
def e414 : ℝ := (123423603661/20000000000000)
theorem h414 : Model (fun x => f414 ((109/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(129733229/5000000000000),(-29324429/20000000000000),(471217/10000000000000),(-113361/100000000000000)⟩
def e415 : ℝ := (1697/50000000000000)
theorem h415 : Model (fun x => f415 ((109/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (3630891978566745447/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5467292688631/100000000000000),(-1696073377/10000000000000),(-13638951/10000000000000),(3665731/100000000000000)⟩
def e416 : ℝ := (13595723/100000000000000)
theorem h416 : Model (fun x => f416 ((109/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(314971888403/6250000000000),(32821349471/50000000000000),(-65230563/20000000000000),(304227/50000000000000)⟩
def e417 : ℝ := (55702983/100000000000000)
theorem h417 : Model (fun x => f417 ((109/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((109/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((251969289693/100000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (27/10) (11/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (27/10) (11/4) ≤ (2519748599913/1000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(109/40)-(1/40)) (by norm_num : ((109/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel34


noncomputable section
namespace Hf4Quad.Panel35
open Hf4Quad.Dag

def p0 : Cubic := ⟨(111/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((111/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((111/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((111/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((111/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(243142857142857/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((111/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-243142857142857/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((111/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-394857142857143/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((111/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((111/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(12321/1600),(111/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((111/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(932223809523809/100000000000000),(671873015873/4000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((111/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-932223809523809/100000000000000),(-671873015873/4000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((111/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-165885119047619/12500000000000),(-21177777777777/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((111/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((111/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1367631/64000),(36963/64000),(333/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((111/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(266485433/1280000),(7202309/1280000),(5069192708333/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((111/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-266485433/1280000),(-7202309/1280000),(-5069192708333/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((111/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-692070481422061/3125000000000),(-583858168402777/100000000000000),(-2572427041997/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((111/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((111/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(151807041/2560000),(1367631/640000),(36963/1280000),(111/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((111/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(4141561138392857/25000000000000),(119396357142857/20000000000000),(8067321428571/100000000000000),(6056547619/12500000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((111/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1395002712983631/25000000000000),(3280904327877/25000000000000),(2922467344577/100000000000000),(33229580027/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((111/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((111/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(16455646045898437/100000000000000),(185311329345703/25000000000000),(1367631/10240000),(12321/10240000)⟩
def e22 : ℝ := (542968751/100000000000000)
theorem h22 : Model (fun x => f22 ((111/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(21441097329433593/20000000000000),(1207268993774413/25000000000000),(87010377929687/100000000000000),(156775455729/20000000000000)⟩
def e23 : ℝ := (1768670433/50000000000000)
theorem h23 : Model (fun x => f23 ((111/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(101625475795233441/100000000000000),(121054989810229/2500000000000),(11241605659283/12500000000000),(51069178667/6250000000000)⟩
def e24 : ℝ := (3646467859/100000000000000)
theorem h24 : Model (fun x => f24 ((111/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((111/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(22832208888684081/50000000000000),(617086726721191/25000000000000),(5559339880371/10000000000000),(333894287109/50000000000000)⟩
def e26 : ℝ := (2264184573/50000000000000)
theorem h26 : Model (fun x => f26 ((111/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(102539570924418243/100000000000000),(5542679509428009/100000000000000),(62417562043107/50000000000000),(749760505021/50000000000000)⟩
def e27 : ℝ := (101684649/1000000000000)
theorem h27 : Model (fun x => f27 ((111/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(51041261679912921/25000000000000),(10384879101837169/100000000000000),(107383984680239/50000000000000),(1158313934357/50000000000000)⟩
def e28 : ℝ := (13814932759/100000000000000)
theorem h28 : Model (fun x => f28 ((111/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((111/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(126718759332196649/100000000000000),(124863642359991/1562500000000),(107990177176207/50000000000000),(3242948263547/100000000000000)⟩
def e30 : ℝ := (14687073983/50000000000000)
theorem h30 : Model (fun x => f30 ((111/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(30070562730418093/100000000000000),(1896341793810149/100000000000000),(51252480913787/100000000000000),(192389192619/25000000000000)⟩
def e31 : ℝ := (348526597/5000000000000)
theorem h31 : Model (fun x => f31 ((111/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(234235609450069777/100000000000000),(6140610447823659/50000000000000),(53204090054853/20000000000000),(308618463919/10000000000000)⟩
def e32 : ℝ := (20785464699/100000000000000)
theorem h32 : Model (fun x => f32 ((111/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((111/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(5285709/320),(47619/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((111/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((111/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(245199/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((111/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(9208893/320),(65291/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((111/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((111/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(9938493/320),(65291/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((111/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-9938493/320),(-65291/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((111/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((111/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(151/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((111/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(22801/1600),(151/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((111/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((111/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(478821/160),(3171/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((111/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(33415409933/100000000000000),(-110647053/25000000000000),(4396571/100000000000000),(-19411/50000000000000)⟩
def e46 : ℝ := (331/100000000000000)
theorem h46 : Model (fun x => f46 ((111/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (236229/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-51890440267383/5000000000000),(27506864823/25000000000000),(-184724273/25000000000000),(4967137/100000000000000)⟩
def e47 : ℝ := (20415583/100000000000000)
theorem h47 : Model (fun x => f47 ((111/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((111/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(191/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((111/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((111/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((111/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(31833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((111/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(51833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((111/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((111/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(32395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((111/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((111/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(680312499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((111/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((111/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(7395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((111/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(100629557291661/12500000000000),(1392708333331/10000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (137/100000000000000)
theorem h60 : Model (fun x => f60 ((111/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(83959201388887/50000000000000),(1079861111109/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((111/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((111/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(32395833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((111/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(731875868055547/50000000000000),(5246527777769/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((111/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(781875868055547/50000000000000),(5246527777769/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((111/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(6294385796757027/50000000000000),(260021468821897/100000000000000),(1314782443567/100000000000000),(1077293113/50000000000000)⟩
def e66 : ℝ := (39721/6250000000000)
theorem h66 : Model (fun x => f66 ((111/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(57395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((111/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(263542534722219/50000000000000),(1913194444441/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((111/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(75631216995803/6250000000000),(1647140842011/25000000000000),(11957465277/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (69/100000000000000)
theorem h69 : Model (fun x => f69 ((111/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(152336658575945941/100000000000000),(1987968807411403/50000000000000),(17273576321307/50000000000000),(36175133473/25000000000000)⟩
def e70 : ℝ := (32607469/10000000000000)
theorem h70 : Model (fun x => f70 ((111/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((111/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1763143229166627/6250000000000),(22677083333289/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((111/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(8345544618054991/100000000000000),(5350374348949/3125000000000),(842187499991/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (109/6250000000000)
theorem h73 : Model (fun x => f73 ((111/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(50494695676501831/50000000000000),(524337350269387/20000000000000),(11234815915507/50000000000000),(22817609927/25000000000000)⟩
def e74 : ℝ := (7735687/4000000000000)
theorem h74 : Model (fun x => f74 ((111/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(253326049928949603/100000000000000),(6597624366169741/100000000000000),(14254196118407/25000000000000),(294963717/125000000000)⟩
def e75 : ℝ := (103893373/20000000000000)
theorem h75 : Model (fun x => f75 ((111/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((111/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(587714409722209/6250000000000),(7559027777763/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((111/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(875173611111/10000000000000),(246527777777/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((111/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(2589055266203/100000000000000),(27349175347/25000000000000),(1540798611/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((111/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(243460014002347/100000000000000),(148158776239/1250000000000),(213559680817/100000000000000),(1718338047/100000000000000)⟩
def e80 : ℝ := (5879773/100000000000000)
theorem h80 : Model (fun x => f80 ((111/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(111788723096077/20000000000000),(28226245294237/100000000000000),(539683692621/100000000000000),(4834849769/100000000000000)⟩
def e81 : ℝ := (20683233/100000000000000)
theorem h81 : Model (fun x => f81 ((111/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(63471248386107497/25000000000000),(3312925305731989/50000000000000),(57556468166249/100000000000000),(240805823369/100000000000000)⟩
def e82 : ℝ := (270075049/50000000000000)
theorem h82 : Model (fun x => f82 ((111/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(153185769917/20000000000000),(43150921103/100000000000000),(455819589/50000000000000),(1069999/12500000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((111/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(56646821167/25000000000000),(1994606379/12500000000000),(449488761/100000000000000),(6330827/100000000000000)⟩
def e84 : ℝ := (44713/100000000000000)
theorem h84 : Model (fun x => f84 ((111/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(33516035857/50000000000000),(1416170529/25000000000000),(199460637/100000000000000),(3745739/100000000000000)⟩
def e85 : ℝ := (7959/20000000000000)
theorem h85 : Model (fun x => f85 ((111/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(3966064243/20000000000000),(1955102091/100000000000000),(82609947/100000000000000),(303/15625000000)⟩
def e86 : ℝ := (6887/25000000000000)
theorem h86 : Model (fun x => f86 ((111/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(11898192729/20000000000000),(5865306273/100000000000000),(247829841/100000000000000),(909/15625000000)⟩
def e87 : ℝ := (20661/25000000000000)
theorem h87 : Model (fun x => f87 ((111/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-11898192729/20000000000000),(-5865306273/100000000000000),(-247829841/100000000000000),(-909/15625000000)⟩
def e88 : ℝ := (20661/25000000000000)
theorem h88 : Model (fun x => f88 ((111/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(253884934053466343/100000000000000),(1325168949231541/20000000000000),(7194527542051/12500000000000),(240800005769/100000000000000)⟩
def e89 : ℝ := (270116371/50000000000000)
theorem h89 : Model (fun x => f89 ((111/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1763143229166627/5000000000000),(22677083333289/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((111/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(17363666901953/625000000000),(20168324532179/100000000000000),(54904694731/100000000000000),(66430361/100000000000000)⟩
def e91 : ℝ := (1897/6250000000000)
theorem h91 : Model (fun x => f91 ((111/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(39186728616554361/4000000000000),(335301152735557/2500000000000),(37612825727973/50000000000000),(110731715937/50000000000000)⟩
def e92 : ℝ := (36190269/10000000000000)
theorem h92 : Model (fun x => f92 ((111/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(2551884363/25000000000000),(-139745233/100000000000000),(564681/50000000000000),(-7039/100000000000000)⟩
def e93 : ℝ := (49/100000000000000)
theorem h93 : Model (fun x => f93 ((111/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (193236144365529247/20000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(25915399728493/100000000000000),(32154349133/10000000000000),(-64618683/12500000000000),(138311/12500000000000)⟩
def e94 : ℝ := (168909/50000000000000)
theorem h94 : Model (fun x => f94 ((111/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(31833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((111/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(7717041800643/20000000000000),(-15508524519/12500000000000),(199466553/50000000000000),(-160343/12500000000000)⟩
def e96 : ℝ := (2071/50000000000000)
theorem h96 : Model (fun x => f96 ((111/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (129166666666663/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(61414790996783/50000000000000),(124068196151/50000000000000),(-99733277/12500000000000),(2565483/100000000000000)⟩
def e97 : ℝ := (34641/100000000000000)
theorem h97 : Model (fun x => f97 ((111/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1289710610932443/50000000000000),(2605432119171/50000000000000),(-2094398817/12500000000000),(53875143/100000000000000)⟩
def e98 : ℝ := (727461/100000000000000)
theorem h98 : Model (fun x => f98 ((111/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(11414790996783/50000000000000),(124068196151/50000000000000),(-99733277/12500000000000),(2565483/100000000000000)⟩
def e99 : ℝ := (34641/100000000000000)
theorem h99 : Model (fun x => f99 ((111/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(294435541402543/50000000000000),(7590101286073/100000000000000),(-11475419931/100000000000000),(-584671/12500000000000)⟩
def e100 : ℝ := (29303/2000000000000)
theorem h100 : Model (fun x => f100 ((111/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(150871062127141/100000000000000),(152392446719/25000000000000),(-268862957/20000000000000),(2342751/100000000000000)⟩
def e101 : ℝ := (104413/100000000000000)
theorem h101 : Model (fun x => f101 ((111/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(61414790996783/5000000000000),(124068196151/5000000000000),(-99733277/1250000000000),(2565483/10000000000000)⟩
def e102 : ℝ := (34641/10000000000000)
theorem h102 : Model (fun x => f102 ((111/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1379166882062801/100000000000000),(386366713737/12500000000000),(-1864595389/20000000000000),(27997581/100000000000000)⟩
def e103 : ℝ := (450823/100000000000000)
theorem h103 : Model (fun x => f103 ((111/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1479166882062801/100000000000000),(386366713737/12500000000000),(-1864595389/20000000000000),(27997581/100000000000000)⟩
def e104 : ℝ := (450823/100000000000000)
theorem h104 : Model (fun x => f104 ((111/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1742077206979489/20000000000000),(65235939672433/50000000000000),(9964072783/100000000000000),(-966637437/100000000000000)⟩
def e105 : ℝ := (3432447/12500000000000)
theorem h105 : Model (fun x => f105 ((111/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(111414790996783/50000000000000),(124068196151/50000000000000),(-99733277/12500000000000),(2565483/100000000000000)⟩
def e106 : ℝ := (34641/100000000000000)
theorem h106 : Model (fun x => f106 ((111/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(496530226114273/100000000000000),(27646064287/2500000000000),(-2940047217/100000000000000),(7473717/100000000000000)⟩
def e107 : ℝ := (34739/20000000000000)
theorem h107 : Model (fun x => f107 ((111/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(553208113661071/50000000000000),(462027071163/12500000000000),(-776894399/10000000000000),(13273579/100000000000000)⟩
def e108 : ℝ := (5043/800000000000)
theorem h108 : Model (fun x => f108 ((111/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(48186562276253513/50000000000000),(110344798564749/6250000000000),(1064015582109/25000000000000),(-19306847011/100000000000000)⟩
def e109 : ℝ := (379826313/100000000000000)
theorem h109 : Model (fun x => f109 ((111/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(3168292304669961/12500000000000),(3200241381099/3125000000000),(-5646122097/2500000000000),(49197771/12500000000000)⟩
def e110 : ℝ := (2192673/12500000000000)
theorem h110 : Model (fun x => f110 ((111/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1157292623184753/20000000000000),(43136372571/50000000000),(40189741/12500000000000),(-318685407/50000000000000)⟩
def e111 : ℝ := (18278829/100000000000000)
theorem h111 : Model (fun x => f111 ((111/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(8002795862823873/12500000000000),(1168415860474801/100000000000000),(2742837748783/100000000000000),(-3243625153/25000000000000)⟩
def e112 : ℝ := (252118993/100000000000000)
theorem h112 : Model (fun x => f112 ((111/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(16039549145509801/10000000000000),(586786527502157/20000000000000),(6998900077219/100000000000000),(-32281347623/100000000000000)⟩
def e113 : ℝ := (315972653/50000000000000)
theorem h113 : Model (fun x => f113 ((111/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(1056097434889987/12500000000000),(1066747127033/3125000000000),(-1882040699/2500000000000),(16399257/12500000000000)⟩
def e114 : ℝ := (730891/12500000000000)
theorem h114 : Model (fun x => f114 ((111/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(5211898140009/100000000000000),(3540531321/3125000000000),(251417647/100000000000000),(-557643/20000000000000)⟩
def e115 : ℝ := (35131/100000000000000)
theorem h115 : Model (fun x => f115 ((111/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(594927279647/50000000000000),(7759569609/20000000000000),(296944717/100000000000000),(-48933/6250000000000)⟩
def e116 : ℝ := (16001/100000000000000)
theorem h116 : Model (fun x => f116 ((111/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(100528187837003/100000000000000),(1842056141217/50000000000000),(37436460171/100000000000000),(3785141/50000000000000)⟩
def e117 : ℝ := (467527/25000000000000)
theorem h117 : Model (fun x => f117 ((111/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(2240065407429/1000000000000),(4229369508833/50000000000000),(91759050569/100000000000000),(16589411/20000000000000)⟩
def e118 : ℝ := (4394219/100000000000000)
theorem h118 : Model (fun x => f118 ((111/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(16061949799584091/10000000000000),(2942391376528451/100000000000000),(1772664781947/25000000000000),(-4024800071/12500000000000)⟩
def e119 : ℝ := (25453581/4000000000000)
theorem h119 : Model (fun x => f119 ((111/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(135819411109/50000000000000),(2952462177/25000000000000),(15456937/10000000000000),(279059/100000000000000)⟩
def e120 : ℝ := (7451/100000000000000)
theorem h120 : Model (fun x => f120 ((111/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(15503501911/25000000000000),(3370173867/100000000000000),(62424759/100000000000000),(44999/12500000000000)⟩
def e121 : ℝ := (103/5000000000000)
theorem h121 : Model (fun x => f121 ((111/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(7078769361/50000000000000),(923275927/100000000000000),(442383/2000000000000),(26473/12500000000000)⟩
def e122 : ℝ := (123/12500000000000)
theorem h122 : Model (fun x => f122 ((111/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(323210691/10000000000000),(6147751/2500000000000),(3613867/50000000000000),(96231/100000000000000)⟩
def e123 : ℝ := (61/10000000000000)
theorem h123 : Model (fun x => f123 ((111/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(969632073/10000000000000),(18443253/2500000000000),(10841601/50000000000000),(288693/100000000000000)⟩
def e124 : ℝ := (183/10000000000000)
theorem h124 : Model (fun x => f124 ((111/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-969632073/10000000000000),(-18443253/2500000000000),(-10841601/50000000000000),(-288693/100000000000000)⟩
def e125 : ℝ := (183/10000000000000)
theorem h125 : Model (fun x => f125 ((111/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(8030974414976009/5000000000000),(2942390638798331/100000000000000),(3545318722293/50000000000000),(-32198689261/100000000000000)⟩
def e126 : ℝ := (127268271/20000000000000)
theorem h126 : Model (fun x => f126 ((111/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(3168292304669961/10000000000000),(3200241381099/2500000000000),(-5646122097/2000000000000),(49197771/10000000000000)⟩
def e127 : ℝ := (2192673/10000000000000)
theorem h127 : Model (fun x => f127 ((111/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2465422654450911/100000000000000),(5490842620639/50000000000000),(-8483784129/50000000000000),(459697/5000000000000)⟩
def e128 : ℝ := (495211/25000000000000)
theorem h128 : Model (fun x => f128 ((111/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(781117962385580969/100000000000000),(265411916979759/4000000000000),(430439289847/25000000000000),(-3767985463/10000000000000)⟩
def e129 : ℝ := (257387061/20000000000000)
theorem h129 : Model (fun x => f129 ((111/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(12802163669/100000000000000),(-54374739/50000000000000),(447783/50000000000000),(-6751/100000000000000)⟩
def e130 : ℝ := (19/25000000000000)
theorem h130 : Model (fun x => f130 ((111/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (774480903737137671/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(10281384888207/50000000000000),(50504202567/25000000000000),(-853625923/100000000000000),(918617/25000000000000)⟩
def e131 : ℝ := (30737/10000000000000)
theorem h131 : Model (fun x => f131 ((111/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(46478169504907/100000000000000),(261780150799/50000000000000),(-1370575387/100000000000000),(1195239/25000000000000)⟩
def e132 : ℝ := (161297/25000000000000)
theorem h132 : Model (fun x => f132 ((111/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-7536789620099/1562500000000),(-2691208081129/50000000000000),(2891317261/20000000000000),(-5268513/10000000000000)⟩
def e133 : ℝ := (1633399/10000000000000)
theorem h133 : Model (fun x => f133 ((111/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(9009009009009/25000000000000),(-162324486649/50000000000000),(116990621/4000000000000),(-26349239/100000000000000)⟩
def e134 : ℝ := (11977/5000000000000)
theorem h134 : Model (fun x => f134 ((111/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (11/4))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-173821454301383/100000000000000),(-373650380079/100000000000000),(8575800291/100000000000000),(-19249019/20000000000000)⟩
def e135 : ℝ := (1140681/12500000000000)
theorem h135 : Model (fun x => f135 ((111/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(151807041/256000),(1367631/64000),(36963/128000),(111/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((111/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((111/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(12308679/32000),(332667/32000),(2997/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((111/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(250276473/256000),(406593/12800),(48951/128000),(129/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((111/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-12321/1600),(-111/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((111/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(248305113/256000),(404817/12800),(48871/128000),(129/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((111/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((111/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(333/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((111/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-333/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((111/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(244042713/256000),(402897/12800),(48871/128000),(129/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((111/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(244810713/256000),(402897/12800),(48871/128000),(129/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((111/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((111/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(244810713/4000),(402897/200),(48871/2000),(129/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((111/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((111/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(28691530749/512000),(258482259/128000),(6986007/256000),(20979/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((111/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1784498723/100000000000000),(-64306261/100000000000000),(1448339/100000000000000),(-26097/100000000000000)⟩
def e151 : ℝ := (29/6250000000000)
theorem h151 : Model (fun x => f151 ((111/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (13821772797/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(13652012647663/12500000000000),(-340869491441/100000000000000),(2703346169/100000000000000),(-2070441/10000000000000)⟩
def e152 : ℝ := (55737593/100000000000000)
theorem h152 : Model (fun x => f152 ((111/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(231/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((111/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(44121/1600),(211/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((111/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(453/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((111/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(4415011037527/100000000000000),(-29238483693/100000000000000),(96816171/50000000000000),(-641167/50000000000000)⟩
def e156 : ℝ := (1069/12500000000000)
theorem h156 : Model (fun x => f156 ((111/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (45/2))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(24349337748341/20000000000000),(17909484963/5000000000000),(15490587/4000000000000),(-641171/25000000000000)⟩
def e157 : ℝ := (456087/100000000000000)
theorem h157 : Model (fun x => f157 ((111/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(44349337748341/20000000000000),(17909484963/5000000000000),(15490587/4000000000000),(-641171/25000000000000)⟩
def e158 : ℝ := (456087/100000000000000)
theorem h158 : Model (fun x => f158 ((111/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(27718336092713/25000000000000),(17909484963/10000000000000),(193632337/100000000000000),(-641171/50000000000000)⟩
def e159 : ℝ := (45609/20000000000000)
theorem h159 : Model (fun x => f159 ((111/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(2718336092713/25000000000000),(17909484963/10000000000000),(193632337/100000000000000),(-641171/50000000000000)⟩
def e160 : ℝ := (45609/20000000000000)
theorem h160 : Model (fun x => f160 ((111/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((111/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((111/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(51146929694887/12500000000000),(165236319599/25000000000000),(714595529/100000000000000),(-4732453/100000000000000)⟩
def e163 : ℝ := (841597/100000000000000)
theorem h163 : Model (fun x => f163 ((111/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2764889723273381/100000000000000),(165236319599/25000000000000),(714595529/100000000000000),(-4732453/100000000000000)⟩
def e164 : ℝ := (420799/50000000000000)
theorem h164 : Model (fun x => f164 ((111/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((111/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(383190713044899/12500000000000),(113691744539/2000000000000),(14659471/200000000000),(-9535691/25000000000000)⟩
def e166 : ℝ := (7256907/100000000000000)
theorem h166 : Model (fun x => f166 ((111/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(521744166046259/6250000000000),(113691744539/2000000000000),(14659471/200000000000),(-9535691/25000000000000)⟩
def e167 : ℝ := (1814227/25000000000000)
theorem h167 : Model (fun x => f167 ((111/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((111/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(9255603295284777/100000000000000),(21253362846339/100000000000000),(17235886289/50000000000000),(-62602247/50000000000000)⟩
def e169 : ℝ := (27236137/100000000000000)
theorem h169 : Model (fun x => f169 ((111/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3631162728583099/25000000000000),(21253362846339/100000000000000),(17235886289/50000000000000),(-62602247/50000000000000)⟩
def e170 : ℝ := (13618069/50000000000000)
theorem h170 : Model (fun x => f170 ((111/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((111/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(16103966226911861/100000000000000),(24788607946657/50000000000000),(52204053179/50000000000000),(-222183557/100000000000000)⟩
def e172 : ℝ := (1276969/2000000000000)
theorem h172 : Model (fun x => f172 ((111/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(9219840256313073/50000000000000),(24788607946657/50000000000000),(52204053179/50000000000000),(-222183557/100000000000000)⟩
def e173 : ℝ := (63848451/100000000000000)
theorem h173 : Model (fun x => f173 ((111/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((111/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(10222345237824437/50000000000000),(17598487078643/20000000000000),(6006404597/2500000000000),(-99907523/50000000000000)⟩
def e175 : ℝ := (14237841/12500000000000)
theorem h175 : Model (fun x => f175 ((111/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(10423535714014913/50000000000000),(17598487078643/20000000000000),(6006404597/2500000000000),(-99907523/50000000000000)⟩
def e176 : ℝ := (113902729/100000000000000)
theorem h176 : Model (fun x => f176 ((111/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((111/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(11556922647818501/50000000000000),(134896187140107/100000000000000),(23216832879/5000000000000),(111795883/100000000000000)⟩
def e178 : ℝ := (87629189/50000000000000)
theorem h178 : Model (fun x => f178 ((111/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(11548113124008977/50000000000000),(134896187140107/100000000000000),(23216832879/5000000000000),(111795883/100000000000000)⟩
def e179 : ℝ := (175258379/100000000000000)
theorem h179 : Model (fun x => f179 ((111/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((111/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(3200944808079507/12500000000000),(47732016445023/25000000000000),(200284866889/25000000000000),(920584903/100000000000000)⟩
def e181 : ℝ := (62060941/25000000000000)
theorem h181 : Model (fun x => f181 ((111/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(25610891797969389/100000000000000),(47732016445023/25000000000000),(200284866889/25000000000000),(920584903/100000000000000)⟩
def e182 : ℝ := (49648753/20000000000000)
theorem h182 : Model (fun x => f182 ((111/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(2784760461639501/100000000000000),(66628054247351/100000000000000),(478643953823/100000000000000),(315235429/20000000000000)⟩
def e183 : ℝ := (21759801/25000000000000)
theorem h183 : Model (fun x => f183 ((111/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(4917159396791/4000000000000),(397136898761/100000000000000),(750122947/100000000000000),(-107499/5000000000000)⟩
def e184 : ℝ := (20429/4000000000000)
theorem h184 : Model (fun x => f184 ((111/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(52718336092713/25000000000000),(17909484963/10000000000000),(193632337/100000000000000),(-641171/50000000000000)⟩
def e185 : ℝ := (45609/20000000000000)
theorem h185 : Model (fun x => f185 ((111/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(444675673661479/100000000000000),(755326598021/100000000000000),(1137387621/100000000000000),(-589333/12500000000000)⟩
def e186 : ℝ := (193363/20000000000000)
theorem h186 : Model (fun x => f186 ((111/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(117212808081697/12500000000000),(1194586843627/50000000000000),(576529281/12500000000000),(-6072337/50000000000000)⟩
def e187 : ℝ := (768057/25000000000000)
theorem h187 : Model (fun x => f187 ((111/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(988682273731451/50000000000000),(6717507276189/100000000000000),(15820554827/100000000000000),(-12373973/50000000000000)⟩
def e188 : ℝ := (4335701/50000000000000)
theorem h188 : Model (fun x => f188 ((111/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2430754166359647/100000000000000),(4027651936881/25000000000000),(7619801593/12500000000000),(40283483/100000000000000)⟩
def e189 : ℝ := (20952017/100000000000000)
theorem h189 : Model (fun x => f189 ((111/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((111/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(27718336092713/3125000000000),(17909484963/1250000000000),(193632337/12500000000000),(-641171/6250000000000)⟩
def e191 : ℝ := (45609/2500000000000)
theorem h191 : Model (fun x => f191 ((111/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(1009915739886591/100000000000000),(1829895695801/100000000000000),(2299181643/100000000000000),(-3102179/25000000000000)⟩
def e192 : ℝ := (467017/20000000000000)
theorem h192 : Model (fun x => f192 ((111/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1109915739886591/100000000000000),(1829895695801/100000000000000),(2299181643/100000000000000),(-3102179/25000000000000)⟩
def e193 : ℝ := (467017/20000000000000)
theorem h193 : Model (fun x => f193 ((111/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(26979323090374813/100000000000000),(55823609261719/25000000000000),(1027281789149/100000000000000),(407843711/25000000000000)⟩
def e194 : ℝ := (290217631/100000000000000)
theorem h194 : Model (fun x => f194 ((111/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(370654221623/100000000000000),(-153386031/5000000000000),(2819183/25000000000000),(1063/100000000000000)⟩
def e195 : ℝ := (4313/100000000000000)
theorem h195 : Model (fun x => f195 ((111/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (26754999449946313/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(5160916106577/50000000000000),(161531024953/100000000000000),(11045359/25000000000000),(-81139/6250000000000)⟩
def e196 : ℝ := (454813/100000000000000)
theorem h196 : Model (fun x => f196 ((111/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(24349337748341/10000000000000),(17909484963/2500000000000),(15490587/2000000000000),(-641171/12500000000000)⟩
def e197 : ℝ := (456087/50000000000000)
theorem h197 : Model (fun x => f197 ((111/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(11274125508643/25000000000000),(-72844841983/100000000000000),(1215913/3125000000000),(292973/50000000000000)⟩
def e198 : ℝ := (94917/100000000000000)
theorem h198 : Model (fun x => f198 ((111/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (221388108756999/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(54903497965427/50000000000000),(145689683961/100000000000000),(-77818433/100000000000000),(-1171893/100000000000000)⟩
def e199 : ℝ := (652061/100000000000000)
theorem h199 : Model (fun x => f199 ((111/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(4903497965427/50000000000000),(145689683961/100000000000000),(-77818433/100000000000000),(-1171893/100000000000000)⟩
def e200 : ℝ := (652061/100000000000000)
theorem h200 : Model (fun x => f200 ((111/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(101310026007633/25000000000000),(16802009683/3125000000000),(-11487483/4000000000000),(-1081211/25000000000000)⟩
def e201 : ℝ := (1203209/50000000000000)
theorem h201 : Model (fun x => f201 ((111/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2760954389744817/100000000000000),(16802009683/3125000000000),(-11487483/4000000000000),(-1081211/25000000000000)⟩
def e202 : ℝ := (2406419/100000000000000)
theorem h202 : Model (fun x => f202 ((111/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1515860537199913/50000000000000),(4612818751571/100000000000000),(-420140377/25000000000000),(-37941217/100000000000000)⟩
def e203 : ℝ := (10332463/50000000000000)
theorem h203 : Model (fun x => f203 ((111/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4157051013390389/50000000000000),(4612818751571/100000000000000),(-420140377/25000000000000),(-37941217/100000000000000)⟩
def e204 : ℝ := (20664927/100000000000000)
theorem h204 : Model (fun x => f204 ((111/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4564732837117109/50000000000000),(17177986665847/100000000000000),(-797438481/50000000000000),(-145132519/100000000000000)⟩
def e205 : ℝ := (19268211/25000000000000)
theorem h205 : Model (fun x => f205 ((111/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14398513293281837/100000000000000),(17177986665847/100000000000000),(-797438481/50000000000000),(-145132519/100000000000000)⟩
def e206 : ℝ := (15414569/20000000000000)
theorem h206 : Model (fun x => f206 ((111/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15810574906057459/100000000000000),(19919889815617/50000000000000),(12070570583/100000000000000),(-8594801/2500000000000)⟩
def e207 : ℝ := (179154481/100000000000000)
theorem h207 : Model (fun x => f207 ((111/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(567071537242867/3125000000000),(19919889815617/50000000000000),(12070570583/100000000000000),(-8594801/2500000000000)⟩
def e208 : ℝ := (89577241/50000000000000)
theorem h208 : Model (fun x => f208 ((111/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9962947517204899/50000000000000),(70184136572671/100000000000000),(57175622087/100000000000000),(-603579921/100000000000000)⟩
def e209 : ℝ := (158273659/50000000000000)
theorem h209 : Model (fun x => f209 ((111/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(81313103947163/400000000000),(70184136572671/100000000000000),(57175622087/100000000000000),(-603579921/100000000000000)⟩
def e210 : ℝ := (316547319/100000000000000)
theorem h210 : Model (fun x => f210 ((111/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(22321869185628089/100000000000000),(106683293030333/100000000000000),(149214733953/100000000000000),(-174463167/20000000000000)⟩
def e211 : ℝ := (482809849/100000000000000)
theorem h211 : Model (fun x => f211 ((111/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(22304250138009041/100000000000000),(106683293030333/100000000000000),(149214733953/100000000000000),(-174463167/20000000000000)⟩
def e212 : ℝ := (9656197/2000000000000)
theorem h212 : Model (fun x => f212 ((111/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(4898325408290217/20000000000000),(29928142154531/20000000000000),(60383590269/20000000000000),(-1084874553/100000000000000)⟩
def e213 : ℝ := (679635003/100000000000000)
theorem h213 : Model (fun x => f213 ((111/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(12247480187392209/50000000000000),(29928142154531/20000000000000),(60383590269/20000000000000),(-1084874553/100000000000000)⟩
def e214 : ℝ := (169908751/25000000000000)
theorem h214 : Model (fun x => f214 ((111/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(2402219767219407/100000000000000),(5036188877277/10000000000000),(57139641369/25000000000000),(-70033077/100000000000000)⟩
def e215 : ℝ := (115957061/50000000000000)
theorem h215 : Model (fun x => f215 ((111/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(24115152710717/20000000000000),(319954930677/100000000000000),(41354673/100000000000000),(-700097/25000000000000)⟩
def e216 : ℝ := (359319/25000000000000)
theorem h216 : Model (fun x => f216 ((111/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(104903497965427/50000000000000),(145689683961/100000000000000),(-77818433/100000000000000),(-1171893/100000000000000)⟩
def e217 : ℝ := (652061/100000000000000)
theorem h217 : Model (fun x => f217 ((111/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(440189755415293/100000000000000),(611334298599/100000000000000),(-114282193/100000000000000),(-2572087/50000000000000)⟩
def e218 : ℝ := (1370699/50000000000000)
theorem h218 : Model (fun x => f218 ((111/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(923548902232199/100000000000000),(961966595239/50000000000000),(308330201/100000000000000),(-16593619/100000000000000)⟩
def e219 : ℝ := (8644513/100000000000000)
theorem h219 : Model (fun x => f219 ((111/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(484417551931439/25000000000000),(1076412381509/20000000000000),(2731179233/100000000000000),(-11671387/25000000000000)⟩
def e220 : ℝ := (24231017/100000000000000)
theorem h220 : Model (fun x => f220 ((111/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1168180324057833/50000000000000),(6344566804913/50000000000000),(21314629837/100000000000000),(-12448683/12500000000000)⟩
def e221 : ℝ := (143801/250000000000)
theorem h221 : Model (fun x => f221 ((111/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(54903497965427/6250000000000),(145689683961/12500000000000),(-77818433/12500000000000),(-1171893/12500000000000)⟩
def e222 : ℝ := (652061/12500000000000)
theorem h222 : Model (fun x => f222 ((111/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(999031731000417/100000000000000),(297094480473/20000000000000),(-581192791/100000000000000),(-3043883/25000000000000)⟩
def e223 : ℝ := (1663441/25000000000000)
theorem h223 : Model (fun x => f223 ((111/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1099031731000417/100000000000000),(297094480473/20000000000000),(-581192791/100000000000000),(-3043883/25000000000000)⟩
def e224 : ℝ := (1663441/25000000000000)
theorem h224 : Model (fun x => f224 ((111/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(5135468974679633/20000000000000),(348327194817/200000000000),(102292340867/25000000000000),(-227221907/20000000000000)⟩
def e225 : ℝ := (15849483/2000000000000)
theorem h225 : Model (fun x => f225 ((111/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(389448365837/100000000000000),(-2641539799/100000000000000),(11711091/100000000000000),(-2011/10000000000000)⟩
def e226 : ℝ := (3089/25000000000000)
theorem h226 : Model (fun x => f226 ((111/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (1593923136127657/6250000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(9355405627249/100000000000000),(132677961619/100000000000000),(-31777119/20000000000000),(-111921/12500000000000)⟩
def e227 : ℝ := (615477/50000000000000)
theorem h227 : Model (fun x => f227 ((111/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(19677237840403/100000000000000),(73552246643/25000000000000),(-114704159/100000000000000),(-274199/12500000000000)⟩
def e228 : ℝ := (1685767/100000000000000)
theorem h228 : Model (fun x => f228 ((111/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(1074535599473/5000000000000),(127124941951/50000000000000),(-74525029/12500000000000),(1874667/100000000000000)⟩
def e229 : ℝ := (13035167/100000000000000)
theorem h229 : Model (fun x => f229 ((111/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3872200358461/50000000000000),(5463050989/25000000000000),(-411713633/100000000000000),(4384687/100000000000000)⟩
def e230 : ℝ := (4882881/100000000000000)
theorem h230 : Model (fun x => f230 ((111/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-166077053584461/100000000000000),(-351798176123/100000000000000),(4082043329/50000000000000),(-11482551/12500000000000)⟩
def e231 : ℝ := (14008329/100000000000000)
theorem h231 : Model (fun x => f231 ((111/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((111/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-12321/320),(-111/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((111/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2331/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((111/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6327/320),(-27/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((111/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((111/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14647/320),(-27/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((111/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((111/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(366175/32),(-675/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((111/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14319/1600),(9/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((111/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23919/1600),(9/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((111/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((111/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4520691/1600),(1701/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((111/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(8848204843/25000000000000),(-13317253/50000000000000),(749869/50000000000000),(-2243/100000000000000)⟩
def e244 : ℝ := (33/50000000000000)
theorem h244 : Model (fun x => f244 ((111/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (45171/16))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(40499892604819/10000000000000),(-898956193543/50000000000000),(-4682770923/50000000000000),(-8516071/12500000000000)⟩
def e245 : ℝ := (183687/10000000000000)
theorem h245 : Model (fun x => f245 ((111/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(999/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((111/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(92241/1600),(471/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((111/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(125841/1600),(471/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((111/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(36481/1600),(191/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((111/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(4590805521/2560000),(20609091/640000),(261083/1280000),(331/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((111/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((111/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(205209/160),(1359/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((111/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(15593857969/20000000000000),(-516352913/50000000000000),(10258667/100000000000000),(-18117/20000000000000)⟩
def e253 : ℝ := (767/100000000000000)
theorem h253 : Model (fun x => f253 ((111/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (101241/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(139821033706591/100000000000000),(26352392983/4000000000000),(261322649/25000000000000),(-2415407/100000000000000)⟩
def e254 : ℝ := (2803011/100000000000000)
theorem h254 : Model (fun x => f254 ((111/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(239821033706591/100000000000000),(26352392983/4000000000000),(261322649/25000000000000),(-2415407/100000000000000)⟩
def e255 : ℝ := (2803011/100000000000000)
theorem h255 : Model (fun x => f255 ((111/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(23982103370659/20000000000000),(329404912287/100000000000000),(261322649/50000000000000),(-150963/12500000000000)⟩
def e256 : ℝ := (1401507/100000000000000)
theorem h256 : Model (fun x => f256 ((111/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(3982103370659/20000000000000),(329404912287/100000000000000),(261322649/50000000000000),(-150963/12500000000000)⟩
def e257 : ℝ := (1401507/100000000000000)
theorem h257 : Model (fun x => f257 ((111/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(442526907434779/100000000000000),(1215660985821/100000000000000),(482202507/25000000000000),(-4457003/100000000000000)⟩
def e258 : ℝ := (5172229/100000000000000)
theorem h258 : Model (fun x => f258 ((111/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(349780149143633/12500000000000),(1215660985821/100000000000000),(482202507/25000000000000),(-4457003/100000000000000)⟩
def e259 : ℝ := (517223/10000000000000)
theorem h259 : Model (fun x => f259 ((111/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3355385477506851/100000000000000),(10675249319153/100000000000000),(209421691/1000000000000),(-26431697/100000000000000)⟩
def e260 : ℝ := (9094611/20000000000000)
theorem h260 : Model (fun x => f260 ((111/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8637766429887803/100000000000000),(10675249319153/100000000000000),(209421691/1000000000000),(-26431697/100000000000000)⟩
def e261 : ℝ := (1421033/3125000000000)
theorem h261 : Model (fun x => f261 ((111/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(10357590370658871/100000000000000),(20626986782951/50000000000000),(52710769481/50000000000000),(-11234813/100000000000000)⟩
def e262 : ℝ := (43998187/25000000000000)
theorem h262 : Model (fun x => f262 ((111/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(1562663798970649/10000000000000),(20626986782951/50000000000000),(52710769481/50000000000000),(-11234813/100000000000000)⟩
def e263 : ℝ := (175992749/100000000000000)
theorem h263 : Model (fun x => f263 ((111/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(18737982380250399/100000000000000),(50471383044397/50000000000000),(85994004093/25000000000000),(180340213/50000000000000)⟩
def e264 : ℝ := (43121963/10000000000000)
theorem h264 : Model (fun x => f264 ((111/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(5268424166491171/25000000000000),(50471383044397/50000000000000),(85994004093/25000000000000),(180340213/50000000000000)⟩
def e265 : ℝ := (431219631/100000000000000)
theorem h265 : Model (fun x => f265 ((111/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(3158697324031731/12500000000000),(95229392280617/50000000000000),(855114533917/100000000000000),(1838632401/100000000000000)⟩
def e266 : ℝ := (51064897/6250000000000)
theorem h266 : Model (fun x => f266 ((111/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(64179898861587/250000000000),(95229392280617/50000000000000),(855114533917/100000000000000),(1838632401/100000000000000)⟩
def e267 : ℝ := (817038353/100000000000000)
theorem h267 : Model (fun x => f267 ((111/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(15391689688170193/50000000000000),(312944808780237/100000000000000),(893463069499/50000000000000),(1141377099/20000000000000)⟩
def e268 : ℝ := (1353112507/100000000000000)
theorem h268 : Model (fun x => f268 ((111/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(15382880164360669/50000000000000),(312944808780237/100000000000000),(893463069499/50000000000000),(1141377099/20000000000000)⟩
def e269 : ℝ := (338278127/25000000000000)
theorem h269 : Model (fun x => f269 ((111/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(36891382224015747/100000000000000),(476597663499191/100000000000000),(41679546771/1250000000000),(874588149/6250000000000)⟩
def e270 : ℝ := (521737699/25000000000000)
theorem h270 : Model (fun x => f270 ((111/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(922367888933727/2500000000000),(476597663499191/100000000000000),(41679546771/1250000000000),(874588149/6250000000000)⟩
def e271 : ℝ := (2086950797/100000000000000)
theorem h271 : Model (fun x => f271 ((111/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(183648213975531/2500000000000),(5410651588341/2500000000000),(2426653666219/100000000000000),(7907527307/50000000000000)⟩
def e272 : ℝ := (200803139/20000000000000)
theorem h272 : Model (fun x => f272 ((111/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(143785320520243/100000000000000),(394991132863/50000000000000),(1169244659/50000000000000),(54691/10000000000000)⟩
def e273 : ℝ := (3375597/100000000000000)
theorem h273 : Model (fun x => f273 ((111/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(43982103370659/20000000000000),(329404912287/100000000000000),(261322649/50000000000000),(-150963/12500000000000)⟩
def e274 : ℝ := (1401507/100000000000000)
theorem h274 : Model (fun x => f274 ((111/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(483606354226833/100000000000000),(14487920903/1000000000000),(1691889957/50000000000000),(-934249/50000000000000)⟩
def e275 : ℝ := (6178611/100000000000000)
theorem h275 : Model (fun x => f275 ((111/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(212700246623121/20000000000000),(4779069260863/100000000000000),(14741226083/100000000000000),(1096103/12500000000000)⟩
def e276 : ℝ := (20411949/100000000000000)
theorem h276 : Model (fun x => f276 ((111/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(584687764621423/25000000000000),(1751612652057/12500000000000),(10743666913/20000000000000),(39987761/50000000000000)⟩
def e277 : ℝ := (11995189/20000000000000)
theorem h277 : Model (fun x => f277 ((111/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(840695176403557/25000000000000),(19312106764891/50000000000000),(242629957733/100000000000000),(439919719/50000000000000)⟩
def e278 : ℝ := (168100249/100000000000000)
theorem h278 : Model (fun x => f278 ((111/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(23982103370659/2500000000000),(329404912287/12500000000000),(261322649/6250000000000),(-150963/1562500000000)⟩
def e279 : ℝ := (1401507/12500000000000)
theorem h279 : Model (fun x => f279 ((111/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1103069455346603/100000000000000),(1712610782011/50000000000000),(3259825851/50000000000000),(-4557361/50000000000000)⟩
def e280 : ℝ := (14587653/100000000000000)
theorem h280 : Model (fun x => f280 ((111/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1203069455346603/100000000000000),(1712610782011/50000000000000),(3259825851/50000000000000),(-4557361/50000000000000)⟩
def e281 : ℝ := (14587653/100000000000000)
theorem h281 : Model (fun x => f281 ((111/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(20228293759766873/50000000000000),(289929402612063/50000000000000),(446121339127/10000000000000),(21107349249/100000000000000)⟩
def e282 : ℝ := (2566822143/100000000000000)
theorem h282 : Model (fun x => f282 ((111/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(49435706831/20000000000000),(-3542776549/100000000000000),(294017/1250000000000),(-75421/100000000000000)⟩
def e283 : ℝ := (16489/100000000000000)
theorem h283 : Model (fun x => f283 ((111/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (19936121913373479/50000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(9078779266131/50000000000000),(68677234269/25000000000000),(29268719/50000000000000),(-1513517/100000000000000)⟩
def e284 : ℝ := (1959761/50000000000000)
theorem h284 : Model (fun x => f284 ((111/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(139821033706591/50000000000000),(26352392983/2000000000000),(261322649/12500000000000),(-2415407/50000000000000)⟩
def e285 : ℝ := (2803011/50000000000000)
theorem h285 : Model (fun x => f285 ((111/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(8339552078017/20000000000000),(-57273738219/50000000000000),(33231787/25000000000000),(277037/50000000000000)⟩
def e286 : ℝ := (123329/25000000000000)
theorem h286 : Model (fun x => f286 ((111/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (119580586686501/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(29151119804957/25000000000000),(114547476437/50000000000000),(-265854297/100000000000000),(-138519/12500000000000)⟩
def e287 : ℝ := (1872833/50000000000000)
theorem h287 : Model (fun x => f287 ((111/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(4151119804957/25000000000000),(114547476437/50000000000000),(-265854297/100000000000000),(-138519/12500000000000)⟩
def e288 : ℝ := (1872833/50000000000000)
theorem h288 : Model (fun x => f288 ((111/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(8606521085273/2000000000000),(845469468939/100000000000000),(-490564477/50000000000000),(-4089609/100000000000000)⟩
def e289 : ℝ := (2764659/20000000000000)
theorem h289 : Model (fun x => f289 ((111/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(557208067995587/20000000000000),(845469468939/100000000000000),(-490564477/50000000000000),(-4089609/100000000000000)⟩
def e290 : ℝ := (215989/1562500000000)
theorem h290 : Model (fun x => f290 ((111/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(812161957321399/25000000000000),(3684266537571/50000000000000),(-3306960193/50000000000000),(-40137663/100000000000000)⟩
def e291 : ℝ := (15069239/12500000000000)
theorem h291 : Model (fun x => f291 ((111/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(2132757195416637/25000000000000),(3684266537571/50000000000000),(-3306960193/50000000000000),(-40137663/100000000000000)⟩
def e292 : ℝ := (120553913/100000000000000)
theorem h292 : Model (fun x => f292 ((111/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(1989512336591183/20000000000000),(7034048996359/25000000000000),(-13511296641/100000000000000),(-176080799/100000000000000)⟩
def e293 : ℝ := (230412037/50000000000000)
theorem h293 : Model (fun x => f293 ((111/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(7608304651001767/50000000000000),(7034048996359/25000000000000),(-13511296641/100000000000000),(-176080799/100000000000000)⟩
def e294 : ℝ := (18432963/4000000000000)
theorem h294 : Model (fun x => f294 ((111/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(141945984252137/800000000000),(67668548710533/100000000000000),(4124909081/50000000000000),(-119924061/25000000000000)⟩
def e295 : ℝ := (277524033/25000000000000)
theorem h295 : Model (fun x => f295 ((111/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(2007896231723141/10000000000000),(67668548710533/100000000000000),(4124909081/50000000000000),(-119924061/25000000000000)⟩
def e296 : ℝ := (1110096133/100000000000000)
theorem h296 : Model (fun x => f296 ((111/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(11706484721376597/50000000000000),(62452224038891/50000000000000),(111264103169/100000000000000),(-471426279/50000000000000)⟩
def e297 : ℝ := (1026732889/50000000000000)
theorem h297 : Model (fun x => f297 ((111/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(11907675197567073/50000000000000),(62452224038891/50000000000000),(111264103169/100000000000000),(-471426279/50000000000000)⟩
def e298 : ℝ := (2053465779/100000000000000)
theorem h298 : Model (fun x => f298 ((111/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(1388488265131171/5000000000000),(25025493371001/12500000000000),(352574582149/100000000000000),(-288096399/20000000000000)⟩
def e299 : ℝ := (1649855229/50000000000000)
theorem h299 : Model (fun x => f299 ((111/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(6938036563751093/25000000000000),(25025493371001/12500000000000),(352574582149/100000000000000),(-288096399/20000000000000)⟩
def e300 : ℝ := (3299710459/100000000000000)
theorem h300 : Model (fun x => f300 ((111/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(32360245612972847/100000000000000),(74256384031003/25000000000000),(159198924001/20000000000000),(-427930679/25000000000000)⟩
def e301 : ℝ := (1227162401/25000000000000)
theorem h301 : Model (fun x => f301 ((111/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(1618178947315309/5000000000000),(74256384031003/25000000000000),(159198924001/20000000000000),(-427930679/25000000000000)⟩
def e302 : ℝ := (981729921/20000000000000)
theorem h302 : Model (fun x => f302 ((111/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(5373803740932039/100000000000000),(61731434679337/50000000000000),(45412581749/6250000000000),(195534029/50000000000000)⟩
def e303 : ℝ := (2059034939/100000000000000)
theorem h303 : Model (fun x => f303 ((111/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(16995755717659/12500000000000),(106853990687/20000000000000),(-95151063/100000000000000),(-950607/25000000000000)⟩
def e304 : ℝ := (875679/10000000000000)
theorem h304 : Model (fun x => f304 ((111/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(54151119804957/25000000000000),(114547476437/50000000000000),(-265854297/100000000000000),(-138519/12500000000000)⟩
def e305 : ℝ := (1872833/50000000000000)
theorem h305 : Model (fun x => f305 ((111/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(7330859440327/1562500000000),(992459859183/100000000000000),(-626859657/100000000000000),(-1504683/25000000000000)⟩
def e306 : ℝ := (8124061/50000000000000)
theorem h306 : Model (fun x => f306 ((111/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(203250814887141/20000000000000),(1612284382087/50000000000000),(-165726279/50000000000000),(-22310617/100000000000000)⟩
def e307 : ℝ := (52865499/100000000000000)
theorem h307 : Model (fun x => f307 ((111/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1100625922740871/50000000000000),(582046698227/6250000000000),(1983814039/50000000000000),(-8614929/12500000000000)⟩
def e308 : ℝ := (76451301/50000000000000)
theorem h308 : Model (fun x => f308 ((111/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2992955091108299/100000000000000),(763212540281/3125000000000),(26527661227/50000000000000),(-165071377/100000000000000)⟩
def e309 : ℝ := (25188359/6250000000000)
theorem h309 : Model (fun x => f309 ((111/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(29151119804957/3125000000000),(114547476437/6250000000000),(-265854297/12500000000000),(-138519/1562500000000)⟩
def e310 : ℝ := (1872833/6250000000000)
theorem h310 : Model (fun x => f310 ((111/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(133600234937487/12500000000000),(2367029576427/100000000000000),(-2221985439/100000000000000),(-3166911/25000000000000)⟩
def e311 : ℝ := (19361059/50000000000000)
theorem h311 : Model (fun x => f311 ((111/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(146100234937487/12500000000000),(2367029576427/100000000000000),(-2221985439/100000000000000),(-3166911/25000000000000)⟩
def e312 : ℝ := (19361059/50000000000000)
theorem h312 : Model (fun x => f312 ((111/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(34981715357461623/100000000000000),(178149146353987/50000000000000),(1131703509599/100000000000000),(-1595330167/100000000000000)⟩
def e313 : ℝ := (2948288553/50000000000000)
theorem h313 : Model (fun x => f313 ((111/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(7146590653/2500000000000),(-2911598843/100000000000000),(2040737/10000000000000),(-6289/6250000000000)⟩
def e314 : ℝ := (49423/100000000000000)
theorem h314 : Model (fun x => f314 ((111/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (34624277869336777/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(19202187793/125000000000),(98235913857/50000000000000),(-421002617/100000000000000),(-124803/50000000000000)⟩
def e315 : ℝ := (4338497/50000000000000)
theorem h315 : Model (fun x => f315 ((111/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(16759654383331/50000000000000),(47118076479/10000000000000),(-362465179/100000000000000),(-1763123/100000000000000)⟩
def e316 : ℝ := (3149129/25000000000000)
theorem h316 : Model (fun x => f316 ((111/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(135752840523757/100000000000000),(1305629232763/100000000000000),(-3269665577/25000000000000),(-1689717/2500000000000)⟩
def e317 : ℝ := (13030891/25000000000000)
theorem h317 : Model (fun x => f317 ((111/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(48919942531083/100000000000000),(3722102229/12500000000000),(-4981291083/100000000000000),(4104043/20000000000000)⟩
def e318 : ℝ := (19790971/100000000000000)
theorem h318 : Model (fun x => f318 ((111/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-58578555526689/50000000000000),(-322021358291/100000000000000),(127311823/4000000000000),(-71340193/100000000000000)⟩
def e319 : ℝ := (337993/1000000000000)
theorem h319 : Model (fun x => f319 ((111/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((111/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-135531/1600),(-1221/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((111/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((111/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(10767/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((111/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(295149/1600),(719/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((111/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((111/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(467949/1600),(719/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((111/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2339745/32),(3595/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((111/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((111/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(547142529885941543/50000000000000),(823493083987369/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (70693/50000000000000)
theorem h329 : Model (fun x => f329 ((111/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4569193333/50000000000000),(-6877/100000000000),(38723/10000000000000),(-579/100000000000000)⟩
def e330 : ℝ := (19/100000000000000)
theorem h330 : Model (fun x => f330 ((111/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (546707908535988627/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(133634340686501/20000000000000),(155045543011/10000000000000),(11061329991/100000000000000),(56490823/100000000000000)⟩
def e331 : ℝ := (273771/12500000000000)
theorem h331 : Model (fun x => f331 ((111/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((111/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(471/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((111/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((111/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((111/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(805806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((111/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((111/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((111/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1787477271975851/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (273/25000000000000)
theorem h339 : Model (fun x => f339 ((111/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3904193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((111/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((111/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((111/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2200045456048039/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (273/25000000000000)
theorem h343 : Model (fun x => f343 ((111/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(227268031497/5000000000000),(-5821126461/100000000000000),(3727483/50000000000000),(-2387/25000000000000)⟩
def e344 : ℝ := (17/100000000000000)
theorem h344 : Model (fun x => f344 ((111/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1098613957206233/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(162494576379031/100000000000000),(200042526093/25000000000000),(-256189327/25000000000000),(656179/50000000000000)⟩
def e345 : ℝ := (2781/100000000000000)
theorem h345 : Model (fun x => f345 ((111/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(262494576379031/100000000000000),(200042526093/25000000000000),(-256189327/25000000000000),(656179/50000000000000)⟩
def e346 : ℝ := (2781/100000000000000)
theorem h346 : Model (fun x => f346 ((111/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(26249457637903/20000000000000),(200042526093/50000000000000),(-256189327/50000000000000),(656179/100000000000000)⟩
def e347 : ℝ := (1391/100000000000000)
theorem h347 : Model (fun x => f347 ((111/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(6249457637903/20000000000000),(200042526093/50000000000000),(-256189327/50000000000000),(656179/100000000000000)⟩
def e348 : ℝ := (1391/100000000000000)
theorem h348 : Model (fun x => f348 ((111/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(121091248031993/25000000000000),(1476504359257/100000000000000),(-236365153/12500000000000),(605403/25000000000000)⟩
def e349 : ℝ := (5137/100000000000000)
theorem h349 : Model (fun x => f349 ((111/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2840079277842257/100000000000000),(1476504359257/100000000000000),(-236365153/12500000000000),(605403/25000000000000)⟩
def e350 : ℝ := (2569/50000000000000)
theorem h350 : Model (fun x => f350 ((111/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3727527034600323/100000000000000),(13300604592403/100000000000000),(-11126469569/100000000000000),(6683717/100000000000000)⟩
def e351 : ℝ := (9423/12500000000000)
theorem h351 : Model (fun x => f351 ((111/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(360396319479251/4000000000000),(13300604592403/100000000000000),(-11126469569/100000000000000),(6683717/100000000000000)⟩
def e352 : ℝ := (15077/20000000000000)
theorem h352 : Model (fun x => f352 ((111/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(11825259901283443/100000000000000),(53503977911963/100000000000000),(-7554304027/100000000000000),(-44771479/100000000000000)⟩
def e353 : ℝ := (98973/25000000000000)
theorem h353 : Model (fun x => f353 ((111/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(8547153760165531/50000000000000),(53503977911963/100000000000000),(-7554304027/100000000000000),(-44771479/100000000000000)⟩
def e354 : ℝ := (395893/100000000000000)
theorem h354 : Model (fun x => f354 ((111/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(5608953763802711/25000000000000),(3465357231163/2500000000000),(11655901599/10000000000000),(-250958699/100000000000000)⟩
def e355 : ℝ := (970557/100000000000000)
theorem h355 : Model (fun x => f355 ((111/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(24771529340925129/100000000000000),(3465357231163/2500000000000),(11655901599/10000000000000),(-250958699/100000000000000)⟩
def e356 : ℝ := (485279/50000000000000)
theorem h356 : Model (fun x => f356 ((111/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(32511960503034269/100000000000000),(140517340885069/50000000000000),(145157892621/25000000000000),(-410725743/100000000000000)⟩
def e357 : ℝ := (2317989/100000000000000)
theorem h357 : Model (fun x => f357 ((111/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(32914341455415221/100000000000000),(140517340885069/50000000000000),(145157892621/25000000000000),(-410725743/100000000000000)⟩
def e358 : ℝ := (231799/10000000000000)
theorem h358 : Model (fun x => f358 ((111/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(2159959029283491/5000000000000),(100107151776783/20000000000000),(1717794884131/100000000000000),(559968999/100000000000000)⟩
def e359 : ℝ := (3146727/50000000000000)
theorem h359 : Model (fun x => f359 ((111/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(10795390384512693/25000000000000),(100107151776783/20000000000000),(1717794884131/100000000000000),(559968999/100000000000000)⟩
def e360 : ℝ := (1258691/20000000000000)
theorem h360 : Model (fun x => f360 ((111/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(28337314258289131/50000000000000),(829702582968187/100000000000000),(807174970087/20000000000000),(5326294639/100000000000000)⟩
def e361 : ℝ := (12178103/100000000000000)
theorem h361 : Model (fun x => f361 ((111/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(11335592369982319/20000000000000),(829702582968187/100000000000000),(807174970087/20000000000000),(5326294639/100000000000000)⟩
def e362 : ℝ := (1522263/12500000000000)
theorem h362 : Model (fun x => f362 ((111/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(17710326079185243/100000000000000),(486019610461099/100000000000000),(4290211679499/100000000000000),(13931944593/100000000000000)⟩
def e363 : ℝ := (10730027/100000000000000)
theorem h363 : Model (fun x => f363 ((111/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(21532313321377/12500000000000),(1050201562891/100000000000000),(31964289/12500000000000),(-2377467/100000000000000)⟩
def e364 : ℝ := (11547/100000000000000)
theorem h364 : Model (fun x => f364 ((111/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(46249457637903/20000000000000),(200042526093/50000000000000),(-256189327/50000000000000),(656179/100000000000000)⟩
def e365 : ℝ := (1391/100000000000000)
theorem h365 : Model (fun x => f365 ((111/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(267376541475023/50000000000000),(1850371667263/100000000000000),(-192260749/25000000000000),(-1065109/100000000000000)⟩
def e366 : ℝ := (14329/100000000000000)
theorem h366 : Model (fun x => f366 ((111/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1236602002831809/100000000000000),(6418401452959/100000000000000),(360588591/12500000000000),(-5755917/50000000000000)⟩
def e367 : ℝ := (41/78125000000)
theorem h367 : Model (fun x => f367 ((111/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2859608597245787/100000000000000),(9894919536723/50000000000000),(2601379081/10000000000000),(-622683/1562500000000)⟩
def e368 : ℝ := (78831/50000000000000)
theorem h368 : Model (fun x => f368 ((111/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1231479765847993/25000000000000),(32060667710783/50000000000000),(51991319049/20000000000000),(187168473/100000000000000)⟩
def e369 : ℝ := (178619/12500000000000)
theorem h369 : Model (fun x => f369 ((111/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(26249457637903/2500000000000),(200042526093/6250000000000),(-256189327/6250000000000),(656179/12500000000000)⟩
def e370 : ℝ := (1391/12500000000000)
theorem h370 : Model (fun x => f370 ((111/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(38194900377723/3125000000000),(4250881980379/100000000000000),(-96082873/2500000000000),(574393/20000000000000)⟩
def e371 : ℝ := (907/4000000000000)
theorem h371 : Model (fun x => f371 ((111/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(41319900377723/3125000000000),(4250881980379/100000000000000),(-96082873/2500000000000),(574393/20000000000000)⟩
def e372 : ℝ := (907/4000000000000)
theorem h372 : Model (fun x => f372 ((111/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(32566157594893259/50000000000000),(1057230907179597/100000000000000),(5973645508481/100000000000000),(5601172167/50000000000000)⟩
def e373 : ℝ := (4055971/20000000000000)
theorem h373 : Model (fun x => f373 ((111/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(153533618003/100000000000000),(-2492165153/100000000000000),(26371527/100000000000000),(-225901/100000000000000)⟩
def e374 : ℝ := (443/25000000000000)
theorem h374 : Model (fun x => f374 ((111/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (64069099414474251/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(27191304389501/100000000000000),(76208229279/25000000000000),(-427505367/50000000000000),(2634047/100000000000000)⟩
def e375 : ℝ := (82381/12500000000000)
theorem h375 : Model (fun x => f375 ((111/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(162494576379031/50000000000000),(200042526093/12500000000000),(-256189327/12500000000000),(656179/25000000000000)⟩
def e376 : ℝ := (2781/50000000000000)
theorem h376 : Model (fun x => f376 ((111/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(9524006303239/25000000000000),(-29032314583/25000000000000),(251362033/50000000000000),(-544073/25000000000000)⟩
def e377 : ℝ := (4813/50000000000000)
theorem h377 : Model (fun x => f377 ((111/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (65423345050553/25000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(123807949574083/100000000000000),(116129258329/50000000000000),(-502724069/50000000000000),(4352581/100000000000000)⟩
def e378 : ℝ := (81803/100000000000000)
theorem h378 : Model (fun x => f378 ((111/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(23807949574083/100000000000000),(116129258329/50000000000000),(-502724069/50000000000000),(4352581/100000000000000)⟩
def e379 : ℝ := (81803/100000000000000)
theorem h379 : Model (fun x => f379 ((111/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(45691029009483/10000000000000),(857144525761/100000000000000),(-742116483/20000000000000),(2007887/12500000000000)⟩
def e380 : ℝ := (60379/20000000000000)
theorem h380 : Model (fun x => f380 ((111/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(562524915161823/20000000000000),(857144525761/100000000000000),(-742116483/20000000000000),(2007887/12500000000000)⟩
def e381 : ℝ := (37737/12500000000000)
theorem h381 : Model (fun x => f381 ((111/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1741126408263007/50000000000000),(7593773181163/100000000000000),(-30882686271/100000000000000),(25014573/20000000000000)⟩
def e382 : ℝ := (1394121/50000000000000)
theorem h382 : Model (fun x => f382 ((111/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4382316884453483/50000000000000),(7593773181163/100000000000000),(-30882686271/100000000000000),(25014573/20000000000000)⟩
def e383 : ℝ := (2788243/100000000000000)
theorem h383 : Model (fun x => f383 ((111/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(5425656678480693/50000000000000),(14879151626537/50000000000000),(-108721882729/100000000000000),(388258813/100000000000000)⟩
def e384 : ℝ := (5784339/50000000000000)
theorem h384 : Model (fun x => f384 ((111/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3224072195201801/20000000000000),(14879151626537/50000000000000),(-108721882729/100000000000000),(388258813/100000000000000)⟩
def e385 : ℝ := (11568679/100000000000000)
theorem h385 : Model (fun x => f385 ((111/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(19958288388337383/100000000000000),(37142028184231/50000000000000),(-2275720093/1000000000000),(315313453/50000000000000)⟩
def e386 : ℝ := (30860117/100000000000000)
theorem h386 : Model (fun x => f386 ((111/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(5573500668512917/25000000000000),(37142028184231/50000000000000),(-2275720093/1000000000000),(315313453/50000000000000)⟩
def e387 : ℝ := (15430059/50000000000000)
theorem h387 : Model (fun x => f387 ((111/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(6900436897183651/25000000000000),(17968660870587/12500000000000),(-333375825857/100000000000000),(475687731/100000000000000)⟩
def e388 : ℝ := (7947467/12500000000000)
theorem h388 : Model (fun x => f388 ((111/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(7001032135278889/25000000000000),(17968660870587/12500000000000),(-333375825857/100000000000000),(475687731/100000000000000)⟩
def e389 : ℝ := (63579737/100000000000000)
theorem h389 : Model (fun x => f389 ((111/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(8667834335711433/25000000000000),(243015018270949/100000000000000),(-360442801739/100000000000000),(-411776673/100000000000000)⟩
def e390 : ℝ := (28156007/25000000000000)
theorem h390 : Model (fun x => f390 ((111/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(8663429573806671/25000000000000),(243015018270949/100000000000000),(-360442801739/100000000000000),(-411776673/100000000000000)⟩
def e391 : ℝ := (112624029/100000000000000)
theorem h391 : Model (fun x => f391 ((111/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(42904058072499027/100000000000000),(4766976541971/1250000000000),(-57564732719/25000000000000),(-2282030179/100000000000000)⟩
def e392 : ℝ := (90751881/50000000000000)
theorem h392 : Model (fun x => f392 ((111/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(1072684785145809/2500000000000),(4766976541971/1250000000000),(-57564732719/25000000000000),(-2282030179/100000000000000)⟩
def e393 : ℝ := (181503763/100000000000000)
theorem h393 : Model (fun x => f393 ((111/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(10215370109454991/100000000000000),(95224810260747/50000000000000),(199752611179/50000000000000),(-3044879757/100000000000000)⟩
def e394 : ℝ := (92674271/100000000000000)
theorem h394 : Model (fun x => f394 ((111/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(76642041888693/50000000000000),(57510901437/10000000000000),(-975104631/50000000000000),(1526801/25000000000000)⟩
def e395 : ℝ := (233357/100000000000000)
theorem h395 : Model (fun x => f395 ((111/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(223807949574083/100000000000000),(116129258329/50000000000000),(-502724069/50000000000000),(4352581/100000000000000)⟩
def e396 : ℝ := (81803/100000000000000)
theorem h396 : Model (fun x => f396 ((111/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(31306248932847/6250000000000),(519813023843/50000000000000),(-1980552769/50000000000000),(7406183/50000000000000)⟩
def e397 : ℝ := (396963/100000000000000)
theorem h397 : Model (fun x => f397 ((111/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1121053981202609/100000000000000),(3490148610847/100000000000000),(-57434693/500000000000),(4412553/12500000000000)⟩
def e398 : ℝ := (141977/10000000000000)
theorem h398 : Model (fun x => f398 ((111/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(501801585789637/20000000000000),(10414973390701/100000000000000),(-28874130737/100000000000000),(6602891/10000000000000)⟩
def e399 : ℝ := (4451043/100000000000000)
theorem h399 : Model (fun x => f399 ((111/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3845909815790193/100000000000000),(30394027308233/100000000000000),(-665858019/2000000000000),(-114729463/100000000000000)⟩
def e400 : ℝ := (14309709/100000000000000)
theorem h400 : Model (fun x => f400 ((111/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(123807949574083/12500000000000),(116129258329/6250000000000),(-502724069/6250000000000),(4352581/12500000000000)⟩
def e401 : ℝ := (81803/12500000000000)
theorem h401 : Model (fun x => f401 ((111/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(22874953607401/2000000000000),(1216588573817/50000000000000),(-4996897183/50000000000000),(10231963/25000000000000)⟩
def e402 : ℝ := (887781/100000000000000)
theorem h402 : Model (fun x => f402 ((111/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(24874953607401/2000000000000),(1216588573817/50000000000000),(-4996897183/50000000000000),(10231963/25000000000000)⟩
def e403 : ℝ := (887781/100000000000000)
theorem h403 : Model (fun x => f403 ((111/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(11958353530753647/25000000000000),(471602808373607/100000000000000),(-14722868769/25000000000000),(-925122151/25000000000000)⟩
def e404 : ℝ := (5642929/2500000000000)
theorem h404 : Model (fun x => f404 ((111/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(6533090011/3125000000000),(-2061169099/100000000000000),(10289511/50000000000000),(-189259/100000000000000)⟩
def e405 : ℝ := (2759/100000000000000)
theorem h405 : Model (fun x => f405 ((111/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (47361748496960141/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(21356138374639/100000000000000),(46898948063/25000000000000),(-988064321/100000000000000),(1314773/25000000000000)⟩
def e406 : ℝ := (17491/2500000000000)
theorem h406 : Model (fun x => f406 ((111/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2427372138207/5000000000000),(61553588671/12500000000000),(-368615011/20000000000000),(7893139/100000000000000)⟩
def e407 : ℝ := (42459/3125000000000)
theorem h407 : Model (fun x => f407 ((111/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(162190137645037/50000000000000),(4042975758091/100000000000000),(689974519/100000000000000),(53028839/50000000000000)⟩
def e408 : ℝ := (2074109/20000000000000)
theorem h408 : Model (fun x => f408 ((111/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(116893792897323/100000000000000),(403830967803/100000000000000),(-1694738681/50000000000000),(13750963/20000000000000)⟩
def e409 : ℝ := (5950193/100000000000000)
theorem h409 : Model (fun x => f409 ((111/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-52663631211/20000000000000),(10226201189/12500000000000),(-206681787/100000000000000),(-1292689/50000000000000)⟩
def e410 : ℝ := (39749493/100000000000000)
theorem h410 : Model (fun x => f410 ((111/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(22385608584960937/100000000000000),(238734415283203/25000000000000),(332667/2048000),(14097/10240000)⟩
def e411 : ℝ := (582031251/100000000000000)
theorem h411 : Model (fun x => f411 ((111/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(53361/1600),(231/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((111/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(12326391/64000),(160083/64000),(693/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((111/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(2155732532743634603/50000000000000),(119956956022303479/50000000000000),(1151894739968591/20000000000000),(19458561297821/25000000000000)⟩
def e414 : ℝ := (650459089597/100000000000000)
theorem h414 : Model (fun x => f414 ((111/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(2319397199/100000000000000),(-129064169/100000000000000),(102087/2500000000000),(-96689/100000000000000)⟩
def e415 : ℝ := (2847/100000000000000)
theorem h415 : Model (fun x => f415 ((111/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (1016428298759634603/25000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1086570832929/20000000000000),(-17463949383/100000000000000),(-23124111/20000000000000),(3264927/100000000000000)⟩
def e416 : ℝ := (633241/5000000000000)
theorem h416 : Model (fun x => f416 ((111/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(516953600859/10000000000000),(64345660129/100000000000000),(-161151171/50000000000000),(679549/100000000000000)⟩
def e417 : ℝ := (52414313/100000000000000)
theorem h417 : Model (fun x => f417 ((111/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((111/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((5169376160163/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/4) (14/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/4) (14/5) ≤ (5169480988789/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(111/40)-(1/40)) (by norm_num : ((111/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel35


noncomputable section
namespace Hf4Quad.Panel36
open Hf4Quad.Dag

def p0 : Cubic := ⟨(113/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((113/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((113/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((113/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((113/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(495047619047619/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((113/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-495047619047619/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((113/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-50452380952381/12500000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((113/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((113/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(12769/1600),(113/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((113/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(193224021164021/20000000000000),(1709947089947/10000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (3/100000000000000)
theorem h9 : Model (fun x => f9 ((113/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-193224021164021/20000000000000),(-1709947089947/10000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (3/100000000000000)
theorem h10 : Model (fun x => f10 ((113/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-1369739153439153/100000000000000),(-10740211640211/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((113/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((113/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1442897/64000),(38307/64000),(339/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((113/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1098246689380787/5000000000000),(145784958767361/25000000000000),(161266547309/3125000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((113/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1098246689380787/5000000000000),(-145784958767361/25000000000000),(-161266547309/3125000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((113/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-23334672941054893/100000000000000),(-302310129174933/50000000000000),(-5236190889549/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/12500000000000)
theorem h16 : Model (fun x => f16 ((113/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((113/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(163047361/2560000),(1442897/640000),(38307/1280000),(113/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((113/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(355857335515873/2000000000000),(157458998015873/25000000000000),(522540922619/6250000000000),(1973015873/4000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((113/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-5541806165261243/100000000000000),(12607866856813/50000000000000),(624892774471/20000000000000),(341025959/1000000000000)⟩
def e20 : ℝ := (21825399/20000000000000)
theorem h20 : Model (fun x => f20 ((113/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((113/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(8996265523925781/50000000000000),(199032423095703/25000000000000),(1442897/10240000),(12769/10240000)⟩
def e22 : ℝ := (69091797/12500000000000)
theorem h22 : Model (fun x => f22 ((113/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(117218007826558879/100000000000000),(162082422326547/3125000000000),(91798894061053/100000000000000),(40618979673/5000000000000)⟩
def e23 : ℝ := (450120263/12500000000000)
theorem h23 : Model (fun x => f23 ((113/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(27919050415324409/25000000000000),(521185324816313/10000000000000),(2966354935419/3125000000000),(10581027367/1250000000000)⟩
def e24 : ℝ := (3710089099/100000000000000)
theorem h24 : Model (fun x => f24 ((113/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((113/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(25414450105090331/50000000000000),(674719914294433/25000000000000),(5970972692871/10000000000000),(704539550781/100000000000000)⟩
def e26 : ℝ := (938544923/20000000000000)
theorem h26 : Model (fun x => f26 ((113/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(2282728597799013/2000000000000),(606034141008587/10000000000000),(67039174890329/50000000000000),(1582045425139/100000000000000)⟩
def e27 : ℝ := (10537525541/100000000000000)
theorem h27 : Model (fun x => f27 ((113/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(112906315775624143/50000000000000),(11272194658249/100000000000),(114500853857033/50000000000000),(2428527614499/100000000000000)⟩
def e28 : ℝ := (178095183/1250000000000)
theorem h28 : Model (fun x => f28 ((113/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((113/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(14359164309376037/10000000000000),(8895057536781609/100000000000000),(236151970003049/100000000000000),(1741533702087/50000000000000)⟩
def e30 : ℝ := (30987753923/100000000000000)
theorem h30 : Model (fun x => f30 ((113/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(34074524829392341/100000000000000),(2110811272617223/100000000000000),(1400980933153/2500000000000),(103317177961/12500000000000)⟩
def e31 : ℝ := (1470688639/20000000000000)
theorem h31 : Model (fun x => f31 ((113/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(259887156380640627/100000000000000),(13383005930866223/100000000000000),(142520472520093/50000000000000),(3255065038187/100000000000000)⟩
def e32 : ℝ := (4320211567/20000000000000)
theorem h32 : Model (fun x => f32 ((113/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((113/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(5477901/320),(48477/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((113/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((113/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(249617/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((113/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(9471773/320),(66149/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((113/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((113/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(10201373/320),(66149/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((113/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-10201373/320),(-66149/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((113/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((113/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(153/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((113/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(23409/1600),(153/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((113/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((113/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(491589/160),(3213/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((113/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(6509502857/20000000000000),(-53182213/12500000000000),(4171153/100000000000000),(-727/2000000000000)⟩
def e46 : ℝ := (61/20000000000000)
theorem h46 : Model (fun x => f46 ((113/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (242571/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-207518333402571/20000000000000),(5356513961/5000000000000),(-4436873/625000000000),(4706449/100000000000000)⟩
def e47 : ℝ := (9667349/50000000000000)
theorem h47 : Model (fun x => f47 ((113/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((113/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(193/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((113/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((113/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((113/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(160833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((113/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(260833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((113/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((113/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(26083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((113/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((113/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(547749999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((113/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((113/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((113/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(833036458333277/100000000000000),(14072916666643/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (137/100000000000000)
theorem h60 : Model (fun x => f60 ((113/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(4252126736111/2500000000000),(1086805555553/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((113/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((113/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(26083333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((113/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(147425173611109/10000000000000),(5253472222213/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((113/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(157425173611109/10000000000000),(5253472222213/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((113/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(262281818154999/2000000000000),(13265323694277/5000000000000),(13277251519/1000000000000),(539912471/25000000000000)⟩
def e66 : ℝ := (635563/100000000000000)
theorem h66 : Model (fun x => f66 ((113/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(46083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((113/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(53091840277777/10000000000000),(384027777777/20000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((113/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(305831121600109/25000000000000),(6636480034709/100000000000000),(2400173611/20000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (69/100000000000000)
theorem h69 : Model (fun x => f69 ((113/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(160427885243318351/100000000000000),(2057936541936901/50000000000000),(17711601405973/50000000000000),(147321466929/100000000000000)⟩
def e70 : ℝ := (330036871/100000000000000)
theorem h70 : Model (fun x => f70 ((113/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((113/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(89294661458331/312500000000),(22822916666613/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((113/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(8691347048610407/100000000000000),(21824414062459/12500000000000),(849479166657/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (111/6250000000000)
theorem h73 : Model (fun x => f73 ((113/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(53161688321846357/50000000000000),(678166680386037/25000000000000),(23021906799669/100000000000000),(23205993329/25000000000000)⟩
def e74 : ℝ := (48865439/25000000000000)
theorem h74 : Model (fun x => f74 ((113/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(53350252377402213/20000000000000),(136570796108359/2000000000000),(11689021922323/20000000000000),(48029088049/20000000000000)⟩
def e75 : ℝ := (525498627/100000000000000)
theorem h75 : Model (fun x => f75 ((113/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((113/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(29764887152777/312500000000),(7607638888871/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((113/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(925173611111/10000000000000),(253472222221/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((113/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(562813946759/20000000000000),(28911675347/25000000000000),(396050347/25000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/20000000000000)
theorem h79 : Model (fun x => f79 ((113/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(5360669956253/2000000000000),(159096866999/1250000000000),(224011210289/100000000000000),(1765598849/100000000000000)⟩
def e80 : ℝ := (2975149/50000000000000)
theorem h80 : Model (fun x => f80 ((113/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(77199231401247/12500000000000),(30443662057699/100000000000000),(569191452707/100000000000000),(5001614057/100000000000000)⟩
def e81 : ℝ := (21091947/100000000000000)
theorem h81 : Model (fun x => f81 ((113/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(267368855738221041/100000000000000),(6858983467475649/100000000000000),(29507150532161/50000000000000),(122573527151/50000000000000)⟩
def e82 : ℝ := (273295287/50000000000000)
theorem h82 : Model (fun x => f82 ((113/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(171189242139/20000000000000),(46901162229/100000000000000),(963722511/100000000000000),(4400559/50000000000000)⟩
def e83 : ℝ := (15073/50000000000000)
theorem h83 : Model (fun x => f83 ((113/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(260350305753/100000000000000),(8916106361/50000000000000),(488553773/100000000000000),(6692517/100000000000000)⟩
def e84 : ℝ := (2873/6250000000000)
theorem h84 : Model (fun x => f84 ((113/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(39594942333/50000000000000),(6508757643/100000000000000),(111451329/50000000000000),(4071281/100000000000000)⟩
def e85 : ℝ := (21031/50000000000000)
theorem h85 : Model (fun x => f85 ((113/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(6021730813/25000000000000),(2309704969/100000000000000),(94919381/100000000000000),(2167109/100000000000000)⟩
def e86 : ℝ := (5987/20000000000000)
theorem h86 : Model (fun x => f86 ((113/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(18065192439/25000000000000),(6929114907/100000000000000),(284758143/100000000000000),(6501327/100000000000000)⟩
def e87 : ℝ := (17961/20000000000000)
theorem h87 : Model (fun x => f87 ((113/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-18065192439/25000000000000),(-6929114907/100000000000000),(-284758143/100000000000000),(-6501327/100000000000000)⟩
def e88 : ℝ := (17961/20000000000000)
theorem h88 : Model (fun x => f88 ((113/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(53473756695490257/20000000000000),(3429488269180371/50000000000000),(59014016306179/100000000000000),(9805622119/4000000000000)⟩
def e89 : ℝ := (546680379/100000000000000)
theorem h89 : Model (fun x => f89 ((113/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(89294661458331/250000000000),(22822916666613/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((113/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(352342938010123/12500000000000),(637148169999/3125000000000),(55304000287/100000000000000),(520871/781250000000)⟩
def e91 : ℝ := (1897/6250000000000)
theorem h91 : Model (fun x => f91 ((113/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(1006794987739124447/100000000000000),(428613058362289/3125000000000),(1196298931851/1562500000000),(224367443949/100000000000000)⟩
def e92 : ℝ := (365018041/100000000000000)
theorem h92 : Model (fun x => f92 ((113/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(2483127181/25000000000000),(-67655529/50000000000000),(1088017/100000000000000),(-3373/50000000000000)⟩
def e93 : ℝ := (47/100000000000000)
theorem h93 : Model (fun x => f93 ((113/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (198600516401486149/20000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(531128554883/2000000000000),(79872228341/25000000000000),(-127590897/25000000000000),(1086249/100000000000000)⟩
def e94 : ℝ := (16881/5000000000000)
theorem h94 : Model (fun x => f94 ((113/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(160833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((113/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(7667731629393/20000000000000),(-12248772571/10000000000000),(195667293/50000000000000),(-1250271/100000000000000)⟩
def e96 : ℝ := (4011/100000000000000)
theorem h96 : Model (fun x => f96 ((113/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (32499999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(30830670926517/25000000000000),(48995090283/20000000000000),(-782669177/100000000000000),(1250269/50000000000000)⟩
def e97 : ℝ := (33813/100000000000000)
theorem h97 : Model (fun x => f97 ((113/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(647444089456857/25000000000000),(1028896895943/20000000000000),(-16436052717/100000000000000),(26255649/50000000000000)⟩
def e98 : ℝ := (710073/100000000000000)
theorem h98 : Model (fun x => f98 ((113/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(5830670926517/25000000000000),(48995090283/20000000000000),(-782669177/100000000000000),(1250269/50000000000000)⟩
def e99 : ℝ := (33813/100000000000000)
theorem h99 : Model (fun x => f99 ((113/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(302002674315309/50000000000000),(3772074083369/50000000000000),(-5749992909/50000000000000),(-3523203/100000000000000)⟩
def e100 : ℝ := (357881/25000000000000)
theorem h100 : Model (fun x => f100 ((113/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(38021210791167/25000000000000),(151055150553/25000000000000),(-26605751/2000000000000),(1166383/50000000000000)⟩
def e101 : ℝ := (101983/100000000000000)
theorem h101 : Model (fun x => f101 ((113/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(30830670926517/2500000000000),(48995090283/2000000000000),(-782669177/10000000000000),(1250269/5000000000000)⟩
def e102 : ℝ := (33813/10000000000000)
theorem h102 : Model (fun x => f102 ((113/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(346327920056337/25000000000000),(1526987558181/50000000000000),(-228924483/2500000000000),(13669073/50000000000000)⟩
def e103 : ℝ := (440113/100000000000000)
theorem h103 : Model (fun x => f103 ((113/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(371327920056337/25000000000000),(1526987558181/50000000000000),(-228924483/2500000000000),(13669073/50000000000000)⟩
def e104 : ℝ := (440113/100000000000000)
theorem h104 : Model (fun x => f104 ((113/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(8971361992396403/100000000000000),(6525014347137/5000000000000),(1069282577/25000000000000),(-37169179/4000000000000)⟩
def e105 : ℝ := (27008711/100000000000000)
theorem h105 : Model (fun x => f105 ((113/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(55830670926517/25000000000000),(48995090283/20000000000000),(-782669177/100000000000000),(1250269/50000000000000)⟩
def e106 : ℝ := (33813/100000000000000)
theorem h106 : Model (fun x => f106 ((113/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(124682552644201/25000000000000),(547085752521/50000000000000),(-180976619/6250000000000),(3666921/50000000000000)⟩
def e107 : ℝ := (169609/100000000000000)
theorem h107 : Model (fun x => f107 ((113/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(556888845356521/50000000000000),(366529975411/10000000000000),(-768954553/10000000000000),(2638351/20000000000000)⟩
def e108 : ℝ := (616321/100000000000000)
theorem h108 : Model (fun x => f108 ((113/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(99921028424420211/100000000000000),(891155195666183/50000000000000),(4141007454531/100000000000000),(-19044179829/100000000000000)⟩
def e109 : ℝ := (46893819/12500000000000)
theorem h109 : Model (fun x => f109 ((113/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(798445426614507/3125000000000),(3172158161613/3125000000000),(-558720771/250000000000),(24494043/6250000000000)⟩
def e110 : ℝ := (2141643/12500000000000)
theorem h110 : Model (fun x => f110 ((113/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(744875605659467/12500000000000),(86266486490897/100000000000000),(-3425150433/100000000000000),(-305837567/50000000000000)⟩
def e111 : ℝ := (8983953/50000000000000)
theorem h111 : Model (fun x => f111 ((113/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(66370066555190373/100000000000000),(235846454207777/20000000000000),(2665556365121/100000000000000),(-12785646649/100000000000000)⟩
def e112 : ℝ := (243031/97656250000)
theorem h112 : Model (fun x => f112 ((113/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(20786386872451323/12500000000000),(2961542662371251/100000000000000),(1701640954913/25000000000000),(-15914913239/50000000000000)⟩
def e113 : ℝ := (78001787/12500000000000)
theorem h113 : Model (fun x => f113 ((113/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(266148475538169/3125000000000),(1057386053871/3125000000000),(-186240257/250000000000),(8164681/6250000000000)⟩
def e114 : ℝ := (713881/12500000000000)
theorem h114 : Model (fun x => f114 ((113/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(1359868938133/25000000000000),(57134849691/50000000000000),(58762701/25000000000000),(-266831/10000000000000)⟩
def e115 : ℝ := (34357/100000000000000)
theorem h115 : Model (fun x => f115 ((113/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(1268631725031/100000000000000),(19988070419/50000000000000),(292179767/100000000000000),(-804843/100000000000000)⟩
def e116 : ℝ := (15523/100000000000000)
theorem h116 : Model (fun x => f116 ((113/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(54023103941817/50000000000000),(3833927179353/100000000000000),(37465611087/100000000000000),(274139/12500000000000)⟩
def e117 : ℝ := (73633/4000000000000)
theorem h117 : Model (fun x => f117 ((113/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(15080730693023/6250000000000),(8826715753767/100000000000000),(46107872097/50000000000000),(17343509/25000000000000)⟩
def e118 : ℝ := (217313/5000000000000)
theorem h118 : Model (fun x => f118 ((113/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(20816548333837369/12500000000000),(1485184689062509/50000000000000),(3449389781923/50000000000000),(-15880226221/50000000000000)⟩
def e119 : ℝ := (157090139/25000000000000)
theorem h119 : Model (fun x => f119 ((113/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(295878964623/100000000000000),(621567259/5000000000000),(9759169/6250000000000),(246899/100000000000000)⟩
def e120 : ℝ := (7377/100000000000000)
theorem h120 : Model (fun x => f120 ((113/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(69006915071/100000000000000),(724830829/20000000000000),(8069449/12500000000000),(175103/50000000000000)⟩
def e121 : ℝ := (431/20000000000000)
theorem h121 : Model (fun x => f121 ((113/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(16094264537/100000000000000),(1014300009/100000000000000),(1462143/6250000000000),(213183/100000000000000)⟩
def e122 : ℝ := (49/5000000000000)
theorem h122 : Model (fun x => f122 ((113/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(938403603/25000000000000),(13799449/5000000000000),(1953749/25000000000000),(49747/50000000000000)⟩
def e123 : ℝ := (121/20000000000000)
theorem h123 : Model (fun x => f123 ((113/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(2815210809/25000000000000),(41398347/5000000000000),(5861247/25000000000000),(149241/50000000000000)⟩
def e124 : ℝ := (363/20000000000000)
theorem h124 : Model (fun x => f124 ((113/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-2815210809/25000000000000),(-41398347/5000000000000),(-5861247/25000000000000),(-149241/50000000000000)⟩
def e125 : ℝ := (363/20000000000000)
theorem h125 : Model (fun x => f125 ((113/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(41633093852463929/25000000000000),(1485184275079039/50000000000000),(3449378059429/50000000000000),(-7940187731/25000000000000)⟩
def e126 : ℝ := (628362371/100000000000000)
theorem h126 : Model (fun x => f126 ((113/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(798445426614507/2500000000000),(3172158161613/2500000000000),(-558720771/200000000000),(24494043/5000000000000)⟩
def e127 : ℝ := (2141643/10000000000000)
theorem h127 : Model (fun x => f127 ((113/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(497463645883967/20000000000000),(5456963851167/50000000000000),(-1691060951/10000000000000),(1957189/20000000000000)⟩
def e128 : ℝ := (1940193/100000000000000)
theorem h128 : Model (fun x => f128 ((113/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(794395145926064141/100000000000000),(6641736992925153/100000000000000),(374705152589/25000000000000),(-9159032137/25000000000000)⟩
def e129 : ℝ := (1270392369/100000000000000)
theorem h129 : Model (fun x => f129 ((113/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(1573524217/12500000000000),(-52623353/50000000000000),(85619/10000000000000),(-319/5000000000000)⟩
def e130 : ℝ := (7/10000000000000)
theorem h130 : Model (fun x => f130 ((113/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (157550374441201543/20000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(4192683609951/20000000000000),(775960579/390625000000),(-33278109/4000000000000),(1774207/50000000000000)⟩
def e131 : ℝ := (74039/25000000000000)
theorem h131 : Model (fun x => f131 ((113/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(9503969158781/20000000000000),(129533705397/25000000000000),(-1342316313/100000000000000),(4634663/100000000000000)⟩
def e132 : ℝ := (39611/6250000000000)
theorem h132 : Model (fun x => f132 ((113/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-493061960134917/100000000000000),(-2662607794603/50000000000000),(884093641/6250000000000),(-10193729/20000000000000)⟩
def e133 : ℝ := (1987991/12500000000000)
theorem h133 : Model (fun x => f133 ((113/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(7079646017699/20000000000000),(-6265173467/2000000000000),(2772200649/100000000000000),(-98131/400000000000)⟩
def e134 : ℝ := (43809/20000000000000)
theorem h134 : Model (fun x => f134 ((113/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (14/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-87267603563701/50000000000000),(-42559088983/12500000000000),(2005072217/25000000000000),(-44509001/50000000000000)⟩
def e135 : ℝ := (8634823/100000000000000)
theorem h135 : Model (fun x => f135 ((113/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(163047361/256000),(1442897/64000),(38307/128000),(113/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((113/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((113/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(12986073/32000),(344763/32000),(3051/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((113/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(53387189/51200),(2132423/64000),(50511/128000),(131/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((113/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-12769/1600),(-113/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((113/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(52978581/51200),(2123383/64000),(50431/128000),(131/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((113/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((113/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(339/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((113/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-339/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((113/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(52110741/51200),(2113783/64000),(50431/128000),(131/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((113/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(52264341/51200),(2113783/64000),(50431/128000),(131/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((113/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((113/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(52264341/800),(2113783/1000),(50431/2000),(131/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((113/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((113/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(30815951229/512000),(272707533/128000),(7240023/256000),(21357/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((113/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(415369297/25000000000000),(-7351669/12500000000000),(65059/5000000000000),(-2303/10000000000000)⟩
def e151 : ℝ := (401/100000000000000)
theorem h151 : Model (fun x => f151 ((113/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (14855277717/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(108545012896691/100000000000000),(-33029912047/10000000000000),(2582958431/100000000000000),(-19502119/100000000000000)⟩
def e152 : ℝ := (51474041/100000000000000)
theorem h152 : Model (fun x => f152 ((113/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(233/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((113/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(44969/1600),(213/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((113/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(459/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((113/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(871459694989/20000000000000),(-1139163/4000000000),(37227549/20000000000000),(-1216587/100000000000000)⟩
def e156 : ℝ := (4003/50000000000000)
theorem h156 : Model (fun x => f156 ((113/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (114/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(30616149237469/25000000000000),(359708516657/100000000000000),(372275487/100000000000000),(-1216593/50000000000000)⟩
def e157 : ℝ := (435493/100000000000000)
theorem h157 : Model (fun x => f157 ((113/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(55616149237469/25000000000000),(359708516657/100000000000000),(372275487/100000000000000),(-1216593/50000000000000)⟩
def e158 : ℝ := (435493/100000000000000)
theorem h158 : Model (fun x => f158 ((113/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(55616149237469/50000000000000),(22481782291/12500000000000),(186137743/100000000000000),(-1216593/100000000000000)⟩
def e159 : ℝ := (54437/25000000000000)
theorem h159 : Model (fun x => f159 ((113/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(5616149237469/50000000000000),(22481782291/12500000000000),(186137743/100000000000000),(-1216593/100000000000000)⟩
def e160 : ℝ := (54437/25000000000000)
theorem h160 : Model (fun x => f160 ((113/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((113/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((113/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(410500149133699/100000000000000),(132749571623/20000000000000),(171734227/25000000000000),(-280613/6250000000000)⟩
def e163 : ℝ := (200899/25000000000000)
theorem h163 : Model (fun x => f163 ((113/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(172888402177999/6250000000000),(132749571623/20000000000000),(171734227/25000000000000),(-280613/6250000000000)⟩
def e164 : ℝ := (803597/100000000000000)
theorem h164 : Model (fun x => f164 ((113/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((113/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(192307743539183/6250000000000),(5713456454217/100000000000000),(3553421807/50000000000000),(-18088359/50000000000000)⟩
def e166 : ℝ := (6935021/100000000000000)
theorem h166 : Model (fun x => f166 ((113/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(208982621225197/2500000000000),(5713456454217/100000000000000),(3553421807/50000000000000),(-18088359/50000000000000)⟩
def e167 : ℝ := (3467511/50000000000000)
theorem h167 : Model (fun x => f167 ((113/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((113/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(929824692007841/10000000000000),(21389774673949/100000000000000),(33740821607/100000000000000),(-118522053/100000000000000)⟩
def e169 : ℝ := (26062649/100000000000000)
theorem h169 : Model (fun x => f169 ((113/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14567294539126029/100000000000000),(21389774673949/100000000000000),(33740821607/100000000000000),(-118522053/100000000000000)⟩
def e170 : ℝ := (521253/2000000000000)
theorem h170 : Model (fun x => f170 ((113/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((113/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(2025442067685501/12500000000000),(12498059390061/25000000000000),(51558172633/50000000000000),(-104280371/50000000000000)⟩
def e172 : ℝ := (489719/800000000000)
theorem h172 : Model (fun x => f172 ((113/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(18539250827198293/100000000000000),(12498059390061/25000000000000),(51558172633/50000000000000),(-104280371/50000000000000)⟩
def e173 : ℝ := (15303719/25000000000000)
theorem h173 : Model (fun x => f173 ((113/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((113/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(20621634815126617/100000000000000),(17790229394427/20000000000000),(239120392087/100000000000000),(-7160823/4000000000000)⟩
def e175 : ℝ := (109471873/100000000000000)
theorem h175 : Model (fun x => f175 ((113/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(21024015767507569/100000000000000),(17790229394427/20000000000000),(239120392087/100000000000000),(-7160823/4000000000000)⟩
def e176 : ℝ := (54735937/50000000000000)
theorem h176 : Model (fun x => f176 ((113/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((113/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(11692747984966023/50000000000000),(68377496463169/50000000000000),(465095162339/100000000000000),(7036723/5000000000000)⟩
def e178 : ℝ := (21112633/12500000000000)
theorem h178 : Model (fun x => f178 ((113/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(11683938461156499/50000000000000),(68377496463169/50000000000000),(465095162339/100000000000000),(7036723/5000000000000)⟩
def e179 : ℝ := (33780213/20000000000000)
theorem h179 : Model (fun x => f179 ((113/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((113/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(25992626605483349/100000000000000),(19414384363683/10000000000000),(806792156109/100000000000000),(963296331/100000000000000)⟩
def e181 : ℝ := (239908827/100000000000000)
theorem h181 : Model (fun x => f181 ((113/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(12997979969408341/50000000000000),(19414384363683/10000000000000),(806792156109/100000000000000),(963296331/100000000000000)⟩
def e182 : ℝ := (59977207/25000000000000)
theorem h182 : Model (fun x => f182 ((113/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(2919943811753199/100000000000000),(8570207116401/12500000000000),(48818556621/10000000000000),(1604360307/100000000000000)⟩
def e183 : ℝ := (10661221/12500000000000)
theorem h183 : Model (fun x => f183 ((113/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(7732890140011/6250000000000),(200056025443/50000000000000),(368783061/50000000000000),(-254617/12500000000000)⟩
def e184 : ℝ := (489233/100000000000000)
theorem h184 : Model (fun x => f184 ((113/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(105616149237469/50000000000000),(22481782291/12500000000000),(186137743/100000000000000),(-1216593/100000000000000)⟩
def e185 : ℝ := (54437/25000000000000)
theorem h185 : Model (fun x => f185 ((113/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(111547709797513/25000000000000),(379910283771/50000000000000),(138730201/12500000000000),(-2235061/50000000000000)⟩
def e186 : ℝ := (924729/100000000000000)
theorem h186 : Model (fun x => f186 ((113/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(942499165205761/100000000000000),(2407479673657/100000000000000),(4541443141/100000000000000),(-5730129/50000000000000)⟩
def e187 : ℝ := (2943461/100000000000000)
theorem h187 : Model (fun x => f187 ((113/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(62214457805351/3125000000000),(6780499533311/100000000000000),(3919324029/25000000000000),(-23024939/100000000000000)⟩
def e188 : ℝ := (8321891/100000000000000)
theorem h188 : Model (fun x => f188 ((113/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2463219544725141/100000000000000),(16354938656001/100000000000000),(3825653347/6250000000000),(1365529/3125000000000)⟩
def e189 : ℝ := (20218029/100000000000000)
theorem h189 : Model (fun x => f189 ((113/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((113/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(55616149237469/6250000000000),(22481782291/1562500000000),(186137743/12500000000000),(-1216593/12500000000000)⟩
def e191 : ℝ := (54437/3125000000000)
theorem h191 : Model (fun x => f191 ((113/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(1583725984437/156250000000),(183894611751/10000000000000),(1113334033/50000000000000),(-147121/1250000000000)⟩
def e192 : ℝ := (2231217/100000000000000)
theorem h192 : Model (fun x => f192 ((113/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1739975984437/156250000000),(183894611751/10000000000000),(1113334033/50000000000000),(-147121/1250000000000)⟩
def e193 : ℝ := (2231217/100000000000000)
theorem h193 : Model (fun x => f193 ((113/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(27430034254192551/100000000000000),(45484672661823/20000000000000),(518618217583/50000000000000),(1686486671/100000000000000)⟩
def e194 : ℝ := (281091001/100000000000000)
theorem h194 : Model (fun x => f194 ((113/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(45570486293/12500000000000),(-377826479/12500000000000),(5637499/50000000000000),(-1/62500000000)⟩
def e195 : ℝ := (4031/100000000000000)
theorem h195 : Model (fun x => f195 ((113/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (13600785843435299/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(5322530377993/50000000000000),(3233849533/2000000000000),(4577393/12500000000000),(-122343/10000000000000)⟩
def e196 : ℝ := (439637/100000000000000)
theorem h196 : Model (fun x => f196 ((113/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(30616149237469/12500000000000),(359708516657/50000000000000),(372275487/50000000000000),(-1216593/25000000000000)⟩
def e197 : ℝ := (435493/50000000000000)
theorem h197 : Model (fun x => f197 ((113/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(44950972591171/100000000000000),(-36341170449/50000000000000),(21150133/50000000000000),(272439/50000000000000)⟩
def e198 : ℝ := (45017/50000000000000)
theorem h198 : Model (fun x => f198 ((113/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (222104513289053/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(110098054817653/100000000000000),(2271323153/1562500000000),(-10575067/12500000000000),(-1089759/100000000000000)⟩
def e199 : ℝ := (310547/50000000000000)
theorem h199 : Model (fun x => f199 ((113/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(10098054817653/100000000000000),(2271323153/1562500000000),(-10575067/12500000000000),(-1089759/100000000000000)⟩
def e200 : ℝ := (310547/50000000000000)
theorem h200 : Model (fun x => f200 ((113/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(40631424992229/10000000000000),(536464897089/100000000000000),(-39027033/12500000000000),(-402173/10000000000000)⟩
def e201 : ℝ := (458427/20000000000000)
theorem h201 : Model (fun x => f201 ((113/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(110481141425463/4000000000000),(536464897089/100000000000000),(-39027033/12500000000000),(-402173/10000000000000)⟩
def e202 : ℝ := (286517/12500000000000)
theorem h202 : Model (fun x => f202 ((113/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1520469845622187/50000000000000),(2302825704153/50000000000000),(-1900604489/100000000000000),(-17717503/50000000000000)⟩
def e203 : ℝ := (19696497/100000000000000)
theorem h203 : Model (fun x => f203 ((113/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4161660321812663/50000000000000),(2302825704153/50000000000000),(-1900604489/100000000000000),(-17717503/50000000000000)⟩
def e204 : ℝ := (9848249/50000000000000)
theorem h204 : Model (fun x => f204 ((113/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(9163814124867639/100000000000000),(429247529509/2500000000000),(-9527781/390625000000),(-68188301/50000000000000)⟩
def e205 : ℝ := (73538519/100000000000000)
theorem h205 : Model (fun x => f205 ((113/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(7216430871957629/50000000000000),(429247529509/2500000000000),(-9527781/390625000000),(-68188301/50000000000000)⟩
def e206 : ℝ := (1838463/2500000000000)
theorem h206 : Model (fun x => f206 ((113/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15890300034571889/100000000000000),(39884010761211/100000000000000),(5031639511/50000000000000),(-20343927/6250000000000)⟩
def e207 : ℝ := (6848127/4000000000000)
theorem h207 : Model (fun x => f207 ((113/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(9113007160143087/50000000000000),(39884010761211/100000000000000),(5031639511/50000000000000),(-20343927/6250000000000)⟩
def e208 : ℝ := (21400397/12500000000000)
theorem h208 : Model (fun x => f208 ((113/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(20066487237421957/100000000000000),(14081141550281/20000000000000),(6704679247/12500000000000),(-36006597/6250000000000)⟩
def e209 : ℝ := (151552669/50000000000000)
theorem h209 : Model (fun x => f209 ((113/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(20468868189802909/100000000000000),(14081141550281/20000000000000),(6704679247/12500000000000),(-36006597/6250000000000)⟩
def e210 : ℝ := (303105339/100000000000000)
theorem h210 : Model (fun x => f210 ((113/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2816978215020293/12500000000000),(107269819825429/100000000000000),(18010254037/12500000000000),(-838936061/100000000000000)⟩
def e211 : ℝ := (115843169/25000000000000)
theorem h211 : Model (fun x => f211 ((113/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(351846979258489/1562500000000),(107269819825429/100000000000000),(18010254037/12500000000000),(-838936061/100000000000000)⟩
def e212 : ℝ := (463372677/100000000000000)
theorem h212 : Model (fun x => f212 ((113/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(24792107526289113/100000000000000),(30167100901801/20000000000000),(59102684721/20000000000000),(-1050352923/100000000000000)⟩
def e213 : ℝ := (326937963/50000000000000)
theorem h213 : Model (fun x => f213 ((113/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(12397720429811223/50000000000000),(30167100901801/20000000000000),(59102684721/20000000000000),(-1050352923/100000000000000)⟩
def e214 : ℝ := (653875927/100000000000000)
theorem h214 : Model (fun x => f214 ((113/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(625964302570851/25000000000000),(12818816408579/25000000000000),(228125582797/100000000000000),(-3715563/5000000000000)⟩
def e215 : ℝ := (225344423/100000000000000)
theorem h215 : Model (fun x => f215 ((113/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(121215816746309/100000000000000),(320087374089/100000000000000),(12510909/50000000000000),(-1322783/50000000000000)⟩
def e216 : ℝ := (343133/25000000000000)
theorem h216 : Model (fun x => f216 ((113/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(210098054817653/100000000000000),(2271323153/1562500000000),(-10575067/12500000000000),(-1089759/100000000000000)⟩
def e217 : ℝ := (310547/50000000000000)
theorem h217 : Model (fun x => f217 ((113/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(88282385276323/20000000000000),(610816737673/100000000000000),(-72089627/50000000000000),(-1206271/25000000000000)⟩
def e218 : ℝ := (8171/312500000000)
theorem h218 : Model (fun x => f218 ((113/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(927397871060903/100000000000000),(7519418463/390625000000),(211557143/100000000000000),(-7837037/50000000000000)⟩
def e219 : ℝ := (8256213/100000000000000)
theorem h219 : Model (fun x => f219 ((113/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(974222443759641/50000000000000),(107848717137/2000000000000),(98324881/4000000000000),(-44358333/100000000000000)⟩
def e220 : ℝ := (5793519/25000000000000)
theorem h220 : Model (fun x => f220 ((113/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2361823384258199/100000000000000),(12773211242433/100000000000000),(5181918839/25000000000000),(-12012411/12500000000000)⟩
def e221 : ℝ := (55266017/100000000000000)
theorem h221 : Model (fun x => f221 ((113/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(110098054817653/12500000000000),(2271323153/195312500000),(-10575067/1562500000000),(-1089759/12500000000000)⟩
def e222 : ℝ := (310547/6250000000000)
theorem h222 : Model (fun x => f222 ((113/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(1002000255287533/100000000000000),(59320193137/4000000000000),(-65178247/10000000000000),(-5681819/50000000000000)⟩
def e223 : ℝ := (1585321/25000000000000)
theorem h223 : Model (fun x => f223 ((113/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1102000255287533/100000000000000),(59320193137/4000000000000),(-65178247/10000000000000),(-5681819/50000000000000)⟩
def e224 : ℝ := (1585321/25000000000000)
theorem h224 : Model (fun x => f224 ((113/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(6506824930991501/25000000000000),(175786775327447/100000000000000),(402452424017/100000000000000),(-220652917/20000000000000)⟩
def e225 : ℝ := (763446351/100000000000000)
theorem h225 : Model (fun x => f225 ((113/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(38421196613/10000000000000),(-2594943897/100000000000000),(2317027/20000000000000),(-4367/20000000000000)⟩
def e226 : ℝ := (11569/100000000000000)
theorem h226 : Model (fun x => f226 ((113/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (6462777157375901/25000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(9620119016717/100000000000000),(33008004091/25000000000000),(-20500419/12500000000000),(-811653/100000000000000)⟩
def e227 : ℝ := (592263/50000000000000)
theorem h227 : Model (fun x => f227 ((113/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(20265179772703/100000000000000),(146862246507/50000000000000),(-7961513/6250000000000),(-2035083/100000000000000)⟩
def e228 : ℝ := (1624163/100000000000000)
theorem h228 : Model (fun x => f228 ((113/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(10998420998909/50000000000000),(251887578271/100000000000000),(-584997453/100000000000000),(1846409/100000000000000)⟩
def e229 : ℝ := (12404803/100000000000000)
theorem h229 : Model (fun x => f229 ((113/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(778649274259/10000000000000),(20256729099/100000000000000),(-193170917/50000000000000),(81451/2000000000000)⟩
def e230 : ℝ := (570377/12500000000000)
theorem h230 : Model (fun x => f230 ((113/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-41687178596203/25000000000000),(-64043196553/20000000000000),(3816973517/50000000000000),(-21236363/25000000000000)⟩
def e231 : ℝ := (13197839/100000000000000)
theorem h231 : Model (fun x => f231 ((113/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((113/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-12769/320),(-113/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((113/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2373/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((113/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1243/64),(-29/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((113/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((113/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2907/64),(-29/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((113/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((113/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(363375/32),(-725/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((113/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14351/1600),(7/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((113/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23951/1600),(7/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((113/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((113/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4526739/1600),(1323/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((113/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(17672766201/50000000000000),(-20660409/100000000000000),(74391/5000000000000),(-1733/100000000000000)⟩
def e244 : ℝ := (13/20000000000000)
theorem h244 : Model (fun x => f244 ((113/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (70686/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(401365088643023/100000000000000),(-14345336451/781250000000),(-9782628891/100000000000000),(-70954927/100000000000000)⟩
def e245 : ℝ := (1826291/100000000000000)
theorem h245 : Model (fun x => f245 ((113/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(1017/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((113/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(94129/1600),(473/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((113/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(127729/1600),(473/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((113/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(37249/1600),(193/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((113/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(4757777521/2560000),(21135237/640000),(265067/1280000),(333/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((113/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((113/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(210681/160),(1377/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((113/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(75944199999/100000000000000),(-992734641/100000000000000),(2433173/25000000000000),(-84817/100000000000000)⟩
def e253 : ℝ := (177/25000000000000)
theorem h253 : Model (fun x => f253 ((113/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (103959/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(5645712618837/4000000000000),(662962540527/100000000000000),(3222483/312500000000),(-1143383/50000000000000)⟩
def e254 : ℝ := (2683987/100000000000000)
theorem h254 : Model (fun x => f254 ((113/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(9645712618837/4000000000000),(662962540527/100000000000000),(3222483/312500000000),(-1143383/50000000000000)⟩
def e255 : ℝ := (2683987/100000000000000)
theorem h255 : Model (fun x => f255 ((113/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(60285703867731/50000000000000),(331481270263/100000000000000),(3222483/625000000000),(-1143383/100000000000000)⟩
def e256 : ℝ := (268399/20000000000000)
theorem h256 : Model (fun x => f256 ((113/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(10285703867731/50000000000000),(331481270263/100000000000000),(3222483/625000000000),(-1143383/100000000000000)⟩
def e257 : ℝ := (268399/20000000000000)
theorem h257 : Model (fun x => f257 ((113/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(444965909499919/100000000000000),(611661867747/50000000000000),(380559897/20000000000000),(-1054907/25000000000000)⟩
def e258 : ℝ := (4952603/100000000000000)
theorem h258 : Model (fun x => f258 ((113/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(700170048803551/25000000000000),(611661867747/50000000000000),(380559897/20000000000000),(-1054907/25000000000000)⟩
def e259 : ℝ := (1238151/25000000000000)
theorem h259 : Model (fun x => f259 ((113/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3376819537538051/100000000000000),(10758708936147/100000000000000),(20789552091/100000000000000),(-24495319/100000000000000)⟩
def e260 : ℝ := (43607507/100000000000000)
theorem h260 : Model (fun x => f260 ((113/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8659200489919003/100000000000000),(10758708936147/100000000000000),(20789552091/100000000000000),(-24495319/100000000000000)⟩
def e261 : ℝ := (10901877/25000000000000)
theorem h261 : Model (fun x => f261 ((113/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2610129982332841/25000000000000),(10418888649269/25000000000000),(105375962859/100000000000000),(-519637/12500000000000)⟩
def e262 : ℝ := (21146381/12500000000000)
theorem h262 : Model (fun x => f262 ((113/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(15709567548378983/100000000000000),(10418888649269/25000000000000),(105375962859/100000000000000),(-519637/12500000000000)⟩
def e263 : ℝ := (169171049/100000000000000)
theorem h263 : Model (fun x => f263 ((113/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(3788249348446769/20000000000000),(51161538460723/50000000000000),(17309902129/5000000000000),(94886703/25000000000000)⟩
def e264 : ℝ := (103992531/25000000000000)
theorem h264 : Model (fun x => f264 ((113/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(2127696102794813/10000000000000),(51161538460723/50000000000000),(17309902129/5000000000000),(94886703/25000000000000)⟩
def e265 : ℝ := (3327761/800000000000)
theorem h265 : Model (fun x => f265 ((113/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(12826965717361343/50000000000000),(6059422342851/3125000000000),(866301120969/100000000000000),(1889504449/100000000000000)⟩
def e266 : ℝ := (791710807/100000000000000)
theorem h266 : Model (fun x => f266 ((113/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(13028156193551819/50000000000000),(6059422342851/3125000000000),(866301120969/100000000000000),(1889504449/100000000000000)⟩
def e267 : ℝ := (98963851/12500000000000)
theorem h267 : Model (fun x => f267 ((113/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(31416462649080419/100000000000000),(80040395376417/25000000000000),(910802149801/50000000000000),(1462913891/25000000000000)⟩
def e268 : ℝ := (659003339/50000000000000)
theorem h268 : Model (fun x => f268 ((113/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(31398843601461371/100000000000000),(80040395376417/25000000000000),(910802149801/50000000000000),(1462913891/25000000000000)⟩
def e269 : ℝ := (1318006679/100000000000000)
theorem h269 : Model (fun x => f269 ((113/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(3785802774293801/10000000000000),(490104611467519/100000000000000),(3419501208229/100000000000000),(7192717963/50000000000000)⟩
def e270 : ℝ := (2044344993/100000000000000)
theorem h270 : Model (fun x => f270 ((113/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(37861361076271343/100000000000000),(490104611467519/100000000000000),(3419501208229/100000000000000),(7192717963/50000000000000)⟩
def e271 : ℝ := (1022172497/50000000000000)
theorem h271 : Model (fun x => f271 ((113/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(7788614961195281/100000000000000),(22632473858977/10000000000000),(1261628337827/50000000000000),(2560681/15625000000)⟩
def e272 : ℝ := (1001805939/100000000000000)
theorem h272 : Model (fun x => f272 ((113/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(14537464363311/10000000000000),(79934326787/10000000000000),(1171062061/50000000000000),(66103/10000000000000)⟩
def e273 : ℝ := (812493/25000000000000)
theorem h273 : Model (fun x => f273 ((113/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(110285703867731/50000000000000),(331481270263/100000000000000),(3222483/625000000000),(-1143383/100000000000000)⟩
def e274 : ℝ := (268399/20000000000000)
theorem h274 : Model (fun x => f274 ((113/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(243258729552017/50000000000000),(365576452099/25000000000000),(1686659341/50000000000000),(-203217/12500000000000)⟩
def e275 : ℝ := (2966981/50000000000000)
theorem h275 : Model (fun x => f275 ((113/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(134139801053071/12500000000000),(967628552093/20000000000000),(7398158579/50000000000000),(9572861/100000000000000)⟩
def e276 : ℝ := (98309/500000000000)
theorem h276 : Model (fun x => f276 ((113/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1183496190065227/50000000000000),(355718653167/2500000000000),(13551737863/25000000000000),(82837493/100000000000000)⟩
def e277 : ℝ := (28976367/50000000000000)
theorem h277 : Model (fun x => f277 ((113/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(688201347487503/20000000000000),(39605383216689/100000000000000),(30997198283/12500000000000),(112828219/12500000000000)⟩
def e278 : ℝ := (82066037/50000000000000)
theorem h278 : Model (fun x => f278 ((113/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(60285703867731/6250000000000),(331481270263/12500000000000),(3222483/78125000000),(-1143383/12500000000000)⟩
def e279 : ℝ := (268399/2500000000000)
theorem h279 : Model (fun x => f279 ((113/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(554972952758403/50000000000000),(1725596714987/50000000000000),(3233451181/50000000000000),(-4243017/50000000000000)⟩
def e280 : ℝ := (3496483/25000000000000)
theorem h280 : Model (fun x => f280 ((113/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(604972952758403/50000000000000),(1725596714987/50000000000000),(3233451181/50000000000000),(-4243017/50000000000000)⟩
def e281 : ℝ := (3496483/25000000000000)
theorem h281 : Model (fun x => f281 ((113/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(41634320128182643/100000000000000),(23918380441679/4000000000000),(458977958107/10000000000000),(10874352977/50000000000000)⟩
def e282 : ℝ := (2522279639/100000000000000)
theorem h282 : Model (fun x => f282 ((113/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(120093230407/50000000000000),(-107800021/3125000000000),(1441597/6250000000000),(-38227/50000000000000)⟩
def e283 : ℝ := (15347/100000000000000)
theorem h283 : Model (fun x => f283 ((113/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (8206349313314801/20000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(4676799655431/25000000000000),(68731316381/25000000000000),(49708237/100000000000000),(-1431319/100000000000000)⟩
def e284 : ℝ := (765933/20000000000000)
theorem h284 : Model (fun x => f284 ((113/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(5645712618837/2000000000000),(662962540527/50000000000000),(3222483/156250000000),(-1143383/25000000000000)⟩
def e285 : ℝ := (2683987/50000000000000)
theorem h285 : Model (fun x => f285 ((113/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(20734600739547/50000000000000),(-114009314823/100000000000000),(136106439/100000000000000),(253299/50000000000000)⟩
def e286 : ℝ := (467181/100000000000000)
theorem h286 : Model (fun x => f286 ((113/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (48095763353017/20000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(117061597041807/100000000000000),(228018629643/100000000000000),(-272212881/100000000000000),(-1013201/100000000000000)⟩
def e287 : ℝ := (1785959/50000000000000)
theorem h287 : Model (fun x => f287 ((113/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(17061597041807/100000000000000),(228018629643/100000000000000),(-272212881/100000000000000),(-1013201/100000000000000)⟩
def e288 : ℝ := (1785959/50000000000000)
theorem h288 : Model (fun x => f288 ((113/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(216006518350953/50000000000000),(420748661841/50000000000000),(-1004595157/100000000000000),(-747839/20000000000000)⟩
def e289 : ℝ := (6591041/50000000000000)
theorem h289 : Model (fun x => f289 ((113/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2787727322416191/100000000000000),(420748661841/50000000000000),(-1004595157/100000000000000),(-747839/20000000000000)⟩
def e290 : ℝ := (13182083/100000000000000)
theorem h290 : Model (fun x => f290 ((113/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3263358124791197/100000000000000),(7341607844923/100000000000000),(-427861083/6250000000000),(-37203771/100000000000000)⟩
def e291 : ℝ := (57540509/50000000000000)
theorem h291 : Model (fun x => f291 ((113/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8545739077172149/100000000000000),(7341607844923/100000000000000),(-427861083/6250000000000),(-37203771/100000000000000)⟩
def e292 : ℝ := (115081019/100000000000000)
theorem h292 : Model (fun x => f292 ((113/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(10003778642763497/100000000000000),(28080080528447/100000000000000),(-7268072607/50000000000000),(-165731293/100000000000000)⟩
def e293 : ℝ := (220314217/50000000000000)
theorem h293 : Model (fun x => f293 ((113/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(3818206565452779/25000000000000),(28080080528447/100000000000000),(-7268072607/50000000000000),(-165731293/100000000000000)⟩
def e294 : ℝ := (88125687/20000000000000)
theorem h294 : Model (fun x => f294 ((113/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(17878614335496603/100000000000000),(67695879867163/100000000000000),(543697071/10000000000000),(-458334843/100000000000000)⟩
def e295 : ℝ := (1063972411/100000000000000)
theorem h295 : Model (fun x => f295 ((113/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(2526791077651361/12500000000000),(67695879867163/100000000000000),(543697071/10000000000000),(-458334843/100000000000000)⟩
def e296 : ℝ := (265993103/25000000000000)
theorem h296 : Model (fun x => f296 ((113/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(473264318305371/2000000000000),(125338313217621/100000000000000),(105697816027/100000000000000),(-456612733/50000000000000)⟩
def e297 : ℝ := (7711471/390625000000)
theorem h297 : Model (fun x => f297 ((113/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(12032798433824751/50000000000000),(125338313217621/100000000000000),(105697816027/100000000000000),(-456612733/50000000000000)⟩
def e298 : ℝ := (1974136577/100000000000000)
theorem h298 : Model (fun x => f298 ((113/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(28171572030913587/100000000000000),(12599817209427/6250000000000),(86004150283/25000000000000),(-282609101/20000000000000)⟩
def e299 : ℝ := (3183188247/100000000000000)
theorem h299 : Model (fun x => f299 ((113/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(28153952983294539/100000000000000),(12599817209427/6250000000000),(86004150283/25000000000000),(-282609101/20000000000000)⟩
def e300 : ℝ := (397898531/12500000000000)
theorem h300 : Model (fun x => f300 ((113/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(32957466992644053/100000000000000),(300189013778101/100000000000000),(392875764729/50000000000000),(-425935259/25000000000000)⟩
def e301 : ℝ := (2376304417/50000000000000)
theorem h301 : Model (fun x => f301 ((113/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(16480400162988693/50000000000000),(300189013778101/100000000000000),(392875764729/50000000000000),(-425935259/25000000000000)⟩
def e302 : ℝ := (950521767/20000000000000)
theorem h302 : Model (fun x => f302 ((113/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(5623638933372869/100000000000000),(126373805117253/100000000000000),(728825091093/100000000000000),(174931059/50000000000000)⟩
def e303 : ℝ := (1009436487/50000000000000)
theorem h303 : Model (fun x => f303 ((113/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(137034175019783/100000000000000),(21353779953/4000000000000),(-58694269/50000000000000),(-3613531/100000000000000)⟩
def e304 : ℝ := (4191443/50000000000000)
theorem h304 : Model (fun x => f304 ((113/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(217061597041807/100000000000000),(228018629643/100000000000000),(-272212881/100000000000000),(-1013201/100000000000000)⟩
def e305 : ℝ := (1785959/50000000000000)
theorem h305 : Model (fun x => f305 ((113/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(471157369103397/100000000000000),(989881758111/100000000000000),(-6618143/1000000000000),(-5639933/100000000000000)⟩
def e306 : ℝ := (7763361/50000000000000)
theorem h306 : Model (fun x => f306 ((113/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(511350854977997/50000000000000),(50359058273/1562500000000),(-230990459/50000000000000),(-10609773/50000000000000)⟩
def e307 : ℝ := (50623847/100000000000000)
theorem h307 : Model (fun x => f307 ((113/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(2219892664604349/100000000000000),(4663900848751/50000000000000),(712457053/20000000000000),(-33124139/50000000000000)⟩
def e308 : ℝ := (36681389/25000000000000)
theorem h308 : Model (fun x => f308 ((113/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(95062862477039/3125000000000),(24633050973463/100000000000000),(6508950613/12500000000000),(-162931997/100000000000000)⟩
def e309 : ℝ := (97353977/25000000000000)
theorem h309 : Model (fun x => f309 ((113/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(117061597041807/12500000000000),(228018629643/12500000000000),(-272212881/12500000000000),(-1013201/12500000000000)⟩
def e310 : ℝ := (1785959/6250000000000)
theorem h310 : Model (fun x => f310 ((113/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1073526951354239/100000000000000),(2357993535969/100000000000000),(-1147545793/50000000000000),(-11719139/100000000000000)⟩
def e311 : ℝ := (3695823/10000000000000)
theorem h311 : Model (fun x => f311 ((113/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1173526951354239/100000000000000),(2357993535969/100000000000000),(-1147545793/50000000000000),(-11719139/100000000000000)⟩
def e312 : ℝ := (3695823/10000000000000)
theorem h312 : Model (fun x => f312 ((113/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(17849412990349897/50000000000000),(360805928988517/100000000000000),(1122103114957/100000000000000),(-401513617/25000000000000)⟩
def e313 : ℝ := (2860207617/50000000000000)
theorem h313 : Model (fun x => f313 ((113/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(350151571/125000000000),(-5529627/195312500000),(4952387/25000000000000),(-98621/100000000000000)⟩
def e314 : ℝ := (2879/6250000000000)
theorem h314 : Model (fun x => f314 ((113/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (17668445311063309/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(7876504029029/50000000000000),(194785167657/100000000000000),(-422244567/100000000000000),(-83121/50000000000000)⟩
def e315 : ℝ := (523273/6250000000000)
theorem h315 : Model (fun x => f315 ((113/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(17230103339891/50000000000000),(469710433181/100000000000000),(-37253633/10000000000000),(-1597561/100000000000000)⟩
def e316 : ℝ := (12202033/100000000000000)
theorem h316 : Model (fun x => f316 ((113/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(221297982539/160000000000),(4892555957/390625000000),(-337279557/2500000000000),(-17493193/25000000000000)⟩
def e317 : ℝ := (25052907/50000000000000)
theorem h317 : Model (fun x => f317 ((113/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(2447986532511/5000000000000),(2522217587/25000000000000),(-608115223/12500000000000),(18283281/100000000000000)⟩
def e318 : ℝ := (9332069/50000000000000)
theorem h318 : Model (fun x => f318 ((113/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-1840452870853/1562500000000),(-310127112417/100000000000000),(11076101/400000000000),(-66662171/100000000000000)⟩
def e319 : ℝ := (31861977/100000000000000)
theorem h319 : Model (fun x => f319 ((113/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((113/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-140459/1600),(-1243/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((113/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((113/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(10961/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((113/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(297981/1600),(697/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((113/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((113/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(470781/1600),(697/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((113/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2353905/32),(3485/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((113/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((113/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1095749047476749521/100000000000000),(128098924175813/20000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (141551/100000000000000)
theorem h329 : Model (fun x => f329 ((113/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9126177223/100000000000000),(-1066899/20000000000000),(384153/100000000000000),(-7/1562500000000)⟩
def e330 : ℝ := (19/100000000000000)
theorem h330 : Model (fun x => f330 ((113/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (273765700809987957/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(335658659314153/50000000000000),(1595392524729/100000000000000),(5705288907/50000000000000),(29943659/50000000000000)⟩
def e331 : ℝ := (2160417/100000000000000)
theorem h331 : Model (fun x => f331 ((113/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((113/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(473/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((113/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((113/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((113/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(815806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((113/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((113/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((113/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3619319460682739/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (219/20000000000000)
theorem h339 : Model (fun x => f339 ((113/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3914193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((113/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((113/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((113/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1102840269658501/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (547/50000000000000)
theorem h343 : Model (fun x => f343 ((113/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4533748120703/100000000000000),(-1447855193/25000000000000),(3698987/50000000000000),(-9451/100000000000000)⟩
def e344 : ℝ := (17/100000000000000)
theorem h344 : Model (fun x => f344 ((113/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2202862997681427/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(164090828030941/100000000000000),(796086770221/100000000000000),(-1016923189/100000000000000),(129899/10000000000000)⟩
def e345 : ℝ := (173/6250000000000)
theorem h345 : Model (fun x => f345 ((113/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(264090828030941/100000000000000),(796086770221/100000000000000),(-1016923189/100000000000000),(129899/10000000000000)⟩
def e346 : ℝ := (173/6250000000000)
theorem h346 : Model (fun x => f346 ((113/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(13204541401547/10000000000000),(39804338511/10000000000000),(-101692319/20000000000000),(129899/20000000000000)⟩
def e347 : ℝ := (693/50000000000000)
theorem h347 : Model (fun x => f347 ((113/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(3204541401547/10000000000000),(39804338511/10000000000000),(-101692319/20000000000000),(129899/20000000000000)⟩
def e348 : ℝ := (693/50000000000000)
theorem h348 : Model (fun x => f348 ((113/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(487310456485663/100000000000000),(58758785421/4000000000000),(-1876465411/100000000000000),(479389/20000000000000)⟩
def e349 : ℝ := (5117/100000000000000)
theorem h349 : Model (fun x => f349 ((113/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(710756185549987/25000000000000),(58758785421/4000000000000),(-1876465411/100000000000000),(479389/20000000000000)⟩
def e350 : ℝ := (2559/50000000000000)
theorem h350 : Model (fun x => f350 ((113/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3754083791400169/100000000000000),(6628089480179/50000000000000),(-173224047/1562500000000),(3346033/50000000000000)⟩
def e351 : ℝ := (74853/100000000000000)
theorem h351 : Model (fun x => f351 ((113/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(9036464743781121/100000000000000),(6628089480179/50000000000000),(-173224047/1562500000000),(3346033/50000000000000)⟩
def e352 : ℝ := (37427/50000000000000)
theorem h352 : Model (fun x => f352 ((113/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(11932237283287761/100000000000000),(26736613275627/50000000000000),(-7820611541/100000000000000),(-22001533/50000000000000)⟩
def e353 : ℝ := (49223/12500000000000)
theorem h353 : Model (fun x => f353 ((113/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(860064245116769/5000000000000),(26736613275627/50000000000000),(-7820611541/100000000000000),(-22001533/50000000000000)⟩
def e354 : ℝ := (78757/20000000000000)
theorem h354 : Model (fun x => f354 ((113/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(11356753932634643/50000000000000),(8692345005919/6250000000000),(115057954629/100000000000000),(-249402793/100000000000000)⟩
def e355 : ℝ := (972791/100000000000000)
theorem h355 : Model (fun x => f355 ((113/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(25049222150983571/100000000000000),(8692345005919/6250000000000),(115057954629/100000000000000),(-249402793/100000000000000)⟩
def e356 : ℝ := (121599/12500000000000)
theorem h356 : Model (fun x => f356 ((113/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(8269087274230269/25000000000000),(283352259004999/100000000000000),(23126077879/4000000000000),(-83161341/20000000000000)⟩
def e357 : ℝ := (231399/10000000000000)
theorem h357 : Model (fun x => f357 ((113/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(8369682512325507/25000000000000),(283352259004999/100000000000000),(23126077879/4000000000000),(-83161341/20000000000000)⟩
def e358 : ℝ := (2313991/100000000000000)
theorem h358 : Model (fun x => f358 ((113/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(22103563850361213/50000000000000),(253706766952709/50000000000000),(430265392689/25000000000000),(528947157/100000000000000)⟩
def e359 : ℝ := (6292979/100000000000000)
theorem h359 : Model (fun x => f359 ((113/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(22094754326551689/50000000000000),(253706766952709/50000000000000),(430265392689/25000000000000),(528947157/100000000000000)⟩
def e360 : ℝ := (314649/5000000000000)
theorem h360 : Model (fun x => f360 ((113/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(7293777456549037/12500000000000),(33836388708889/4000000000000),(4067622202909/100000000000000),(52560279/1000000000000)⟩
def e361 : ℝ := (6156281/50000000000000)
theorem h361 : Model (fun x => f361 ((113/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(58353552985725629/100000000000000),(33836388708889/4000000000000),(4067622202909/100000000000000),(52560279/1000000000000)⟩
def e362 : ℝ := (12312563/100000000000000)
theorem h362 : Model (fun x => f362 ((113/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(18699637647012433/100000000000000),(6291846610969/1250000000000),(1093467161163/25000000000000),(13953094377/100000000000000)⟩
def e363 : ℝ := (10548703/100000000000000)
theorem h363 : Model (fun x => f363 ((113/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(10897494601573/6250000000000),(1051196071659/100000000000000),(241584927/100000000000000),(-2332539/100000000000000)⟩
def e364 : ℝ := (11437/100000000000000)
theorem h364 : Model (fun x => f364 ((113/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(23204541401547/10000000000000),(39804338511/10000000000000),(-101692319/20000000000000),(129899/20000000000000)⟩
def e365 : ℝ := (693/50000000000000)
theorem h365 : Model (fun x => f365 ((113/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(134612685414027/25000000000000),(1847282841879/100000000000000),(-775338263/100000000000000),(-1033549/100000000000000)⟩
def e366 : ℝ := (14209/100000000000000)
theorem h366 : Model (fun x => f366 ((113/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(312362563186321/25000000000000),(401862667357/6250000000000),(704008761/25000000000000),(-11379999/100000000000000)⟩
def e367 : ℝ := (26173/50000000000000)
theorem h367 : Model (fun x => f367 ((113/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(289929201190013/10000000000000),(19893416325167/100000000000000),(25774909727/100000000000000),(-7955137/20000000000000)⟩
def e368 : ℝ := (78507/50000000000000)
theorem h368 : Model (fun x => f368 ((113/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2527601523845231/50000000000000),(65163387256673/100000000000000),(65266043439/25000000000000),(91012183/50000000000000)⟩
def e369 : ℝ := (285973/20000000000000)
theorem h369 : Model (fun x => f369 ((113/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(13204541401547/1250000000000),(39804338511/1250000000000),(-101692319/2500000000000),(129899/2500000000000)⟩
def e370 : ℝ := (693/6250000000000)
theorem h370 : Model (fun x => f370 ((113/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(19230050402327/1562500000000),(4235543152539/100000000000000),(-3826107833/100000000000000),(2863421/100000000000000)⟩
def e371 : ℝ := (901/4000000000000)
theorem h371 : Model (fun x => f371 ((113/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(20792550402327/1562500000000),(4235543152539/100000000000000),(-3826107833/100000000000000),(2863421/100000000000000)⟩
def e372 : ℝ := (901/4000000000000)
theorem h372 : Model (fun x => f372 ((113/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(13454152212876927/20000000000000),(1081259635442661/100000000000000),(6040647461411/100000000000000),(11131256531/100000000000000)⟩
def e373 : ℝ := (5163769/25000000000000)
theorem h373 : Model (fun x => f373 ((113/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(9290812087/6250000000000),(-2389336451/100000000000000),(6263987/25000000000000),(-26597/12500000000000)⟩
def e374 : ℝ := (1657/100000000000000)
theorem h374 : Model (fun x => f374 ((113/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (16545862407392239/25000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(27797571115741/100000000000000),(150722103821/50000000000000),(-83941261/10000000000000),(1282729/50000000000000)⟩
def e375 : ℝ := (16213/2500000000000)
theorem h375 : Model (fun x => f375 ((113/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(164090828030941/50000000000000),(796086770221/50000000000000),(-1016923189/50000000000000),(129899/5000000000000)⟩
def e376 : ℝ := (173/3125000000000)
theorem h376 : Model (fun x => f376 ((113/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(4733220041453/12500000000000),(-114144179369/100000000000000),(244944593/50000000000000),(-84101/4000000000000)⟩
def e377 : ℝ := (369/4000000000000)
theorem h377 : Model (fun x => f377 ((113/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (263293723035773/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(62134239668373/50000000000000),(45657671747/20000000000000),(-489889187/50000000000000),(2102523/50000000000000)⟩
def e378 : ℝ := (19747/25000000000000)
theorem h378 : Model (fun x => f378 ((113/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(12134239668373/50000000000000),(45657671747/20000000000000),(-489889187/50000000000000),(2102523/50000000000000)⟩
def e379 : ℝ := (19747/25000000000000)
theorem h379 : Model (fun x => f379 ((113/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(458609864218943/100000000000000),(421246376237/50000000000000),(-1807924381/50000000000000),(7759311/50000000000000)⟩
def e380 : ℝ := (145753/50000000000000)
theorem h380 : Model (fun x => f380 ((113/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(703581037483307/25000000000000),(421246376237/50000000000000),(-1807924381/50000000000000),(7759311/50000000000000)⟩
def e381 : ℝ := (291507/100000000000000)
theorem h381 : Model (fun x => f381 ((113/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(139892712989153/4000000000000),(7471727343387/100000000000000),(-3014418679/10000000000000),(121119257/100000000000000)⟩
def e382 : ℝ := (538631/20000000000000)
theorem h382 : Model (fun x => f382 ((113/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8779698777109777/100000000000000),(7471727343387/100000000000000),(-3014418679/10000000000000),(121119257/100000000000000)⟩
def e383 : ℝ := (673289/25000000000000)
theorem h383 : Model (fun x => f383 ((113/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2727599540165301/25000000000000),(5865606437991/20000000000000),(-26606057183/25000000000000),(377681393/100000000000000)⟩
def e384 : ℝ := (11182251/100000000000000)
theorem h384 : Model (fun x => f384 ((113/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(16179445779708823/100000000000000),(5865606437991/20000000000000),(-26606057183/25000000000000),(377681393/100000000000000)⟩
def e385 : ℝ := (2795563/25000000000000)
theorem h385 : Model (fun x => f385 ((113/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(20105951235557481/100000000000000),(18345322711191/25000000000000),(-223821998139/100000000000000),(619388219/100000000000000)⟩
def e386 : ℝ := (29871099/100000000000000)
theorem h386 : Model (fun x => f386 ((113/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(11220832760635883/50000000000000),(18345322711191/25000000000000),(-223821998139/100000000000000),(619388219/100000000000000)⟩
def e387 : ℝ := (298711/1000000000000)
theorem h387 : Model (fun x => f387 ((113/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(3485989560140407/12500000000000),(35605381035443/25000000000000),(-82624458641/25000000000000),(241726547/50000000000000)⟩
def e388 : ℝ := (15420347/25000000000000)
theorem h388 : Model (fun x => f388 ((113/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(1768143589594013/6250000000000),(35605381035443/25000000000000),(-82624458641/25000000000000),(241726547/50000000000000)⟩
def e389 : ℝ := (61681389/100000000000000)
theorem h389 : Model (fun x => f389 ((113/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(439449030255727/1250000000000),(241568517991393/100000000000000),(-362755089499/100000000000000),(-359503547/100000000000000)⟩
def e390 : ℝ := (109600001/100000000000000)
theorem h390 : Model (fun x => f390 ((113/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(4392287921604889/12500000000000),(241568517991393/100000000000000),(-362755089499/100000000000000),(-359503547/100000000000000)⟩
def e391 : ℝ := (54800001/50000000000000)
theorem h391 : Model (fun x => f391 ((113/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(21832917633079847/50000000000000),(380410179921397/100000000000000),(-60898731483/25000000000000),(-2164131509/100000000000000)⟩
def e392 : ℝ := (88649493/50000000000000)
theorem h392 : Model (fun x => f392 ((113/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(43669168599493027/100000000000000),(380410179921397/100000000000000),(-60898731483/25000000000000),(-2164131509/100000000000000)⟩
def e393 : ℝ := (177298987/100000000000000)
theorem h393 : Model (fun x => f393 ((113/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(10597843158096737/100000000000000),(38402278835621/20000000000000),(190727150947/50000000000000),(-594433743/20000000000000)⟩
def e394 : ℝ := (91682049/100000000000000)
theorem h394 : Model (fun x => f394 ((113/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(9651659347917/6250000000000),(113476188761/20000000000000),(-956977813/50000000000000),(5977653/100000000000000)⟩
def e395 : ℝ := (225561/100000000000000)
theorem h395 : Model (fun x => f395 ((113/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(112134239668373/50000000000000),(45657671747/20000000000000),(-489889187/50000000000000),(2102523/50000000000000)⟩
def e396 : ℝ := (19747/25000000000000)
theorem h396 : Model (fun x => f396 ((113/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(125740877060041/25000000000000),(40958306451/4000000000000),(-1936756187/50000000000000),(2877549/20000000000000)⟩
def e397 : ℝ := (383537/100000000000000)
theorem h397 : Model (fun x => f397 ((113/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(281997152887241/25000000000000),(344462141399/10000000000000),(-5638709421/50000000000000),(3454173/10000000000000)⟩
def e398 : ℝ := (1373287/100000000000000)
theorem h398 : Model (fun x => f398 ((113/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(316215363276567/12500000000000),(5150133376043/50000000000000),(-7119953633/25000000000000),(32701981/50000000000000)⟩
def e399 : ℝ := (1077929/25000000000000)
theorem h399 : Model (fun x => f399 ((113/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3906563797661757/100000000000000),(30259512242329/100000000000000),(-33956418079/100000000000000),(-106512437/100000000000000)⟩
def e400 : ℝ := (13947203/100000000000000)
theorem h400 : Model (fun x => f400 ((113/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(62134239668373/6250000000000),(45657671747/2500000000000),(-489889187/6250000000000),(2102523/6250000000000)⟩
def e401 : ℝ := (19747/3125000000000)
theorem h401 : Model (fun x => f401 ((113/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(7178589901629/625000000000),(478737562737/20000000000000),(-4876091309/50000000000000),(39618021/100000000000000)⟩
def e402 : ℝ := (171493/20000000000000)
theorem h402 : Model (fun x => f402 ((113/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(7803589901629/625000000000),(478737562737/20000000000000),(-4876091309/50000000000000),(39618021/100000000000000)⟩
def e403 : ℝ := (171493/20000000000000)
theorem h403 : Model (fun x => f403 ((113/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(12194088720601089/25000000000000),(471323460218391/100000000000000),(-80628116559/100000000000000),(-1772978637/50000000000000)⟩
def e404 : ℝ := (55246711/25000000000000)
theorem h404 : Model (fun x => f404 ((113/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(102508685039/50000000000000),(-49526813/2500000000000),(19481901/100000000000000),(-176623/100000000000000)⟩
def e405 : ℝ := (1/39062500000)
theorem h405 : Model (fun x => f405 ((113/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (6038118378390661/12500000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(21727419327721/100000000000000),(45926438019/25000000000000),(-239294019/25000000000000),(1259723/25000000000000)⟩
def e406 : ℝ := (67323/10000000000000)
theorem h406 : Model (fun x => f406 ((113/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(24762495221731/50000000000000),(242574979859/50000000000000),(-898294343/50000000000000),(152087/2000000000000)⟩
def e407 : ℝ := (5287/400000000000)
theorem h407 : Model (fun x => f407 ((113/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(332469837895973/100000000000000),(505876712039/12500000000000),(1330322769/100000000000000),(107404279/100000000000000)⟩
def e408 : ℝ := (10181919/100000000000000)
theorem h408 : Model (fun x => f408 ((113/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(58844219096631/50000000000000),(391080616451/100000000000000),(-2989979697/100000000000000),(8059901/12500000000000)⟩
def e409 : ℝ := (354289/6250000000000)
theorem h409 : Model (fun x => f409 ((113/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-10054554133/10000000000000),(40476752017/50000000000000),(-220954447/100000000000000),(-2182963/100000000000000)⟩
def e410 : ℝ := (37530601/100000000000000)
theorem h410 : Model (fun x => f410 ((113/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(12180784293457031/50000000000000),(255395587158203/25000000000000),(1749353/10240000),(14577/10240000)⟩
def e411 : ℝ := (147949219/25000000000000)
theorem h411 : Model (fun x => f411 ((113/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(54289/1600),(233/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((113/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(12649337/64000),(162867/64000),(699/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((113/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(601870490047831563/12500000000000),(263906796752388449/100000000000000),(6242282166111021/100000000000000),(83147933630493/100000000000000)⟩
def e414 : ℝ := (68510975269/10000000000000)
theorem h414 : Model (fun x => f414 ((113/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(51921469/2500000000000),(-28458009/25000000000000),(3546591/100000000000000),(-82677/100000000000000)⟩
def e415 : ℝ := (599/25000000000000)
theorem h415 : Model (fun x => f415 ((113/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (4544731008420769851/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2698744586703/50000000000000),(-3577742077/20000000000000),(-19423159/20000000000000),(2908771/100000000000000)⟩
def e416 : ℝ := (1181211/10000000000000)
theorem h416 : Model (fun x => f416 ((113/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1324235908019/25000000000000),(63064793649/100000000000000),(-159035121/50000000000000),(45363/6250000000000)⟩
def e417 : ℝ := (49342711/100000000000000)
theorem h417 : Model (fun x => f417 ((113/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((113/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((5296788265951/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (14/5) (57/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (14/5) (57/20) ≤ (5296886951373/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(113/40)-(1/40)) (by norm_num : ((113/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel36

