import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel10
open Hf4Quad.Dag

def p0 : Cubic := ⟨(61/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((61/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((61/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((61/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((61/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(53447619047619/20000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((61/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-53447619047619/20000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((61/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-43952380952381/25000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((61/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((61/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(3721/1600),(61/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((61/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(140767989417989/50000000000000),(9230687830687/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (3/100000000000000)
theorem h9 : Model (fun x => f9 ((61/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-140767989417989/50000000000000),(-9230687830687/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (3/100000000000000)
theorem h10 : Model (fun x => f10 ((61/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-228672751322751/50000000000000),(-13611640211639/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((61/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((61/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(226981/64000),(11163/64000),(183/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((61/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(431910822120949/12500000000000),(169932126736111/100000000000000),(696443142361/25000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((61/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-431910822120949/12500000000000),(-169932126736111/100000000000000),(-696443142361/25000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((61/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1956316039806547/50000000000000),(-734175067791/400000000000),(-572286789021/20000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/12500000000000)
theorem h16 : Model (fun x => f16 ((61/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((61/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(13845841/2560000),(226981/640000),(11163/1280000),(61/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((61/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(755477435515873/50000000000000),(99079007936507/100000000000000),(2436369047619/100000000000000),(13313492063/50000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((61/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-600419302145337/25000000000000),(-84464759011243/100000000000000),(-212532448743/50000000000000),(11404183201/100000000000000)⟩
def e20 : ℝ := (21825399/20000000000000)
theorem h20 : Model (fun x => f20 ((61/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((61/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(51550067199707/6250000000000),(16901661376953/25000000000000),(226981/10240000),(3721/10240000)⟩
def e22 : ℝ := (149414063/50000000000000)
theorem h22 : Model (fun x => f22 ((61/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(2686713131978803/50000000000000),(440444775734227/100000000000000),(2888162463831/20000000000000),(118367314091/50000000000000)⟩
def e23 : ℝ := (389361981/20000000000000)
theorem h23 : Model (fun x => f23 ((61/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(1485874527688129/50000000000000),(44497502090373/12500000000000),(14015747421669/100000000000000),(248138811383/100000000000000)⟩
def e24 : ℝ := (20559369/1000000000000)
theorem h24 : Model (fun x => f24 ((61/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((61/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(25156432793457/2000000000000),(1933127519989/1562500000000),(1014099682617/20000000000000),(55415283203/50000000000000)⟩
def e26 : ℝ := (1371630863/100000000000000)
theorem h26 : Model (fun x => f26 ((61/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(141222090972793/5000000000000),(277813949454673/100000000000000),(11385817600599/100000000000000),(248870330067/100000000000000)⟩
def e27 : ℝ := (3080000733/100000000000000)
theorem h27 : Model (fun x => f27 ((61/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(2898095437416059/50000000000000),(633793966177657/100000000000000),(6350391255567/25000000000000),(9940182829/2000000000000)⟩
def e28 : ℝ := (5135937633/100000000000000)
theorem h28 : Model (fun x => f28 ((61/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((61/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(239772250062637/12500000000000),(220118786942747/100000000000000),(10825514111937/100000000000000),(18486192131/6250000000000)⟩
def e30 : ℝ := (4896791999/100000000000000)
theorem h30 : Model (fun x => f30 ((61/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(91037336849179/20000000000000),(52234537536413/100000000000000),(1284455841059/50000000000000),(70188843773/100000000000000)⟩
def e31 : ℝ := (290504129/25000000000000)
theorem h31 : Model (fun x => f31 ((61/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(6251377559078013/100000000000000),(68602850371407/10000000000000),(13985238352193/50000000000000),(567197985223/100000000000000)⟩
def e32 : ℝ := (6297954149/100000000000000)
theorem h32 : Model (fun x => f32 ((61/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((61/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1596309/320),(26169/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((61/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((61/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(134749/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((61/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(3752293/320),(43841/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((61/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((61/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(4481893/320),(43841/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((61/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-4481893/320),(-43841/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((61/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((61/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(101/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((61/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(10201/1600),(101/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((61/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((61/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(214221/160),(2121/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((61/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(74689222811/100000000000000),(-92437157/6250000000000),(4393053/20000000000000),(-289971/100000000000000)⟩
def e46 : ℝ := (1847/50000000000000)
theorem h46 : Model (fun x => f46 ((61/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (104979/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-261522738196923/25000000000000),(249358487053/100000000000000),(-2520147599/100000000000000),(6366621/25000000000000)⟩
def e47 : ℝ := (25787603/25000000000000)
theorem h47 : Model (fun x => f47 ((61/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((61/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(141/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((61/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((61/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((61/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(58749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((61/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(108749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((61/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((61/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(108749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((61/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((61/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2283749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((61/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((61/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(8749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((61/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(7993124999999/4000000000000),(10281249999983/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (19/25000000000000)
theorem h60 : Model (fun x => f60 ((61/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(118265624999997/100000000000000),(453124999999/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (9/100000000000000)
theorem h61 : Model (fun x => f61 ((61/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((61/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(108749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((61/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1205765624999987/100000000000000),(2536458333329/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (39/100000000000000)
theorem h64 : Model (fun x => f64 ((61/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1305765624999987/100000000000000),(2536458333329/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (39/100000000000000)
theorem h65 : Model (fun x => f65 ((61/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1304643482665839/50000000000000),(144386142577883/100000000000000),(1001088867181/100000000000000),(2027994791/100000000000000)⟩
def e66 : ℝ := (317019/50000000000000)
theorem h66 : Model (fun x => f66 ((61/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(208749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((61/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(87153124999999/20000000000000),(173958333333/10000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (3/20000000000000)
theorem h68 : Model (fun x => f68 ((61/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(181932148437497/20000000000000),(544707031249/10000000000000),(10872395833/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (23/50000000000000)
theorem h69 : Model (fun x => f69 ((61/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(11867829587318723/50000000000000),(1455553751846103/100000000000000),(8627509567077/50000000000000),(44432435199/50000000000000)⟩
def e70 : ℝ := (23584977/10000000000000)
theorem h70 : Model (fun x => f70 ((61/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((61/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2483578124999937/12500000000000),(9515624999979/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (189/12500000000000)
theorem h72 : Model (fun x => f72 ((61/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1738504687499757/100000000000000),(48053906249917/50000000000000),(659895833329/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (741/100000000000000)
theorem h73 : Model (fun x => f73 ((61/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(7907247321637253/50000000000000),(15139884581253/1562500000000),(11426890568987/100000000000000),(719685957/1250000000000)⟩
def e74 : ℝ := (72541673/50000000000000)
theorem h74 : Model (fun x => f74 ((61/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(2471884613619497/6250000000000),(484901273009259/20000000000000),(28681909703141/100000000000000),(73219873479/50000000000000)⟩
def e75 : ℝ := (95233279/25000000000000)
theorem h75 : Model (fun x => f75 ((61/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((61/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(827859374999979/12500000000000),(3171874999993/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (63/12500000000000)
theorem h77 : Model (fun x => f77 ((61/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(765624999999/100000000000000),(36458333333/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((61/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(66992187499/100000000000000),(9570312499/100000000000000),(227864583/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((61/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(69325138091/1562500000000),(667828369073/100000000000000),(35104437889/100000000000000),(719672289/100000000000000)⟩
def e80 : ℝ := (1030381/25000000000000)
theorem h80 : Model (fun x => f80 ((61/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(9261838448957/100000000000000),(141257842393/10000000000000),(76063132297/100000000000000),(824292197/50000000000000)⟩
def e81 : ℝ := (2904873/25000000000000)
theorem h81 : Model (fun x => f81 ((61/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(39559415656360909/100000000000000),(97036757738809/4000000000000),(14378986417719/50000000000000),(18511041419/12500000000000)⟩
def e82 : ℝ := (12267269/3125000000000)
theorem h82 : Model (fun x => f82 ((61/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(2930908203/50000000000000),(558268229/50000000000000),(19938151/25000000000000),(632957/25000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((61/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(102581787/20000000000000),(4884847/4000000000000),(2907647/25000000000000),(553837/100000000000000)⟩
def e84 : ℝ := (6657/50000000000000)
theorem h84 : Model (fun x => f84 ((61/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(44879531/100000000000000),(12822723/100000000000000),(763257/50000000000000),(96921/100000000000000)⟩
def e85 : ℝ := (3531/100000000000000)
theorem h85 : Model (fun x => f85 ((61/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1963479/50000000000000),(654493/50000000000000),(186997/100000000000000),(14841/100000000000000)⟩
def e86 : ℝ := (73/10000000000000)
theorem h86 : Model (fun x => f86 ((61/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(5890437/50000000000000),(1963479/50000000000000),(560991/100000000000000),(44523/100000000000000)⟩
def e87 : ℝ := (219/10000000000000)
theorem h87 : Model (fun x => f87 ((61/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-5890437/50000000000000),(-1963479/50000000000000),(-560991/100000000000000),(-44523/100000000000000)⟩
def e88 : ℝ := (219/10000000000000)
theorem h88 : Model (fun x => f88 ((61/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(7911883128916007/20000000000000),(2425918939543267/100000000000000),(28757972274447/100000000000000),(148088286829/100000000000000)⟩
def e89 : ℝ := (196277399/50000000000000)
theorem h89 : Model (fun x => f89 ((61/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2483578124999937/10000000000000),(9515624999979/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (189/10000000000000)
theorem h90 : Model (fun x => f90 ((61/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(379783359863273/20000000000000),(3790253092441/25000000000000),(45392252603/100000000000000),(30201099/50000000000000)⟩
def e91 : ℝ := (30267/100000000000000)
theorem h91 : Model (fun x => f91 ((61/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(471610822397701943/100000000000000),(3689615950565457/50000000000000),(23524978195401/50000000000000),(156663012761/100000000000000)⟩
def e92 : ℝ := (11531067/4000000000000)
theorem h92 : Model (fun x => f92 ((61/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(5300980981/25000000000000),(-165887491/50000000000000),(1537921/50000000000000),(-2759/12500000000000)⟩
def e93 : ℝ := (21/12500000000000)
theorem h93 : Model (fun x => f93 ((61/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (464184383588890791/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(1677629679611/20000000000000),(47892720283/12500000000000),(-733988441/100000000000000),(1874649/100000000000000)⟩
def e94 : ℝ := (299183/100000000000000)
theorem h94 : Model (fun x => f94 ((61/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(58749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((61/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(45977011494253/100000000000000),(-88078566081/50000000000000),(33746577/5000000000000),(-517189/20000000000000)⟩
def e96 : ℝ := (9949/100000000000000)
theorem h96 : Model (fun x => f96 ((61/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (10833333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(27011494252873/25000000000000),(352314264323/100000000000000),(-337465771/25000000000000),(323243/6250000000000)⟩
def e97 : ℝ := (16663/25000000000000)
theorem h97 : Model (fun x => f97 ((61/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(567241379310333/25000000000000),(7398599550783/100000000000000),(-7086781191/25000000000000),(6788103/6250000000000)⟩
def e98 : ℝ := (349923/25000000000000)
theorem h98 : Model (fun x => f98 ((61/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(2011494252873/25000000000000),(352314264323/100000000000000),(-337465771/25000000000000),(323243/6250000000000)⟩
def e99 : ℝ := (16663/25000000000000)
theorem h99 : Model (fun x => f99 ((61/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(91280221957959/50000000000000),(8589178788839/100000000000000),(-6842409471/100000000000000),(-36827433/50000000000000)⟩
def e100 : ℝ := (2785713/100000000000000)
theorem h100 : Model (fun x => f100 ((61/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(58369665741839/50000000000000),(761322778077/100000000000000),(-1675692107/100000000000000),(1664513/100000000000000)⟩
def e101 : ℝ := (199307/100000000000000)
theorem h101 : Model (fun x => f101 ((61/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(27011494252873/2500000000000),(352314264323/10000000000000),(-337465771/2500000000000),(323243/625000000000)⟩
def e102 : ℝ := (16663/2500000000000)
theorem h102 : Model (fun x => f102 ((61/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(598599550799299/50000000000000),(4284465421307/100000000000000),(-15174322947/100000000000000),(53383393/100000000000000)⟩
def e103 : ℝ := (865827/100000000000000)
theorem h103 : Model (fun x => f103 ((61/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(648599550799299/50000000000000),(4284465421307/100000000000000),(-15174322947/100000000000000),(53383393/100000000000000)⟩
def e104 : ℝ := (865827/100000000000000)
theorem h104 : Model (fun x => f104 ((61/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(23681724383517/1000000000000),(59620244588039/50000000000000),(251538409663/100000000000000),(-2454503697/100000000000000)⟩
def e105 : ℝ := (40386439/100000000000000)
theorem h105 : Model (fun x => f105 ((61/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(52011494252873/25000000000000),(352314264323/100000000000000),(-337465771/25000000000000),(323243/6250000000000)⟩
def e106 : ℝ := (16663/25000000000000)
theorem h106 : Model (fun x => f106 ((61/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(216415642753331/50000000000000),(1465951306723/100000000000000),(-175016731/4000000000000),(12008289/100000000000000)⟩
def e107 : ℝ := (332611/100000000000000)
theorem h107 : Model (fun x => f107 ((61/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(180097615348747/20000000000000),(4574779077877/100000000000000),(-9780755877/100000000000000),(12164753/100000000000000)⟩
def e108 : ℝ := (1160209/100000000000000)
theorem h108 : Model (fun x => f108 ((61/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(5331277611022109/25000000000000),(1182085044919249/100000000000000),(7488437173689/100000000000000),(-10984862711/50000000000000)⟩
def e109 : ℝ := (517044887/100000000000000)
theorem h109 : Model (fun x => f109 ((61/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1225762980578619/6250000000000),(15987778339617/12500000000000),(-35189534247/12500000000000),(34954773/12500000000000)⟩
def e110 : ℝ := (4185447/12500000000000)
theorem h110 : Model (fun x => f110 ((61/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1577993722123757/100000000000000),(39693794498369/50000000000000),(40807275717/25000000000000),(-420376473/25000000000000)⟩
def e111 : ℝ := (6847117/25000000000000)
theorem h111 : Model (fun x => f111 ((61/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(14209645319489097/100000000000000),(787065499979877/100000000000000),(123683142681/2500000000000),(-7623568229/50000000000000)⟩
def e112 : ℝ := (43816747/12500000000000)
theorem h112 : Model (fun x => f112 ((61/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(35534755763577533/100000000000000),(984575272449563/50000000000000),(12435762880929/100000000000000),(-930421547/2500000000000)⟩
def e113 : ℝ := (867578863/100000000000000)
theorem h113 : Model (fun x => f113 ((61/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(408587660192873/6250000000000),(5329259446539/12500000000000),(-11729844749/12500000000000),(11651591/12500000000000)⟩
def e114 : ℝ := (1395149/12500000000000)
theorem h114 : Model (fun x => f114 ((61/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(323688730347/50000000000000),(56694249431/100000000000000),(1024034061/100000000000000),(-8679263/100000000000000)⟩
def e115 : ℝ := (66003/100000000000000)
theorem h115 : Model (fun x => f115 ((61/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(10417568333/20000000000000),(3421204707/50000000000000),(273396763/100000000000000),(2177673/100000000000000)⟩
def e116 : ℝ := (9531/20000000000000)
theorem h116 : Model (fun x => f116 ((61/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(3405191896063/100000000000000),(469523018187/100000000000000),(2592670801/12500000000000),(252551153/100000000000000)⟩
def e117 : ℝ := (3822419/100000000000000)
theorem h117 : Model (fun x => f117 ((61/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(44277279683/625000000000),(494410363629/50000000000000),(5594976191/12500000000000),(592335501/100000000000000)⟩
def e118 : ℝ := (2151233/25000000000000)
theorem h118 : Model (fun x => f118 ((61/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(35541840128326813/100000000000000),(123133710351649/6250000000000),(12480522690457/100000000000000),(-36624526379/100000000000000)⟩
def e119 : ℝ := (175236759/20000000000000)
theorem h119 : Model (fun x => f119 ((61/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(2095487883/50000000000000),(2867389/390625000000),(4540111/10000000000000),(1048761/100000000000000)⟩
def e120 : ℝ := (2099/25000000000000)
theorem h120 : Model (fun x => f120 ((61/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(168602473/50000000000000),(73827027/100000000000000),(3091279/50000000000000),(46929/20000000000000)⟩
def e121 : ℝ := (3843/100000000000000)
theorem h121 : Model (fun x => f121 ((61/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(3391429/12500000000000),(3564063/50000000000000),(376499/50000000000000),(19841/50000000000000)⟩
def e122 : ℝ := (269/25000000000000)
theorem h122 : Model (fun x => f122 ((61/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(545747/25000000000000),(133823/20000000000000),(85333/100000000000000),(23/400000000000)⟩
def e123 : ℝ := (7/3125000000000)
theorem h123 : Model (fun x => f123 ((61/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(1637241/25000000000000),(401469/20000000000000),(255999/100000000000000),(69/400000000000)⟩
def e124 : ℝ := (21/3125000000000)
theorem h124 : Model (fun x => f124 ((61/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-1637241/25000000000000),(-401469/20000000000000),(-255999/100000000000000),(-69/400000000000)⟩
def e125 : ℝ := (21/3125000000000)
theorem h125 : Model (fun x => f125 ((61/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(35541840121777849/100000000000000),(1970139363619039/100000000000000),(6240261217229/50000000000000),(-36624543629/100000000000000)⟩
def e126 : ℝ := (876184467/100000000000000)
theorem h126 : Model (fun x => f126 ((61/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1225762980578619/5000000000000),(15987778339617/10000000000000),(-35189534247/10000000000000),(34954773/10000000000000)⟩
def e127 : ℝ := (4185447/10000000000000)
theorem h127 : Model (fun x => f127 ((61/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1873429217133497/100000000000000),(6345095885791/50000000000000),(-3277245199/20000000000000),(-24331739/100000000000000)⟩
def e128 : ℝ := (3433281/100000000000000)
theorem h128 : Model (fun x => f128 ((61/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(28704752263707801/6250000000000),(6106230563858979/100000000000000),(193583226207/2000000000000),(-70270588381/100000000000000)⟩
def e129 : ℝ := (42493977/2500000000000)
theorem h129 : Model (fun x => f129 ((61/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(4354679631/20000000000000),(-289484709/100000000000000),(1694963/50000000000000),(-17819/50000000000000)⟩
def e130 : ℝ := (9/2000000000000)
theorem h130 : Model (fun x => f130 ((61/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (226580027261904013/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(483666647583/6250000000000),(326078095399/100000000000000),(-445244071/25000000000000),(10016253/100000000000000)⟩
def e131 : ℝ := (270461/50000000000000)
theorem h131 : Model (fun x => f131 ((61/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(16126814759383/100000000000000),(709219857663/100000000000000),(-100598589/4000000000000),(5945451/50000000000000)⟩
def e132 : ℝ := (168021/20000000000000)
theorem h132 : Model (fun x => f132 ((61/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-10543821885671/6250000000000),(-7378871185093/100000000000000),(13835449413/50000000000000),(-144427383/100000000000000)⟩
def e133 : ℝ := (5286803/20000000000000)
theorem h133 : Model (fun x => f133 ((61/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(65573770491803/100000000000000),(-33593120129/3125000000000),(3524524079/20000000000000),(-288895417/100000000000000)⟩
def e134 : ℝ := (2407463/50000000000000)
theorem h134 : Model (fun x => f134 ((61/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (3/2))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-110623705029991/100000000000000),(-756275173663/25000000000000),(16934166589/25000000000000),(-1205143633/100000000000000)⟩
def e135 : ℝ := (26977037/50000000000000)
theorem h135 : Model (fun x => f135 ((61/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(13845841/256000),(226981/64000),(11163/128000),(61/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((61/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((61/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(2042829/32000),(100467/32000),(1647/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((61/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(30188473/256000),(85583/12800),(17751/128000),(79/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((61/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-3721/1600),(-61/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((61/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(29593113/256000),(84607/12800),(17671/128000),(79/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((61/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((61/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(183/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((61/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-183/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((61/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(27250713/256000),(82687/12800),(17671/128000),(79/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((61/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(28018713/256000),(82687/12800),(17671/128000),(79/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((61/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((61/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(28018713/4000),(82687/200),(17671/2000),(79/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((61/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((61/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(2616863949/512000),(42899409/128000),(2109807/256000),(11529/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((61/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1222837741/6250000000000),(-1282977303/100000000000000),(13145259/25000000000000),(-1723969/100000000000000)⟩
def e151 : ℝ := (29089/50000000000000)
theorem h151 : Model (fun x => f151 ((61/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (1220500197/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(137049358842589/100000000000000),(-897820466363/100000000000000),(2151128747/20000000000000),(-31771649/25000000000000)⟩
def e152 : ℝ := (199513579/25000000000000)
theorem h152 : Model (fun x => f152 ((61/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(181/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((61/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(25521/1600),(161/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((61/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(303/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((61/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3300330033003/50000000000000),(-65353069961/100000000000000),(323530049/50000000000000),(-800817/12500000000000)⟩
def e156 : ℝ := (16017/25000000000000)
theorem h156 : Model (fun x => f156 ((61/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := 15)
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(13160581683167/12500000000000),(285960526737/100000000000000),(1294120187/100000000000000),(-6406539/50000000000000)⟩
def e157 : ℝ := (240471/12500000000000)
theorem h157 : Model (fun x => f157 ((61/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(25660581683167/12500000000000),(285960526737/100000000000000),(1294120187/100000000000000),(-6406539/50000000000000)⟩
def e158 : ℝ := (240471/12500000000000)
theorem h158 : Model (fun x => f158 ((61/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(25660581683167/25000000000000),(17872532921/12500000000000),(647060093/100000000000000),(-6406539/100000000000000)⟩
def e159 : ℝ := (192377/20000000000000)
theorem h159 : Model (fun x => f159 ((61/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(660581683167/25000000000000),(17872532921/12500000000000),(647060093/100000000000000),(-6406539/100000000000000)⟩
def e160 : ℝ := (192377/20000000000000)
theorem h160 : Model (fun x => f160 ((61/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((61/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((61/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(378799062941989/100000000000000),(527665257667/100000000000000),(2387959867/100000000000000),(-1182159/5000000000000)⟩
def e163 : ℝ := (709963/20000000000000)
theorem h163 : Model (fun x => f163 ((61/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(1367256674328137/50000000000000),(527665257667/100000000000000),(2387959867/100000000000000),(-1182159/5000000000000)⟩
def e164 : ℝ := (443727/12500000000000)
theorem h164 : Model (fun x => f164 ((61/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((61/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2806768125876193/100000000000000),(4451422285571/100000000000000),(130621621/625000000000),(-24078369/12500000000000)⟩
def e166 : ℝ := (15004577/50000000000000)
theorem h166 : Model (fun x => f166 ((61/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1617829815651429/20000000000000),(4451422285571/100000000000000),(130621621/625000000000),(-24078369/12500000000000)⟩
def e167 : ℝ := (6001831/20000000000000)
theorem h167 : Model (fun x => f167 ((61/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((61/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(83028908267973/1000000000000),(1008433128933/6250000000000),(80158002217/100000000000000),(-657265797/100000000000000)⟩
def e169 : ℝ := (218249/200000000000)
theorem h169 : Model (fun x => f169 ((61/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13571938445844919/100000000000000),(1008433128933/6250000000000),(80158002217/100000000000000),(-657265797/100000000000000)⟩
def e170 : ℝ := (109124501/100000000000000)
theorem h170 : Model (fun x => f170 ((61/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((61/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(557222136141629/4000000000000),(35966460967289/100000000000000),(38632880313/20000000000000),(-1325111621/100000000000000)⟩
def e172 : ℝ := (122165649/50000000000000)
theorem h172 : Model (fun x => f172 ((61/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(1626626768925501/10000000000000),(35966460967289/100000000000000),(38632880313/20000000000000),(-1325111621/100000000000000)⟩
def e173 : ℝ := (244331299/100000000000000)
theorem h173 : Model (fun x => f173 ((61/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((61/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(4174018907203883/25000000000000),(30087182381231/50000000000000),(177472951819/50000000000000),(-946659299/50000000000000)⟩
def e175 : ℝ := (102729723/25000000000000)
theorem h175 : Model (fun x => f175 ((61/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(4274614145299121/25000000000000),(30087182381231/50000000000000),(177472951819/50000000000000),(-946659299/50000000000000)⟩
def e176 : ℝ := (410918893/100000000000000)
theorem h176 : Model (fun x => f176 ((61/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((61/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(17550253670315069/100000000000000),(86211786340451/100000000000000),(560999488409/100000000000000),(-2141898663/100000000000000)⟩
def e178 : ℝ := (36982327/6250000000000)
theorem h178 : Model (fun x => f178 ((61/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(17532634622696021/100000000000000),(86211786340451/100000000000000),(560999488409/100000000000000),(-2141898663/100000000000000)⟩
def e179 : ℝ := (591717233/100000000000000)
theorem h179 : Model (fun x => f179 ((61/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((61/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(17995904114272523/100000000000000),(22711598115303/20000000000000),(20313386223/2500000000000),(-15326321/781250000000)⟩
def e181 : ℝ := (782686323/100000000000000)
theorem h181 : Model (fun x => f181 ((61/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(562476170237683/3125000000000),(22711598115303/20000000000000),(20313386223/2500000000000),(-15326321/781250000000)⟩
def e182 : ℝ := (195671581/25000000000000)
theorem h182 : Model (fun x => f182 ((61/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(237799331377239/50000000000000),(14367965124451/50000000000000),(75075309487/25000000000000),(5403041/781250000000)⟩
def e183 : ℝ := (200924801/100000000000000)
theorem h183 : Model (fun x => f183 ((61/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(105354472370957/100000000000000),(146758269089/50000000000000),(766374313/50000000000000),(-2260261/20000000000000)⟩
def e184 : ℝ := (398317/20000000000000)
theorem h184 : Model (fun x => f184 ((61/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(50660581683167/25000000000000),(17872532921/12500000000000),(647060093/100000000000000),(-6406539/100000000000000)⟩
def e185 : ℝ := (192377/20000000000000)
theorem h185 : Model (fun x => f185 ((61/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(410639125836293/100000000000000),(289738532457/50000000000000),(706717203/25000000000000),(-24114383/100000000000000)⟩
def e186 : ℝ := (783071/20000000000000)
theorem h186 : Model (fun x => f186 ((61/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(104016084883669/12500000000000),(440349677709/25000000000000),(9214052477/100000000000000),(-33691137/50000000000000)⟩
def e187 : ℝ := (11948921/100000000000000)
theorem h187 : Model (fun x => f187 ((61/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(33724898333519/2000000000000),(4759119107571/100000000000000),(13287197723/50000000000000),(-20660509/12500000000000)⟩
def e188 : ℝ := (32402487/100000000000000)
theorem h188 : Model (fun x => f188 ((61/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(177653443484603/10000000000000),(2490838132479/25000000000000),(67812011551/100000000000000),(-42751253/20000000000000)⟩
def e189 : ℝ := (6853261/10000000000000)
theorem h189 : Model (fun x => f189 ((61/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((61/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(25660581683167/3125000000000),(17872532921/1562500000000),(647060093/12500000000000),(-6406539/12500000000000)⟩
def e191 : ℝ := (192377/2500000000000)
theorem h191 : Model (fun x => f191 ((61/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(926493086232301/100000000000000),(718679322561/50000000000000),(670922937/10000000000000),(-62553617/100000000000000)⟩
def e192 : ℝ := (1937333/20000000000000)
theorem h192 : Model (fun x => f192 ((61/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1026493086232301/100000000000000),(718679322561/50000000000000),(670922937/10000000000000),(-62553617/100000000000000)⟩
def e193 : ℝ := (1937333/20000000000000)
theorem h193 : Model (fun x => f193 ((61/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(18236003148230579/100000000000000),(127808296159367/100000000000000),(958486489209/100000000000000),(-415578461/25000000000000)⟩
def e194 : ℝ := (882342971/100000000000000)
theorem h194 : Model (fun x => f194 ((61/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(548365775039/100000000000000),(-3843259667/100000000000000),(-943209/50000000000000),(265209/100000000000000)⟩
def e195 : ℝ := (581/2000000000000)
theorem h195 : Model (fun x => f195 ((61/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (4526808455231297/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(81500634159/3125000000000),(139299515041/100000000000000),(266690507/50000000000000),(-7029667/100000000000000)⟩
def e196 : ℝ := (16261/1250000000000)
theorem h196 : Model (fun x => f196 ((61/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(13160581683167/6250000000000),(285960526737/50000000000000),(1294120187/50000000000000),(-6406539/25000000000000)⟩
def e197 : ℝ := (240471/6250000000000)
theorem h197 : Model (fun x => f197 ((61/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(77940555857/160000000000),(-4241047513/6250000000000),(-212563013/100000000000000),(1882169/50000000000000)⟩
def e198 : ℝ := (29123/6250000000000)
theorem h198 : Model (fun x => f198 ((61/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (102498692040783/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(25643576294687/25000000000000),(33928380103/25000000000000),(212563011/50000000000000),(-7528679/100000000000000)⟩
def e199 : ℝ := (2894299/100000000000000)
theorem h199 : Model (fun x => f199 ((61/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(643576294687/25000000000000),(33928380103/25000000000000),(212563011/50000000000000),(-7528679/100000000000000)⟩
def e200 : ℝ := (2894299/100000000000000)
theorem h200 : Model (fun x => f200 ((61/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(47318503877101/12500000000000),(250423757903/50000000000000),(784458731/50000000000000),(-27784411/100000000000000)⟩
def e201 : ℝ := (10681343/100000000000000)
theorem h201 : Model (fun x => f201 ((61/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2734262316731093/100000000000000),(250423757903/50000000000000),(784458731/50000000000000),(-27784411/100000000000000)⟩
def e202 : ℝ := (10431/97656250000)
theorem h202 : Model (fun x => f202 ((61/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(350581321643907/12500000000000),(4224504506677/100000000000000),(13913084599/100000000000000),(-115047517/50000000000000)⟩
def e203 : ℝ := (5637007/6250000000000)
theorem h203 : Model (fun x => f203 ((61/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(505439470345763/6250000000000),(4224504506677/100000000000000),(13913084599/100000000000000),(-115047517/50000000000000)⟩
def e204 : ℝ := (90192113/100000000000000)
theorem h204 : Model (fun x => f204 ((61/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8295216396900967/100000000000000),(1913556415637/12500000000000),(6798068633/12500000000000),(-404011811/50000000000000)⟩
def e205 : ℝ := (327395497/100000000000000)
theorem h205 : Model (fun x => f205 ((61/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6782132007974293/50000000000000),(1913556415637/12500000000000),(6798068633/12500000000000),(-404011811/50000000000000)⟩
def e206 : ℝ := (163697749/50000000000000)
theorem h206 : Model (fun x => f206 ((61/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13913449566970201/100000000000000),(17055538897183/50000000000000),(26845085513/20000000000000),(-1711147117/100000000000000)⟩
def e207 : ℝ := (365664971/50000000000000)
theorem h207 : Model (fun x => f207 ((61/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8124581926342243/50000000000000),(17055538897183/50000000000000),(26845085513/20000000000000),(-1711147117/100000000000000)⟩
def e208 : ℝ := (731329943/100000000000000)
theorem h208 : Model (fun x => f208 ((61/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(1666746691924739/10000000000000),(11408302667709/20000000000000),(126526784059/50000000000000),(-662841883/25000000000000)⟩
def e209 : ℝ := (479211/39062500000)
theorem h209 : Model (fun x => f209 ((61/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(8534923935814171/50000000000000),(11408302667709/20000000000000),(126526784059/50000000000000),(-662841883/25000000000000)⟩
def e210 : ℝ := (1226780161/100000000000000)
theorem h210 : Model (fun x => f210 ((61/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(700371113975683/4000000000000),(16335205489203/20000000000000),(409549350293/100000000000000),(-1709414827/50000000000000)⟩
def e211 : ℝ := (176258973/10000000000000)
theorem h211 : Model (fun x => f211 ((61/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(17491658801773027/100000000000000),(16335205489203/20000000000000),(409549350293/100000000000000),(-1709414827/50000000000000)⟩
def e212 : ℝ := (1762589731/100000000000000)
theorem h212 : Model (fun x => f212 ((61/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(4485486870039/25000000000),(21503432717739/20000000000000),(151324851463/25000000000000),(-3920691719/100000000000000)⟩
def e213 : ℝ := (2328094193/100000000000000)
theorem h213 : Model (fun x => f213 ((61/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(17945280813489333/100000000000000),(21503432717739/20000000000000),(151324851463/25000000000000),(-3920691719/100000000000000)⟩
def e214 : ℝ := (1164047097/50000000000000)
theorem h214 : Model (fun x => f214 ((61/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(461966293322527/100000000000000),(105945282227/390625000000),(59446910041/25000000000000),(-34683317/20000000000000)⟩
def e215 : ℝ := (596526293/100000000000000)
theorem h215 : Model (fun x => f215 ((61/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(105214880829029/100000000000000),(34801800149/12500000000000),(528160861/50000000000000),(-7145537/50000000000000)⟩
def e216 : ℝ := (596419/10000000000000)
theorem h216 : Model (fun x => f216 ((61/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(50643576294687/25000000000000),(33928380103/25000000000000),(212563011/50000000000000),(-7528679/100000000000000)⟩
def e217 : ℝ := (2894299/100000000000000)
theorem h217 : Model (fun x => f217 ((61/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(16414539647461/4000000000000),(17182545063/3125000000000),(953286883/50000000000000),(-1834277/6250000000000)⟩
def e218 : ℝ := (2938197/25000000000000)
theorem h218 : Model (fun x => f218 ((61/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(166258198195671/20000000000000),(1670756221123/100000000000000),(3176499861/50000000000000),(-17084467/20000000000000)⟩
def e219 : ℝ := (447383/1250000000000)
theorem h219 : Model (fun x => f219 ((61/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1683981948987931/100000000000000),(902539414979/20000000000000),(18671021451/100000000000000),(-219904233/100000000000000)⟩
def e220 : ℝ := (19375103/20000000000000)
theorem h220 : Model (fun x => f220 ((61/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1771799600810011/100000000000000),(9436477108981/100000000000000),(49996958629/100000000000000),(-46547459/12500000000000)⟩
def e221 : ℝ := (203969329/100000000000000)
theorem h221 : Model (fun x => f221 ((61/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(25643576294687/3125000000000),(33928380103/3125000000000),(212563011/6250000000000),(-7528679/12500000000000)⟩
def e222 : ℝ := (2894299/12500000000000)
theorem h222 : Model (fun x => f222 ((61/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(925809322259013/100000000000000),(170515320561/12500000000000),(2228664949/50000000000000),(-37260253/50000000000000)⟩
def e223 : ℝ := (14559291/50000000000000)
theorem h223 : Model (fun x => f223 ((61/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1025809322259013/100000000000000),(170515320561/12500000000000),(2228664949/50000000000000),(-37260253/50000000000000)⟩
def e224 : ℝ := (14559291/50000000000000)
theorem h224 : Model (fun x => f224 ((61/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(18175285476857071/100000000000000),(60484890014461/50000000000000),(360286764669/50000000000000),(-1009406177/25000000000000)⟩
def e225 : ℝ := (2623750873/100000000000000)
theorem h225 : Model (fun x => f225 ((61/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(550197685353/100000000000000),(-1830983427/50000000000000),(1280019/50000000000000),(489/195312500000)⟩
def e226 : ℝ := (2597/3125000000000)
theorem h226 : Model (fun x => f226 ((61/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (1805358846192323/10000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(2541727852971/100000000000000),(132307521043/100000000000000),(163465119/50000000000000),(-781089/10000000000000)⟩
def e227 : ℝ := (1895761/50000000000000)
theorem h227 : Model (fun x => f227 ((61/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(5149748146059/100000000000000),(67901759021/25000000000000),(215077813/25000000000000),(-14840557/100000000000000)⟩
def e228 : ℝ := (2546201/50000000000000)
theorem h228 : Model (fun x => f228 ((61/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(7057696816181/100000000000000),(326000208703/100000000000000),(-35280197/5000000000000),(-2697247/50000000000000)⟩
def e229 : ℝ := (50419877/100000000000000)
theorem h229 : Model (fun x => f229 ((61/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(4627997912249/100000000000000),(17237726303/12500000000000),(-1361688263/50000000000000),(41108143/100000000000000)⟩
def e230 : ℝ := (34978067/100000000000000)
theorem h230 : Model (fun x => f230 ((61/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-52997853558871/50000000000000),(-721799721057/25000000000000),(6501328983/10000000000000),(-116403549/10000000000000)⟩
def e231 : ℝ := (88932141/100000000000000)
theorem h231 : Model (fun x => f231 ((61/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((61/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-3721/320),(-61/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((61/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1281/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((61/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6527/320),(23/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((61/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((61/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14847/320),(23/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((61/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((61/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(371175/32),(575/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((61/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(10919/1600),(59/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((61/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(20519/1600),(59/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((61/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((61/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3878091/1600),(11151/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((61/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(20628706237/50000000000000),(-237261791/100000000000000),(337513/10000000000000),(-30973/100000000000000)⟩
def e244 : ℝ := (349/100000000000000)
theorem h244 : Model (fun x => f244 ((61/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (9639/4))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(59819219043113/12500000000000),(-634681577021/50000000000000),(-161007793/10000000000000),(-26304047/50000000000000)⟩
def e245 : ℝ := (1567011/20000000000000)
theorem h245 : Model (fun x => f245 ((61/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(549/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((61/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(47641/1600),(421/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((61/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(81241/1600),(421/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((61/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(19881/1600),(141/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((61/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1615152321/2560000),(9912441/640000),(169283/1280000),(281/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((61/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((61/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(91809/160),(909/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((61/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(174274853227/100000000000000),(-3450987193/100000000000000),(10250457/20000000000000),(-338299/50000000000000)⟩
def e253 : ℝ := (8613/100000000000000)
theorem h253 : Model (fun x => f253 ((61/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (44991/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(21990658881369/20000000000000),(65238614603/12500000000000),(1934749711/100000000000000),(-6478481/50000000000000)⟩
def e254 : ℝ := (2730403/25000000000000)
theorem h254 : Model (fun x => f254 ((61/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(41990658881369/20000000000000),(65238614603/12500000000000),(1934749711/100000000000000),(-6478481/50000000000000)⟩
def e255 : ℝ := (2730403/25000000000000)
theorem h255 : Model (fun x => f255 ((61/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(52488323601711/50000000000000),(65238614603/25000000000000),(193474971/20000000000000),(-6478481/100000000000000)⟩
def e256 : ℝ := (5460807/100000000000000)
theorem h256 : Model (fun x => f256 ((61/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(2488323601711/50000000000000),(65238614603/25000000000000),(193474971/20000000000000),(-6478481/100000000000000)⟩
def e257 : ℝ := (5460807/100000000000000)
theorem h257 : Model (fun x => f257 ((61/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(387413817060247/100000000000000),(60190388473/6250000000000),(3570073869/100000000000000),(-597717/2500000000000)⟩
def e258 : ℝ := (1007649/5000000000000)
theorem h258 : Model (fun x => f258 ((61/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(685782025693633/25000000000000),(60190388473/6250000000000),(3570073869/100000000000000),(-597717/2500000000000)⟩
def e259 : ℝ := (20152981/100000000000000)
theorem h259 : Model (fun x => f259 ((61/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2879643910787543/100000000000000),(1633857742453/20000000000000),(32797187393/100000000000000),(-18417903/10000000000000)⟩
def e260 : ℝ := (171149141/100000000000000)
theorem h260 : Model (fun x => f260 ((61/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(1632404972633699/20000000000000),(1633857742453/20000000000000),(32797187393/100000000000000),(-18417903/10000000000000)⟩
def e261 : ℝ := (85574571/50000000000000)
theorem h261 : Model (fun x => f261 ((61/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4284110022631989/50000000000000),(29875013167637/100000000000000),(67352443501/50000000000000),(-557506833/100000000000000)⟩
def e262 : ℝ := (626971781/100000000000000)
theorem h262 : Model (fun x => f262 ((61/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(13837267664311597/100000000000000),(29875013167637/100000000000000),(67352443501/50000000000000),(-557506833/100000000000000)⟩
def e263 : ℝ := (313485891/50000000000000)
theorem h263 : Model (fun x => f263 ((61/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(1815737457319697/12500000000000),(67470754067389/100000000000000),(353227100809/100000000000000),(-168234993/20000000000000)⟩
def e264 : ℝ := (283836567/20000000000000)
theorem h264 : Model (fun x => f264 ((61/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(16861613944271861/100000000000000),(67470754067389/100000000000000),(353227100809/100000000000000),(-168234993/20000000000000)⟩
def e265 : ℝ := (354795709/25000000000000)
theorem h265 : Model (fun x => f265 ((61/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(55314865572129/312500000000),(7176854300663/6250000000000),(2839955687/400000000000),(-200478377/50000000000000)⟩
def e266 : ℝ := (1210596033/50000000000000)
theorem h266 : Model (fun x => f266 ((61/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(2262892241932779/12500000000000),(7176854300663/6250000000000),(2839955687/400000000000),(-200478377/50000000000000)⟩
def e267 : ℝ := (2421192067/100000000000000)
theorem h267 : Model (fun x => f267 ((61/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(118775420270369/625000000000),(5243290058351/3125000000000),(1220100910263/100000000000000),(1369861779/100000000000000)⟩
def e268 : ℝ := (3544582199/100000000000000)
theorem h268 : Model (fun x => f268 ((61/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(2373306024454999/12500000000000),(5243290058351/3125000000000),(1220100910263/100000000000000),(1369861779/100000000000000)⟩
def e269 : ℝ := (17722911/500000000000)
theorem h269 : Model (fun x => f269 ((61/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(4982834184699369/25000000000000),(112840673232819/50000000000000),(951167163693/50000000000000),(5015021877/100000000000000)⟩
def e270 : ℝ := (1195221011/25000000000000)
theorem h270 : Model (fun x => f270 ((61/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(19934670072130809/100000000000000),(112840673232819/50000000000000),(951167163693/50000000000000),(5015021877/100000000000000)⟩
def e271 : ℝ := (956176809/20000000000000)
theorem h271 : Model (fun x => f271 ((61/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(9920782006561/1000000000000),(2530070989619/4000000000000),(438220494607/50000000000000),(1526381743/25000000000000)⟩
def e272 : ℝ := (8552603/625000000000)
theorem h272 : Model (fun x => f272 ((61/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(110200964580717/100000000000000),(547882482337/100000000000000),(271200767/10000000000000),(-8552969/100000000000000)⟩
def e273 : ℝ := (11518333/100000000000000)
theorem h273 : Model (fun x => f273 ((61/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(102488323601711/50000000000000),(65238614603/25000000000000),(193474971/20000000000000),(-6478481/100000000000000)⟩
def e274 : ℝ := (5460807/100000000000000)
theorem h274 : Model (fun x => f274 ((61/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(420154258987561/100000000000000),(1069791399161/100000000000000),(232337869/5000000000000),(-21509931/100000000000000)⟩
def e275 : ℝ := (22439947/100000000000000)
theorem h275 : Model (fun x => f275 ((61/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(215304528288771/25000000000000),(1644616906553/50000000000000),(8190451243/50000000000000),(-763049/1562500000000)⟩
def e276 : ℝ := (17284729/25000000000000)
theorem h276 : Model (fun x => f276 ((61/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(220662001681733/12500000000000),(1797909650343/20000000000000),(50491634453/100000000000000),(-81328561/100000000000000)⟩
def e277 : ℝ := (18929331/10000000000000)
theorem h277 : Model (fun x => f277 ((61/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1945373234531101/100000000000000),(9789158251973/50000000000000),(30553878319/20000000000000),(139910989/50000000000000)⟩
def e278 : ℝ := (414180687/100000000000000)
theorem h278 : Model (fun x => f278 ((61/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(52488323601711/6250000000000),(65238614603/3125000000000),(193474971/2500000000000),(-6478481/12500000000000)⟩
def e279 : ℝ := (5460807/12500000000000)
theorem h279 : Model (fun x => f279 ((61/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(950014142208093/100000000000000),(2635518149633/100000000000000),(1045100651/10000000000000),(-60380817/100000000000000)⟩
def e280 : ℝ := (55204789/100000000000000)
theorem h280 : Model (fun x => f280 ((61/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1050014142208093/100000000000000),(2635518149633/100000000000000),(1045100651/10000000000000),(-60380817/100000000000000)⟩
def e281 : ℝ := (55204789/100000000000000)
theorem h281 : Model (fun x => f281 ((61/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(20426694081307573/100000000000000),(256845756771863/100000000000000),(2323401384951/100000000000000),(979491783/12500000000000)⟩
def e282 : ℝ := (5456329529/100000000000000)
theorem h282 : Model (fun x => f282 ((61/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(489555478737/100000000000000),(-6155682703/100000000000000),(21718007/100000000000000),(47857/20000000000000)⟩
def e283 : ℝ := (68659/50000000000000)
theorem h283 : Model (fun x => f283 ((61/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (10083755815443483/50000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(4856773184667/100000000000000),(124291671221/50000000000000),(38284121/6250000000000),(-3975033/50000000000000)⟩
def e284 : ℝ := (1654329/20000000000000)
theorem h284 : Model (fun x => f284 ((61/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(21990658881369/10000000000000),(65238614603/6250000000000),(1934749711/50000000000000),(-6478481/25000000000000)⟩
def e285 : ℝ := (2730403/12500000000000)
theorem h285 : Model (fun x => f285 ((61/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(5953705101563/12500000000000),(-11839935313/10000000000000),(-1445929/1000000000000),(2194947/50000000000000)⟩
def e286 : ℝ := (2507019/100000000000000)
theorem h286 : Model (fun x => f286 ((61/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (26178678357717/12500000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(10474071837499/10000000000000),(236798706257/100000000000000),(144592899/50000000000000),(-548737/6250000000000)⟩
def e287 : ℝ := (2005029/12500000000000)
theorem h287 : Model (fun x => f287 ((61/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(474071837499/10000000000000),(236798706257/100000000000000),(144592899/50000000000000),(-548737/6250000000000)⟩
def e288 : ℝ := (2005029/12500000000000)
theorem h288 : Model (fun x => f288 ((61/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(24158945458517/6250000000000),(873899987377/100000000000000),(533616651/50000000000000),(-16200807/50000000000000)⟩
def e289 : ℝ := (924939/1562500000000)
theorem h289 : Model (fun x => f289 ((61/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2742257413050557/100000000000000),(873899987377/100000000000000),(533616651/50000000000000),(-16200807/50000000000000)⟩
def e290 : ℝ := (59196097/100000000000000)
theorem h290 : Model (fun x => f290 ((61/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(287226011412057/10000000000000),(3704479600499/50000000000000),(5558715337/50000000000000),(-269647791/100000000000000)⟩
def e291 : ℝ := (25114907/5000000000000)
theorem h291 : Model (fun x => f291 ((61/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4077320533250761/50000000000000),(3704479600499/50000000000000),(5558715337/50000000000000),(-269647791/100000000000000)⟩
def e292 : ℝ := (502298141/100000000000000)
theorem h292 : Model (fun x => f292 ((61/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(213530740848891/2500000000000),(6767570409153/25000000000000),(5277086013/10000000000000),(-29707499/3125000000000)⟩
def e293 : ℝ := (918886963/50000000000000)
theorem h293 : Model (fun x => f293 ((61/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(13810277253003259/100000000000000),(6767570409153/25000000000000),(5277086013/10000000000000),(-29707499/3125000000000)⟩
def e294 : ℝ := (1837773927/100000000000000)
theorem h294 : Model (fun x => f294 ((61/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1808122950546681/12500000000000),(3816010332371/6250000000000),(2489250237/1562500000000),(-1002488313/50000000000000)⟩
def e295 : ℝ := (2076644577/50000000000000)
theorem h295 : Model (fun x => f295 ((61/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(16800697890087733/100000000000000),(3816010332371/6250000000000),(2489250237/1562500000000),(-1002488313/50000000000000)⟩
def e296 : ℝ := (830657831/20000000000000)
theorem h296 : Model (fun x => f296 ((61/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(17597171662089679/100000000000000),(51867250706051/50000000000000),(36002999097/10000000000000),(-3021278701/100000000000000)⟩
def e297 : ℝ := (3537195419/50000000000000)
theorem h297 : Model (fun x => f297 ((61/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(17999552614470631/100000000000000),(51867250706051/50000000000000),(36002999097/10000000000000),(-3021278701/100000000000000)⟩
def e298 : ℝ := (7074390839/100000000000000)
theorem h298 : Model (fun x => f298 ((61/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(18852860712680833/100000000000000),(4727342803277/3125000000000),(674792106057/100000000000000),(-359230049/10000000000000)⟩
def e299 : ℝ := (5172835517/50000000000000)
theorem h299 : Model (fun x => f299 ((61/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(3767048333012357/20000000000000),(4727342803277/3125000000000),(674792106057/100000000000000),(-359230049/10000000000000)⟩
def e300 : ℝ := (2069134207/20000000000000)
theorem h300 : Model (fun x => f300 ((61/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(19728167427651141/100000000000000),(50762024643417/25000000000000),(1119468114487/100000000000000),(-135237267/4000000000000)⟩
def e301 : ℝ := (13926157893/100000000000000)
theorem h301 : Model (fun x => f301 ((61/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(9865750380492237/50000000000000),(50762024643417/25000000000000),(1119468114487/100000000000000),(-135237267/4000000000000)⟩
def e302 : ℝ := (6963078947/50000000000000)
theorem h302 : Model (fun x => f302 ((61/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(467707441118641/50000000000000),(56349877046251/100000000000000),(1846708747/312500000000),(1345407101/100000000000000)⟩
def e303 : ℝ := (1956826417/50000000000000)
theorem h303 : Model (fun x => f303 ((61/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(109706180857089/100000000000000),(62006166509/12500000000000),(1166526837/100000000000000),(-8511229/50000000000000)⟩
def e304 : ℝ := (33718171/100000000000000)
theorem h304 : Model (fun x => f304 ((61/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(20474071837499/10000000000000),(236798706257/100000000000000),(144592899/50000000000000),(-548737/6250000000000)⟩
def e305 : ℝ := (2005029/12500000000000)
theorem h305 : Model (fun x => f305 ((61/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(419187617607069/100000000000000),(484823372293/50000000000000),(1744898433/100000000000000),(-17291021/50000000000000)⟩
def e306 : ℝ := (13159727/20000000000000)
theorem h306 : Model (fun x => f306 ((61/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(858247739627719/100000000000000),(372236570731/12500000000000),(708085959/10000000000000),(-20134269/20000000000000)⟩
def e307 : ℝ := (40485867/20000000000000)
theorem h307 : Model (fun x => f307 ((61/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(351436517510181/20000000000000),(8129278175671/100000000000000),(6007736109/25000000000000),(-500173/195312500000)⟩
def e308 : ℝ := (55355929/10000000000000)
theorem h308 : Model (fun x => f308 ((61/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(15060452402249/781250000000),(17634813106609/100000000000000),(21796666979/25000000000000),(-183012557/50000000000000)⟩
def e309 : ℝ := (37739419/3125000000000)
theorem h309 : Model (fun x => f309 ((61/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(10474071837499/1250000000000),(236798706257/12500000000000),(144592899/6250000000000),(-548737/781250000000)⟩
def e310 : ℝ := (2005029/1562500000000)
theorem h310 : Model (fun x => f310 ((61/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(947631927857009/100000000000000),(149402436383/6250000000000),(3480013221/100000000000000),(-43630397/50000000000000)⟩
def e311 : ℝ := (162040027/100000000000000)
theorem h311 : Model (fun x => f311 ((61/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1047631927857009/100000000000000),(149402436383/6250000000000),(3480013221/100000000000000),(-43630397/50000000000000)⟩
def e312 : ℝ := (162040027/100000000000000)
theorem h312 : Model (fun x => f312 ((61/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(10097798902122779/50000000000000),(230829330936597/100000000000000),(280406070179/20000000000000),(-1409458719/50000000000000)⟩
def e313 : ℝ := (3170875441/20000000000000)
theorem h313 : Model (fun x => f313 ((61/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(99031482969/20000000000000),(-2829746757/50000000000000),(30311129/100000000000000),(28891/25000000000000)⟩
def e314 : ℝ := (40203/10000000000000)
theorem h314 : Model (fun x => f314 ((61/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (19963347769663423/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(4631776148961/100000000000000),(226080849861/100000000000000),(5133517/25000000000000),(-4310713/50000000000000)⟩
def e315 : ℝ := (1485013/6250000000000)
theorem h315 : Model (fun x => f315 ((61/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(2372137333407/25000000000000),(474664192303/100000000000000),(158270001/25000000000000),(-4142873/25000000000000)⟩
def e316 : ℝ := (32031853/100000000000000)
theorem h316 : Model (fun x => f316 ((61/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(22703904439587/50000000000000),(2151079154209/100000000000000),(-3148357287/100000000000000),(-9997379/10000000000000)⟩
def e317 : ℝ := (77263537/50000000000000)
theorem h317 : Model (fun x => f317 ((61/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(14887806189893/50000000000000),(461209457283/50000000000000),(-17186118133/100000000000000),(216183057/100000000000000)⟩
def e318 : ℝ := (111011439/100000000000000)
theorem h318 : Model (fun x => f318 ((61/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-19055023684489/25000000000000),(-982389984831/50000000000000),(47827171697/100000000000000),(-947852433/100000000000000)⟩
def e319 : ℝ := (9997179/5000000000000)
theorem h319 : Model (fun x => f319 ((61/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((61/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-40931/1600),(-671/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((61/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((61/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(5917/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((61/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(195749/1600),(1269/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((61/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((61/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(368549/1600),(1269/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((61/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1842745/32),(6345/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((61/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((61/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(938736366129824367/100000000000000),(5398454661694979/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (24379/20000000000000)
theorem h329 : Model (fun x => f329 ((61/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(5326309047/50000000000000),(-61260731/100000000000000),(435727/50000000000000),(-3999/50000000000000)⟩
def e330 : ℝ := (93/100000000000000)
theorem h330 : Model (fun x => f330 ((61/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (58330760115764401/6250000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(4907514682407/800000000000),(2177130651/312500000000),(7580463427/100000000000000),(-9693221/100000000000000)⟩
def e331 : ℝ := (5037893/50000000000000)
theorem h331 : Model (fun x => f331 ((61/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((61/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(421/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((61/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((61/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((61/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(555806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((61/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((61/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((61/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(616457906418941/25000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (103/10000000000000)
theorem h339 : Model (fun x => f339 ((61/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3654193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((61/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((61/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((61/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2059168374323977/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1029/100000000000000)
theorem h343 : Model (fun x => f343 ((61/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(48563294409/1000000000000),(-6644872057/100000000000000),(4546059/50000000000000),(-12441/100000000000000)⟩
def e344 : ℝ := (11/50000000000000)
theorem h344 : Model (fun x => f344 ((61/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2056350832688467/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(23949781440143/20000000000000),(228350474913/25000000000000),(-1249799657/100000000000000),(1710081/100000000000000)⟩
def e345 : ℝ := (3359/100000000000000)
theorem h345 : Model (fun x => f345 ((61/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(43949781440143/20000000000000),(228350474913/25000000000000),(-1249799657/100000000000000),(1710081/100000000000000)⟩
def e346 : ℝ := (3359/100000000000000)
theorem h346 : Model (fun x => f346 ((61/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(109874453600357/100000000000000),(228350474913/50000000000000),(-624899829/100000000000000),(167/19531250000)⟩
def e347 : ℝ := (1681/100000000000000)
theorem h347 : Model (fun x => f347 ((61/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(9874453600357/100000000000000),(228350474913/50000000000000),(-624899829/100000000000000),(167/19531250000)⟩
def e348 : ℝ := (1681/100000000000000)
theorem h348 : Model (fun x => f348 ((61/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(202744527476849/50000000000000),(3370887963/200000000000),(-2306177941/100000000000000),(197219/6250000000000)⟩
def e349 : ℝ := (6207/100000000000000)
theorem h349 : Model (fun x => f349 ((61/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2761203340667983/100000000000000),(3370887963/200000000000),(-2306177941/100000000000000),(197219/6250000000000)⟩
def e350 : ℝ := (97/1562500000000)
theorem h350 : Model (fun x => f350 ((61/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(2427085666683/80000000000),(14462314248871/100000000000000),(-6045608347/50000000000000),(1502953/25000000000000)⟩
def e351 : ℝ := (96569/100000000000000)
theorem h351 : Model (fun x => f351 ((61/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4158119017867351/50000000000000),(14462314248871/100000000000000),(-6045608347/50000000000000),(1502953/25000000000000)⟩
def e352 : ℝ := (9657/10000000000000)
theorem h352 : Model (fun x => f352 ((61/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1827484220373713/20000000000000),(10774145371581/20000000000000),(796211/100000000000),(-1060673/1562500000000)⟩
def e353 : ℝ := (473403/100000000000000)
theorem h353 : Model (fun x => f353 ((61/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(1800808590114523/12500000000000),(10774145371581/20000000000000),(796211/100000000000),(-1060673/1562500000000)⟩
def e354 : ℝ := (118351/25000000000000)
theorem h354 : Model (fun x => f354 ((61/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(15829028790212997/100000000000000),(124984646270473/100000000000000),(78438477661/50000000000000),(-142203431/50000000000000)⟩
def e355 : ℝ := (182289/20000000000000)
theorem h355 : Model (fun x => f355 ((61/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(9082371537963641/50000000000000),(124984646270473/100000000000000),(78438477661/50000000000000),(-142203431/50000000000000)⟩
def e356 : ℝ := (455723/50000000000000)
theorem h356 : Model (fun x => f356 ((61/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(9979206101291891/50000000000000),(220284751335233/100000000000000),(629662315719/100000000000000),(-221744963/100000000000000)⟩
def e357 : ℝ := (505347/20000000000000)
theorem h357 : Model (fun x => f357 ((61/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(10180396577482367/50000000000000),(220284751335233/100000000000000),(629662315719/100000000000000),(-221744963/100000000000000)⟩
def e358 : ℝ := (157921/6250000000000)
theorem h358 : Model (fun x => f358 ((61/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(2237131022771639/10000000000000),(335024602625323/100000000000000),(314129203797/20000000000000),(1429566601/100000000000000)⟩
def e359 : ℝ := (1551123/25000000000000)
theorem h359 : Model (fun x => f359 ((61/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(11176845590048671/50000000000000),(335024602625323/100000000000000),(314129203797/20000000000000),(1429566601/100000000000000)⟩
def e360 : ℝ := (6204493/100000000000000)
theorem h360 : Model (fun x => f360 ((61/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(24560996043643149/100000000000000),(7346812054719/1562500000000),(389513886967/12500000000000),(684144861/10000000000000)⟩
def e361 : ℝ := (1913247/25000000000000)
theorem h361 : Model (fun x => f361 ((61/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(12282164688488241/50000000000000),(7346812054719/1562500000000),(389513886967/12500000000000),(684144861/10000000000000)⟩
def e362 : ℝ := (7652989/100000000000000)
theorem h362 : Model (fun x => f362 ((61/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(1212796653284203/50000000000000),(158614808619753/100000000000000),(460317191981/20000000000000),(608932283/5000000000000)⟩
def e363 : ℝ := (17020493/100000000000000)
theorem h363 : Model (fun x => f363 ((61/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(12072395553977/10000000000000),(1003595346417/100000000000000),(71254703/10000000000000),(-1914453/50000000000000)⟩
def e364 : ℝ := (15437/100000000000000)
theorem h364 : Model (fun x => f364 ((61/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(209874453600357/100000000000000),(228350474913/50000000000000),(-624899829/100000000000000),(167/19531250000)⟩
def e365 : ℝ := (1681/100000000000000)
theorem h365 : Model (fun x => f365 ((61/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(110118215685121/25000000000000),(1916997246069/100000000000000),(-134313157/25000000000000),(-1059413/50000000000000)⟩
def e366 : ℝ := (18799/100000000000000)
theorem h366 : Model (fun x => f366 ((61/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(924440013934441/100000000000000),(3017465621791/50000000000000),(4874874447/100000000000000),(-7556803/50000000000000)⟩
def e367 : ℝ := (57059/100000000000000)
theorem h367 : Model (fun x => f367 ((61/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(485040857026993/25000000000000),(3377541059367/20000000000000),(32015880353/100000000000000),(-4907993/12500000000000)⟩
def e368 : ℝ := (183679/100000000000000)
theorem h368 : Model (fun x => f368 ((61/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(468448406869589/20000000000000),(19929447855807/50000000000000),(110979819261/50000000000000),(319954707/100000000000000)⟩
def e369 : ℝ := (167469/12500000000000)
theorem h369 : Model (fun x => f369 ((61/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(109874453600357/12500000000000),(228350474913/6250000000000),(-624899829/12500000000000),(167/2441406250)⟩
def e370 : ℝ := (1681/12500000000000)
theorem h370 : Model (fun x => f370 ((61/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(499859792171313/50000000000000),(186288117801/4000000000000),(-2143325801/50000000000000),(1505707/50000000000000)⟩
def e371 : ℝ := (5777/20000000000000)
theorem h371 : Model (fun x => f371 ((61/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(549859792171313/50000000000000),(186288117801/4000000000000),(-2143325801/50000000000000),(1505707/50000000000000)⟩
def e372 : ℝ := (5777/20000000000000)
theorem h372 : Model (fun x => f372 ((61/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(1609880897776843/6250000000000),(136854761811647/25000000000000),(419683952341/10000000000000),(1527204751/12500000000000)⟩
def e373 : ℝ := (5519441/25000000000000)
theorem h373 : Model (fun x => f373 ((61/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(388227477487/100000000000000),(-4125365659/50000000000000),(56046053/50000000000000),(-1222047/100000000000000)⟩
def e374 : ℝ := (1547/12500000000000)
theorem h374 : Model (fun x => f374 ((61/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (12603233118971859/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(1177102463523/12500000000000),(51957135479/12500000000000),(-358148489/25000000000000),(1383991/25000000000000)⟩
def e375 : ℝ := (153103/20000000000000)
theorem h375 : Model (fun x => f375 ((61/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(23949781440143/10000000000000),(228350474913/12500000000000),(-1249799657/50000000000000),(1710081/50000000000000)⟩
def e376 : ℝ := (3359/50000000000000)
theorem h376 : Model (fun x => f376 ((61/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(45506483410477/100000000000000),(-94575460973/50000000000000),(522516361/50000000000000),(-288683/5000000000000)⟩
def e377 : ℝ := (32291/100000000000000)
theorem h377 : Model (fun x => f377 ((61/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (109417126893983/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(108987033179041/100000000000000),(378301843891/100000000000000),(-2090065447/100000000000000),(5773659/50000000000000)⟩
def e378 : ℝ := (54811/25000000000000)
theorem h378 : Model (fun x => f378 ((61/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(8987033179041/100000000000000),(378301843891/100000000000000),(-2090065447/100000000000000),(5773659/50000000000000)⟩
def e379 : ℝ := (54811/25000000000000)
theorem h379 : Model (fun x => f379 ((61/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(402214051017889/100000000000000),(349028486923/25000000000000),(-7713336769/100000000000000),(21307551/50000000000000)⟩
def e380 : ℝ := (809117/100000000000000)
theorem h380 : Model (fun x => f380 ((61/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1378964168366087/50000000000000),(349028486923/25000000000000),(-7713336769/100000000000000),(21307551/50000000000000)⟩
def e381 : ℝ := (404559/50000000000000)
theorem h381 : Model (fun x => f381 ((61/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(751446067852117/25000000000000),(5977438461219/50000000000000),(-15191879829/25000000000000),(3065523/1000000000000)⟩
def e382 : ℝ := (7420011/100000000000000)
theorem h382 : Model (fun x => f382 ((61/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(414408261189471/5000000000000),(5977438461219/50000000000000),(-15191879829/25000000000000),(3065523/1000000000000)⟩
def e383 : ℝ := (1855003/25000000000000)
theorem h383 : Model (fun x => f383 ((61/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(1129128172798139/12500000000000),(44383547544299/100000000000000),(-9711563707/5000000000000),(811413653/100000000000000)⟩
def e384 : ℝ := (3013643/10000000000000)
theorem h384 : Model (fun x => f384 ((61/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(14302073001432731/100000000000000),(44383547544299/100000000000000),(-9711563707/5000000000000),(811413653/100000000000000)⟩
def e385 : ℝ := (30136431/100000000000000)
theorem h385 : Model (fun x => f385 ((61/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(3117481009472431/20000000000000),(102477317567197/100000000000000),(-68541162091/20000000000000),(436707917/50000000000000)⟩
def e386 : ℝ := (38353681/50000000000000)
theorem h386 : Model (fun x => f386 ((61/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(448077983326911/2500000000000),(102477317567197/100000000000000),(-68541162091/20000000000000),(436707917/50000000000000)⟩
def e387 : ℝ := (76707363/100000000000000)
theorem h387 : Model (fun x => f387 ((61/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(19533876014259131/100000000000000),(44872619754441/25000000000000),(-180218118813/50000000000000),(-52094477/12500000000000)⟩
def e388 : ℝ := (72885953/50000000000000)
theorem h388 : Model (fun x => f388 ((61/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(19936256966640083/100000000000000),(44872619754441/25000000000000),(-180218118813/50000000000000),(-52094477/12500000000000)⟩
def e389 : ℝ := (145771907/100000000000000)
theorem h389 : Model (fun x => f389 ((61/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(217279349948909/1000000000000),(271040575627957/100000000000000),(-130493788443/100000000000000),(-1633556113/50000000000000)⟩
def e390 : ℝ := (115123207/50000000000000)
theorem h390 : Model (fun x => f390 ((61/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(5427578986817963/25000000000000),(271040575627957/100000000000000),(-130493788443/100000000000000),(-1633556113/50000000000000)⟩
def e391 : ℝ := (46049283/20000000000000)
theorem h391 : Model (fun x => f391 ((61/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(11830714622363901/50000000000000),(94382401907849/25000000000000),(429370374737/100000000000000),(-7212355291/100000000000000)⟩
def e392 : ℝ := (160863537/50000000000000)
theorem h392 : Model (fun x => f392 ((61/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(4732952515612227/20000000000000),(94382401907849/25000000000000),(429370374737/100000000000000),(-7212355291/100000000000000)⟩
def e393 : ℝ := (12869083/4000000000000)
theorem h393 : Model (fun x => f393 ((61/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(132922504039477/6250000000000),(123452944283769/100000000000000),(972180099183/100000000000000),(-4181831211/100000000000000)⟩
def e394 : ℝ := (9038693/10000000000000)
theorem h394 : Model (fun x => f394 ((61/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(118781734011693/100000000000000),(206149978059/25000000000000),(-1562338897/50000000000000),(4678323/50000000000000)⟩
def e395 : ℝ := (611101/100000000000000)
theorem h395 : Model (fun x => f395 ((61/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(208987033179041/100000000000000),(378301843891/100000000000000),(-2090065447/100000000000000),(5773659/50000000000000)⟩
def e396 : ℝ := (54811/25000000000000)
theorem h396 : Model (fun x => f396 ((61/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(17470232014791/4000000000000),(790601800009/50000000000000),(-456550543/6250000000000),(16225641/50000000000000)⟩
def e397 : ℝ := (1049589/100000000000000)
theorem h397 : Model (fun x => f397 ((61/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(912762989430167/100000000000000),(4956765738297/100000000000000),(-9206431327/50000000000000),(7196267/12500000000000)⟩
def e398 : ℝ := (226131/6250000000000)
theorem h398 : Model (fun x => f398 ((61/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1907556291566429/100000000000000),(13811996877471/100000000000000),(-19403151527/50000000000000),(52457917/100000000000000)⟩
def e399 : ℝ := (5382771/50000000000000)
theorem h399 : Model (fun x => f399 ((61/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(9063313761487/400000000000),(3213583689881/10000000000000),(1638785321/20000000000000),(-127695857/25000000000000)⟩
def e400 : ℝ := (27561103/100000000000000)
theorem h400 : Model (fun x => f400 ((61/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(108987033179041/12500000000000),(378301843891/12500000000000),(-2090065447/12500000000000),(5773659/6250000000000)⟩
def e401 : ℝ := (54811/3125000000000)
theorem h401 : Model (fun x => f401 ((61/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(990677999444021/100000000000000),(962753665841/25000000000000),(-1984520137/10000000000000),(10173519/10000000000000)⟩
def e402 : ℝ := (2365053/100000000000000)
theorem h402 : Model (fun x => f402 ((61/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1090677999444021/100000000000000),(962753665841/25000000000000),(-1984520137/10000000000000),(10173519/10000000000000)⟩
def e403 : ℝ := (2365053/100000000000000)
theorem h403 : Model (fun x => f403 ((61/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(4942578460856053/20000000000000),(218877944238961/50000000000000),(27414591539/3125000000000),(-1865545967/20000000000000)⟩
def e404 : ℝ := (367525279/100000000000000)
theorem h404 : Model (fun x => f404 ((61/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(404647091763/100000000000000),(-7167782913/100000000000000),(56301699/50000000000000),(-1587443/100000000000000)⟩
def e405 : ℝ := (5629/20000000000000)
theorem h405 : Model (fun x => f405 ((61/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (24274249453617981/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(2151468187577/25000000000000),(173553602113/50000000000000),(-9844283/390625000000),(18645689/100000000000000)⟩
def e406 : ℝ := (159143/10000000000000)
theorem h406 : Model (fun x => f406 ((61/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(4505673114623/25000000000000),(381382144029/50000000000000),(-988182601/25000000000000),(24181653/100000000000000)⟩
def e407 : ℝ := (471389/20000000000000)
theorem h407 : Model (fun x => f407 ((61/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(55279142410347/50000000000000),(4804656998303/100000000000000),(-17567359471/100000000000000),(88437953/50000000000000)⟩
def e408 : ℝ := (16575533/100000000000000)
theorem h408 : Model (fun x => f408 ((61/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(14499447189599/20000000000000),(1962115475149/100000000000000),(-10921351861/25000000000000),(41606921/5000000000000)⟩
def e409 : ℝ := (35565929/100000000000000)
theorem h409 : Model (fun x => f409 ((61/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3722858789961/100000000000000),(-2664494513/100000000000000),(4141764253/100000000000000),(-115714013/100000000000000)⟩
def e410 : ℝ := (235509509/100000000000000)
theorem h410 : Model (fun x => f410 ((61/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(341413559814453/25000000000000),(25768106689453/25000000000000),(63257/2048000),(4697/10240000)⟩
def e411 : ℝ := (168945313/50000000000000)
theorem h411 : Model (fun x => f411 ((61/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(32761/1600),(181/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((61/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(5929741/64000),(98283/64000),(543/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((61/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(63265436987116073/50000000000000),(465883369070169/4000000000000),(228024463764251/50000000000000),(9888981916137/100000000000000)⟩
def e414 : ℝ := (130522541647/100000000000000)
theorem h414 : Model (fun x => f414 ((61/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(39516047293/50000000000000),(-3637426319/50000000000000),(192396993/50000000000000),(-1922047/12500000000000)⟩
def e415 : ℝ := (394269/50000000000000)
theorem h415 : Model (fun x => f415 ((61/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (22883544263098327/20000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2470297312709/50000000000000),(43702095337/50000000000000),(-1873492103/50000000000000),(92018591/100000000000000)⟩
def e416 : ℝ := (25428971/25000000000000)
theorem h416 : Model (fun x => f416 ((61/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1217735835457/100000000000000),(84739696161/100000000000000),(394780047/100000000000000),(-11847711/50000000000000)⟩
def e417 : ℝ := (337225393/100000000000000)
theorem h417 : Model (fun x => f417 ((61/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((61/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((1217530203413/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (3/2) (31/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (3/2) (31/20) ≤ (1218204654199/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(61/40)-(1/40)) (by norm_num : ((61/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel10


noncomputable section
namespace Hf4Quad.Panel11
open Hf4Quad.Dag

def p0 : Cubic := ⟨(63/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((63/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((63/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((63/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((63/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(69/25),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((63/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-69/25),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((63/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-184571428571429/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((63/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((63/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(3969/1600),(63/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((63/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(3003/1000),(9533333333333/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/100000000000000)
theorem h9 : Model (fun x => f9 ((63/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-3003/1000),(-9533333333333/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/100000000000000)
theorem h10 : Model (fun x => f10 ((63/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-484871428571429/100000000000000),(-2782857142857/20000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (3/100000000000000)
theorem h11 : Model (fun x => f11 ((63/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((63/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(250047/64000),(11907/64000),(189/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((63/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(48722121/1280000),(2320101/1280000),(36827/1280000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/100000000000000)
theorem h14 : Model (fun x => f14 ((63/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-48722121/1280000),(-2320101/1280000),(-36827/1280000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/100000000000000)
theorem h15 : Model (fun x => f15 ((63/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-4291287131696429/100000000000000),(-39034435267857/20000000000000),(-2952770750661/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/25000000000000)
theorem h16 : Model (fun x => f16 ((63/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((63/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(15752961/2560000),(250047/640000),(11907/1280000),(63/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((63/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(2750517/160000),(43659/40000),(2079/80000),(11/40000)⟩
def e19 : ℝ := (21825397/20000000000000)
theorem h19 : Model (fun x => f19 ((63/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2572214006696429/100000000000000),(-17204935267857/20000000000000),(-354020750661/100000000000000),(491087963/4000000000000)⟩
def e20 : ℝ := (109126989/100000000000000)
theorem h20 : Model (fun x => f20 ((63/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((63/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(969176311523437/100000000000000),(19229688720703/25000000000000),(250047/10240000),(3969/10240000)⟩
def e22 : ℝ := (308593751/100000000000000)
theorem h22 : Model (fun x => f22 ((63/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(1262800838496093/20000000000000),(125277860961913/25000000000000),(15908299804687/100000000000000),(15782043457/6250000000000)⟩
def e23 : ℝ := (251303893/12500000000000)
theorem h23 : Model (fun x => f23 ((63/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(935447546446009/25000000000000),(415086767508367/100000000000000),(7777139527013/50000000000000),(264789894387/100000000000000)⟩
def e24 : ℝ := (2119558133/100000000000000)
theorem h24 : Model (fun x => f24 ((63/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((63/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(1526452690649413/100000000000000),(72688223364257/50000000000000),(576890661621/10000000000000),(61046630859/50000000000000)⟩
def e26 : ℝ := (292548829/20000000000000)
theorem h26 : Model (fun x => f26 ((63/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(214228347192993/6250000000000),(81610798930663/25000000000000),(12954095068357/100000000000000),(54832148437/20000000000000)⟩
def e27 : ℝ := (65691917/2000000000000)
theorem h27 : Model (fun x => f27 ((63/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(1792360935217981/25000000000000),(741529963231019/100000000000000),(28508374122383/100000000000000),(134737659143/25000000000000)⟩
def e28 : ℝ := (5404153983/100000000000000)
theorem h28 : Model (fun x => f28 ((63/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((63/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(96166519510913/4000000000000),(66782305215911/25000000000000),(12720439088743/100000000000000),(336519552611/100000000000000)⟩
def e30 : ℝ := (5392722177/100000000000000)
theorem h30 : Model (fun x => f30 ((63/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(570511693130217/100000000000000),(63390188125579/100000000000000),(3018580386931/100000000000000),(9982077999/12500000000000)⟩
def e31 : ℝ := (255940307/20000000000000)
theorem h31 : Model (fun x => f31 ((63/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(7739955434002141/100000000000000),(402460075678299/50000000000000),(15763477254657/50000000000000),(154701815141/25000000000000)⟩
def e32 : ℝ := (3341927759/50000000000000)
theorem h32 : Model (fun x => f32 ((63/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((63/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1702701/320),(27027/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((63/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((63/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(139167/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((63/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(3929373/320),(44699/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((63/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((63/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(4658973/320),(44699/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((63/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-4658973/320),(-44699/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((63/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((63/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(103/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((63/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(10609/1600),(103/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((63/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((63/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(222789/160),(2163/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((63/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(17954207793/25000000000000),(-1394501577/100000000000000),(812331/4000000000000),(-262891/100000000000000)⟩
def e46 : ℝ := (1641/50000000000000)
theorem h46 : Model (fun x => f46 ((63/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (109221/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-261400529199927/25000000000000),(239575383081/100000000000000),(-593338667/25000000000000),(11756373/50000000000000)⟩
def e47 : ℝ := (95275069/100000000000000)
theorem h47 : Model (fun x => f47 ((63/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((63/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(143/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((63/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((63/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((63/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(23833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((63/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(43833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((63/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((63/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(27395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((63/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((63/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(575312499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((63/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((63/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(2395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((63/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(220536458333299/100000000000000),(2606770833329/25000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (103/100000000000000)
theorem h60 : Model (fun x => f60 ((63/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(120085069444441/100000000000000),(456597222221/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((63/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((63/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(27395833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((63/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1215918402777761/100000000000000),(2539930555551/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((63/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1315918402777761/100000000000000),(2539930555551/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((63/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(290207984004219/10000000000000),(4637964194961/3125000000000),(1013272026903/100000000000000),(2033058449/100000000000000)⟩
def e66 : ℝ := (317219/50000000000000)
theorem h66 : Model (fun x => f66 ((63/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(52395833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((63/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(87850347222221/20000000000000),(873263888887/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((63/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(184119686053237/20000000000000),(5490646701377/100000000000000),(1091579861/10000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (3/5000000000000)
theorem h69 : Model (fun x => f69 ((63/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(26716501452499813/100000000000000),(3814119423531/250000000000),(17793886863449/100000000000000),(4538104421/5000000000000)⟩
def e70 : ℝ := (1868309/781250000000)
theorem h70 : Model (fun x => f70 ((63/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((63/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2521786458333261/12500000000000),(9588541666641/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((63/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1933369618055231/100000000000000),(12345247395811/12500000000000),(133437499999/20000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1/100000000000)
theorem h73 : Model (fun x => f73 ((63/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(17798570355059793/100000000000000),(1015355725065679/100000000000000),(11775831737099/100000000000000),(29370625681/50000000000000)⟩
def e74 : ℝ := (9180699/6250000000000)
theorem h74 : Model (fun x => f74 ((63/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(22257535903779803/50000000000000),(2541003494478079/100000000000000),(7392429650137/25000000000000),(74751669891/50000000000000)⟩
def e75 : ℝ := (24127171/6250000000000)
theorem h75 : Model (fun x => f75 ((63/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((63/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(840595486111087/12500000000000),(3196180555547/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((63/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(918402777777/100000000000000),(7986111111/10000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((63/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(5500849971/6250000000000),(5740017361/50000000000000),(62391493/12500000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((63/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(1479676689727/25000000000000),(81701440629/10000000000000),(19760887853/50000000000000),(47054211/6250000000000)⟩
def e80 : ℝ := (4191789/100000000000000)
theorem h80 : Model (fun x => f80 ((63/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(1550577864443/12500000000000),(868493652339/50000000000000),(8623528161/10000000000000),(1742558607/100000000000000)⟩
def e81 : ℝ := (11939707/100000000000000)
theorem h81 : Model (fun x => f81 ((63/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(890549528609503/2000000000000),(2542740481782757/100000000000000),(14827976941079/50000000000000),(151245898389/100000000000000)⟩
def e82 : ℝ := (397974443/100000000000000)
theorem h82 : Model (fun x => f82 ((63/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(4217318311/50000000000000),(58675733/4000000000000),(19133391/20000000000000),(554591/20000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((63/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(404159671/50000000000000),(43930399/25000000000000),(7640069/50000000000000),(664353/100000000000000)⟩
def e84 : ℝ := (3643/25000000000000)
theorem h84 : Model (fun x => f84 ((63/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(605187/781250000000),(20207983/100000000000000),(2196519/100000000000000),(63667/50000000000000)⟩
def e85 : ℝ := (4229/100000000000000)
theorem h85 : Model (fun x => f85 ((63/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(7423627/100000000000000),(564841/25000000000000),(294699/100000000000000),(4271/20000000000000)⟩
def e86 : ℝ := (239/25000000000000)
theorem h86 : Model (fun x => f86 ((63/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(22270881/100000000000000),(1694523/25000000000000),(884097/100000000000000),(12813/20000000000000)⟩
def e87 : ℝ := (717/25000000000000)
theorem h87 : Model (fun x => f87 ((63/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-22270881/100000000000000),(-1694523/25000000000000),(-884097/100000000000000),(-12813/20000000000000)⟩
def e88 : ℝ := (717/25000000000000)
theorem h88 : Model (fun x => f88 ((63/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(44527476408204269/100000000000000),(508548095000933/20000000000000),(29655952998061/100000000000000),(37811458581/25000000000000)⟩
def e89 : ℝ := (397977311/100000000000000)
theorem h89 : Model (fun x => f89 ((63/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2521786458333261/10000000000000),(9588541666641/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((63/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(9647104383831/500000000000),(59934793637/390625000000),(1830215567/4000000000000),(15160831/25000000000000)⟩
def e91 : ℝ := (30307/100000000000000)
theorem h91 : Model (fun x => f91 ((63/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(30409921496590567/6250000000000),(3784660459438821/50000000000000),(239984335253/500000000000),(31795516633/20000000000000)⟩
def e92 : ℝ := (145539881/50000000000000)
theorem h92 : Model (fun x => f92 ((63/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(5138125727/25000000000000),(-63946437/20000000000000),(2946611/100000000000000),(-2627/12500000000000)⟩
def e93 : ℝ := (1/625000000000)
theorem h93 : Model (fun x => f93 ((63/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (478941266890857903/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(1830302176731/20000000000000),(190114068411/50000000000000),(-18071689/2500000000000),(915977/50000000000000)⟩
def e94 : ℝ := (304367/100000000000000)
theorem h94 : Model (fun x => f94 ((63/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(23833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((63/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(9125475285171/20000000000000),(-173488123293/100000000000000),(329825329/50000000000000),(-1254089/50000000000000)⟩
def e96 : ℝ := (4789/50000000000000)
theorem h96 : Model (fun x => f96 ((63/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (218333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(54372623574143/50000000000000),(173488123291/50000000000000),(-32982533/2500000000000),(5016353/100000000000000)⟩
def e97 : ℝ := (16199/25000000000000)
theorem h97 : Model (fun x => f97 ((63/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1141825095057003/50000000000000),(3643250589111/50000000000000),(-692633193/2500000000000),(105343413/100000000000000)⟩
def e98 : ℝ := (340179/25000000000000)
theorem h98 : Model (fun x => f98 ((63/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(4372623574143/50000000000000),(173488123291/50000000000000),(-32982533/2500000000000),(5016353/100000000000000)⟩
def e99 : ℝ := (16199/25000000000000)
theorem h99 : Model (fun x => f99 ((63/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(49927713281943/25000000000000),(4280473125609/50000000000000),(-726869819/10000000000000),(-17123329/25000000000000)⟩
def e100 : ℝ := (338441/12500000000000)
theorem h100 : Model (fun x => f100 ((63/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(59127643886709/50000000000000),(377320176891/50000000000000),(-832714903/50000000000000),(877383/50000000000000)⟩
def e101 : ℝ := (193729/100000000000000)
theorem h101 : Model (fun x => f101 ((63/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(54372623574143/5000000000000),(173488123291/5000000000000),(-32982533/250000000000),(5016353/10000000000000)⟩
def e102 : ℝ := (16199/2500000000000)
theorem h102 : Model (fun x => f102 ((63/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(602853879628139/50000000000000),(2112201409801/50000000000000),(-7429221503/50000000000000),(6489787/12500000000000)⟩
def e103 : ℝ := (841689/100000000000000)
theorem h103 : Model (fun x => f103 ((63/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(652853879628139/50000000000000),(2112201409801/50000000000000),(-7429221503/50000000000000),(6489787/12500000000000)⟩
def e104 : ℝ := (841689/100000000000000)
theorem h104 : Model (fun x => f104 ((63/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(651910026341557/25000000000000),(120217530378493/100000000000000),(59266743817/25000000000000),(-2369718481/100000000000000)⟩
def e105 : ℝ := (39857967/100000000000000)
theorem h105 : Model (fun x => f105 ((63/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(104372623574143/50000000000000),(173488123291/50000000000000),(-32982533/2500000000000),(5016353/100000000000000)⟩
def e106 : ℝ := (16199/25000000000000)
theorem h106 : Model (fun x => f106 ((63/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(43574578206999/10000000000000),(724296423473/50000000000000),(-2152016223/50000000000000),(736717/6250000000000)⟩
def e107 : ℝ := (323321/100000000000000)
theorem h107 : Model (fun x => f107 ((63/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(113699826215029/12500000000000),(907160615559/20000000000000),(-9706989933/100000000000000),(12419059/100000000000000)⟩
def e108 : ℝ := (565027/50000000000000)
theorem h108 : Model (fun x => f108 ((63/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(11859529072459201/50000000000000),(302943601279947/25000000000000),(7356064991583/100000000000000),(-11073847203/50000000000000)⟩
def e109 : ℝ := (511015949/100000000000000)
theorem h109 : Model (fun x => f109 ((63/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1241680521620889/6250000000000),(7923723714711/6250000000000),(-17487012963/6250000000000),(18425043/6250000000000)⟩
def e110 : ℝ := (4068309/12500000000000)
theorem h110 : Model (fun x => f110 ((63/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(217176060815747/12500000000000),(4001028552527/5000000000000),(153322385927/100000000000000),(-1621042867/100000000000000)⟩
def e111 : ℝ := (27006751/100000000000000)
theorem h111 : Model (fun x => f111 ((63/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(7901721719300801/50000000000000),(806671429371619/100000000000000),(4855543748479/100000000000000),(-15342400873/100000000000000)⟩
def e112 : ℝ := (10814669/3125000000000)
theorem h112 : Model (fun x => f112 ((63/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(9880625395880001/25000000000000),(2018445834491407/100000000000000),(6105804370031/50000000000000),(-37490095279/100000000000000)⟩
def e113 : ℝ := (857085357/100000000000000)
theorem h113 : Model (fun x => f113 ((63/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(413893507206963/6250000000000),(2641241238237/6250000000000),(-5829004321/6250000000000),(6141681/6250000000000)⟩
def e114 : ℝ := (1356103/12500000000000)
theorem h114 : Model (fun x => f114 ((63/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(382396738423/50000000000000),(30343930309/50000000000000),(486586417/50000000000000),(-413897/5000000000000)⟩
def e115 : ℝ := (64137/100000000000000)
theorem h115 : Model (fun x => f115 ((63/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(16720769931/25000000000000),(79609551/1000000000000),(285588899/100000000000000),(1890461/100000000000000)⟩
def e116 : ℝ := (22523/50000000000000)
theorem h116 : Model (fun x => f116 ((63/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(4429195590363/100000000000000),(277731358029/50000000000000),(22214453147/100000000000000),(119261203/50000000000000)⟩
def e117 : ℝ := (3552173/100000000000000)
theorem h117 : Model (fun x => f117 ((63/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(1155716910223/12500000000000),(234974055213/20000000000000),(48240504371/100000000000000),(283938509/50000000000000)⟩
def e118 : ℝ := (399753/5000000000000)
theorem h118 : Model (fun x => f118 ((63/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(9882936829700447/25000000000000),(126226294047967/6250000000000),(12259849244433/100000000000000),(-36922218261/100000000000000)⟩
def e119 : ℝ := (865080417/100000000000000)
theorem h119 : Model (fun x => f119 ((63/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(2924545311/50000000000000),(464136799/50000000000000),(6464461/12500000000000),(1054577/100000000000000)⟩
def e120 : ℝ := (7349/100000000000000)
theorem h120 : Model (fun x => f120 ((63/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(51151743/10000000000000),(4058991/4000000000000),(3833193/50000000000000),(259713/100000000000000)⟩
def e121 : ℝ := (371/10000000000000)
theorem h121 : Model (fun x => f121 ((63/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(44733463/100000000000000),(10649063/100000000000000),(1015789/100000000000000),(47999/100000000000000)⟩
def e122 : ℝ := (1149/100000000000000)
theorem h122 : Model (fun x => f122 ((63/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(3912051/100000000000000),(1086501/100000000000000),(15649/12500000000000),(7583/100000000000000)⟩
def e123 : ℝ := (131/50000000000000)
theorem h123 : Model (fun x => f123 ((63/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(11736153/100000000000000),(3259503/100000000000000),(46947/12500000000000),(22749/100000000000000)⟩
def e124 : ℝ := (393/50000000000000)
theorem h124 : Model (fun x => f124 ((63/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-11736153/100000000000000),(-3259503/100000000000000),(-46947/12500000000000),(-22749/100000000000000)⟩
def e125 : ℝ := (393/50000000000000)
theorem h125 : Model (fun x => f125 ((63/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(7906349461413127/20000000000000),(2019620701507969/100000000000000),(12259848868857/100000000000000),(-3692224101/10000000000000)⟩
def e126 : ℝ := (865081203/100000000000000)
theorem h126 : Model (fun x => f126 ((63/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1241680521620889/5000000000000),(7923723714711/5000000000000),(-17487012963/5000000000000),(18425043/5000000000000)⟩
def e127 : ℝ := (4068309/10000000000000)
theorem h127 : Model (fun x => f127 ((63/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1898743865917871/100000000000000),(394511389371/3125000000000),(-413126683/2500000000000),(-21968987/100000000000000)⟩
def e128 : ℝ := (167727/5000000000000)
theorem h128 : Model (fun x => f128 ((63/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(471526654771473077/100000000000000),(6144109849240311/100000000000000),(231548816237/2500000000000),(-68799303727/100000000000000)⟩
def e129 : ℝ := (1685508111/100000000000000)
theorem h129 : Model (fun x => f129 ((63/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(2120770883/10000000000000),(-276341733/100000000000000),(3184229/100000000000000),(-32969/100000000000000)⟩
def e130 : ℝ := (103/25000000000000)
theorem h130 : Model (fun x => f130 ((63/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (58171651560596431/12500000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(8383777864293/100000000000000),(79768140563/25000000000000),(-861120217/50000000000000),(4783343/50000000000000)⟩
def e131 : ℝ := (535793/100000000000000)
theorem h131 : Model (fun x => f131 ((63/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(4383822186987/25000000000000),(349650349537/50000000000000),(-1222553997/50000000000000),(142483/1250000000000)⟩
def e132 : ℝ := (5251/625000000000)
theorem h132 : Model (fun x => f132 ((63/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-91674675167743/50000000000000),(-7269892677121/100000000000000),(26825278677/100000000000000),(-34379039/25000000000000)⟩
def e133 : ℝ := (13206369/50000000000000)
theorem h133 : Model (fun x => f133 ((63/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(63492063492063/100000000000000),(-1007810531621/100000000000000),(3199398513/20000000000000),(-253920517/100000000000000)⟩
def e134 : ℝ := (819099/20000000000000)
theorem h134 : Model (fun x => f134 ((63/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (31/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-29103071481823/25000000000000),(-2767990812023/100000000000000),(12193657013/20000000000000),(-527531201/50000000000000)⟩
def e135 : ℝ := (6134467/12500000000000)
theorem h135 : Model (fun x => f135 ((63/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(15752961/256000),(250047/64000),(11907/128000),(63/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((63/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((63/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(2250423/32000),(107163/32000),(1701/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((63/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(6751269/51200),(464373/64000),(18711/128000),(81/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((63/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-3969/1600),(-63/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((63/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(6624261/51200),(459333/64000),(18631/128000),(81/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((63/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((63/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(189/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((63/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-189/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((63/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(6140421/51200),(449733/64000),(18631/128000),(81/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((63/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(6294021/51200),(449733/64000),(18631/128000),(81/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((63/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((63/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(6294021/800),(449733/1000),(18631/2000),(81/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((63/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((63/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(2977309629/512000),(47258883/128000),(2250423/256000),(11907/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((63/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(859836671/5000000000000),(-1091856091/100000000000000),(21663811/50000000000000),(-1375481/100000000000000)⟩
def e151 : ℝ := (44787/100000000000000)
theorem h151 : Model (fun x => f151 ((63/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (1391862717/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(67647875798051/50000000000000),(-856267945989/100000000000000),(2006731647/20000000000000),(-57010729/50000000000000)⟩
def e152 : ℝ := (138069103/20000000000000)
theorem h152 : Model (fun x => f152 ((63/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(183/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((63/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(26169/1600),(163/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((63/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(309/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((63/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1294498381877/20000000000000),(-15709931819/25000000000000),(610094439/100000000000000),(-5923247/100000000000000)⟩
def e156 : ℝ := (58073/100000000000000)
theorem h156 : Model (fun x => f156 ((63/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (153/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(21172330097087/20000000000000),(72746803027/25000000000000),(1220188869/100000000000000),(-2369299/20000000000000)⟩
def e157 : ℝ := (895473/50000000000000)
theorem h157 : Model (fun x => f157 ((63/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(41172330097087/20000000000000),(72746803027/25000000000000),(1220188869/100000000000000),(-2369299/20000000000000)⟩
def e158 : ℝ := (895473/50000000000000)
theorem h158 : Model (fun x => f158 ((63/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(102930825242717/100000000000000),(72746803027/50000000000000),(305047217/50000000000000),(-370203/6250000000000)⟩
def e159 : ℝ := (35819/4000000000000)
theorem h159 : Model (fun x => f159 ((63/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(2930825242717/100000000000000),(72746803027/50000000000000),(305047217/50000000000000),(-370203/6250000000000)⟩
def e160 : ℝ := (35819/4000000000000)
theorem h160 : Model (fun x => f160 ((63/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((63/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((63/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(47482969978039/12500000000000),(33558793063/6250000000000),(1125769491/50000000000000),(-10929803/50000000000000)⟩
def e163 : ℝ := (826183/25000000000000)
theorem h163 : Model (fun x => f163 ((63/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2735578045538597/100000000000000),(33558793063/6250000000000),(1125769491/50000000000000),(-10929803/50000000000000)⟩
def e164 : ℝ := (3304733/100000000000000)
theorem h164 : Model (fun x => f164 ((63/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((63/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1407876528715733/50000000000000),(906553725427/20000000000000),(19788351419/100000000000000),(-35596731/20000000000000)⟩
def e166 : ℝ := (13978903/50000000000000)
theorem h166 : Model (fun x => f166 ((63/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4049067004906209/50000000000000),(906553725427/20000000000000),(19788351419/100000000000000),(-35596731/20000000000000)⟩
def e167 : ℝ := (27957807/100000000000000)
theorem h167 : Model (fun x => f167 ((63/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((63/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(166709523311221/2000000000000),(8223941674107/50000000000000),(38184733399/50000000000000),(-606427651/100000000000000)⟩
def e169 : ℝ := (101784571/100000000000000)
theorem h169 : Model (fun x => f169 ((63/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13604523784608669/100000000000000),(8223941674107/50000000000000),(38184733399/50000000000000),(-606427651/100000000000000)⟩
def e170 : ℝ := (25446143/25000000000000)
theorem h170 : Model (fun x => f170 ((63/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((63/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(7001624300919709/50000000000000),(36723654305977/100000000000000),(185538783393/100000000000000),(-1218570357/100000000000000)⟩
def e172 : ℝ := (228288401/100000000000000)
theorem h172 : Model (fun x => f172 ((63/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(16338962887553703/100000000000000),(36723654305977/100000000000000),(185538783393/100000000000000),(-1218570357/100000000000000)⟩
def e173 : ℝ := (114144201/50000000000000)
theorem h173 : Model (fun x => f173 ((63/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((63/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(16817829336260289/100000000000000),(61572106733351/100000000000000),(172045136483/50000000000000),(-86404289/5000000000000)⟩
def e175 : ℝ := (384789253/100000000000000)
theorem h175 : Model (fun x => f175 ((63/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(17220210288641241/100000000000000),(61572106733351/100000000000000),(172045136483/50000000000000),(-86404289/5000000000000)⟩
def e176 : ℝ := (192394627/50000000000000)
theorem h176 : Model (fun x => f176 ((63/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((63/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2215613069828711/12500000000000),(8843098249899/10000000000000),(548817980447/100000000000000),(-961225687/50000000000000)⟩
def e178 : ℝ := (555479187/100000000000000)
theorem h178 : Model (fun x => f178 ((63/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(221341068887633/1250000000000),(8843098249899/10000000000000),(548817980447/100000000000000),(-961225687/50000000000000)⟩
def e179 : ℝ := (138869797/25000000000000)
theorem h179 : Model (fun x => f179 ((63/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((63/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(18226255104567309/100000000000000),(116785708280699/100000000000000),(50099716561/6250000000000),(-1689633927/100000000000000)⟩
def e181 : ℝ := (368331563/50000000000000)
theorem h181 : Model (fun x => f181 ((63/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(9114794218950321/50000000000000),(116785708280699/100000000000000),(50099716561/6250000000000),(-1689633927/100000000000000)⟩
def e182 : ℝ := (736663127/100000000000000)
theorem h182 : Model (fun x => f182 ((63/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(534277379581411/100000000000000),(29945670605281/100000000000000),(152313402483/50000000000000),(749469303/100000000000000)⟩
def e183 : ℝ := (191504257/100000000000000)
theorem h183 : Model (fun x => f183 ((63/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(105947547851467/100000000000000),(299515538773/100000000000000),(293526873/20000000000000),(-13023/125000000000)⟩
def e184 : ℝ := (371929/20000000000000)
theorem h184 : Model (fun x => f184 ((63/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(202930825242717/100000000000000),(72746803027/50000000000000),(305047217/50000000000000),(-370203/6250000000000)⟩
def e185 : ℝ := (35819/4000000000000)
theorem h185 : Model (fun x => f185 ((63/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(411809198336901/100000000000000),(590502750881/100000000000000),(2687823233/100000000000000),(-347889/1562500000000)⟩
def e186 : ℝ := (730119/20000000000000)
theorem h186 : Model (fun x => f186 ((63/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(83568780461049/10000000000000),(898734079083/50000000000000),(8825990611/100000000000000),(-31030791/50000000000000)⟩
def e187 : ℝ := (2789437/25000000000000)
theorem h187 : Model (fun x => f187 ((63/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1695868158348811/100000000000000),(2431744644561/50000000000000),(5124868321/20000000000000),(-151634437/100000000000000)⟩
def e188 : ℝ := (30302189/100000000000000)
theorem h188 : Model (fun x => f188 ((63/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(898365364282199/50000000000000),(10232136293201/100000000000000),(8325551451/12500000000000),(-189208171/100000000000000)⟩
def e189 : ℝ := (64413393/100000000000000)
theorem h189 : Model (fun x => f189 ((63/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((63/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(102930825242717/12500000000000),(72746803027/6250000000000),(305047217/6250000000000),(-370203/781250000000)⟩
def e191 : ℝ := (35819/500000000000)
theorem h191 : Model (fun x => f191 ((63/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(929394149793203/100000000000000),(292692877441/20000000000000),(6348389837/100000000000000),(-1806387/3125000000000)⟩
def e192 : ℝ := (1804689/20000000000000)
theorem h192 : Model (fun x => f192 ((63/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1029394149793203/100000000000000),(292692877441/20000000000000),(6348389837/100000000000000),(-1806387/3125000000000)⟩
def e193 : ℝ := (1804689/20000000000000)
theorem h193 : Model (fun x => f193 ((63/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(9247720503689353/50000000000000),(131623526747587/100000000000000),(237357264567/25000000000000),(-1361979229/100000000000000)⟩
def e194 : ℝ := (20789419/2500000000000)
theorem h194 : Model (fun x => f194 ((63/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(540673779879/100000000000000),(-3847726027/100000000000000),(-371991/100000000000000),(239977/100000000000000)⟩
def e195 : ℝ := (26661/100000000000000)
theorem h195 : Model (fun x => f195 ((63/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (9181432929008431/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2888697703221/100000000000000),(141350859381/100000000000000),(98564487/20000000000000),(-3249137/50000000000000)⟩
def e196 : ℝ := (308979/25000000000000)
theorem h196 : Model (fun x => f196 ((63/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(21172330097087/10000000000000),(72746803027/12500000000000),(1220188869/50000000000000),(-2369299/10000000000000)⟩
def e197 : ℝ := (895473/25000000000000)
theorem h197 : Model (fun x => f197 ((63/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(9715262630431/20000000000000),(-68663036099/100000000000000),(-47716769/25000000000000),(3472141/100000000000000)⟩
def e198 : ℝ := (17263/4000000000000)
theorem h198 : Model (fun x => f198 ((63/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (205569429447017/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(102847373695689/100000000000000),(34331518049/25000000000000),(381734149/100000000000000),(-1388857/20000000000000)⟩
def e199 : ℝ := (672659/25000000000000)
theorem h199 : Model (fun x => f199 ((63/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(2847373695689/100000000000000),(34331518049/25000000000000),(381734149/100000000000000),(-1388857/20000000000000)⟩
def e200 : ℝ := (672659/25000000000000)
theorem h200 : Model (fun x => f200 ((63/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(379555783876947/100000000000000),(50679859977/10000000000000),(1408780787/100000000000000),(-25627719/100000000000000)⟩
def e201 : ℝ := (2482433/25000000000000)
theorem h201 : Model (fun x => f201 ((63/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(42738594837363/1562500000000),(50679859977/10000000000000),(1408780787/100000000000000),(-25627719/100000000000000)⟩
def e202 : ℝ := (9929733/100000000000000)
theorem h202 : Model (fun x => f202 ((63/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1406576715029413/50000000000000),(534683500039/12500000000000),(6293160287/50000000000000),(-212433139/100000000000000)⟩
def e203 : ℝ := (8390119/10000000000000)
theorem h203 : Model (fun x => f203 ((63/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4047767191219889/50000000000000),(534683500039/12500000000000),(6293160287/50000000000000),(-212433139/100000000000000)⟩
def e204 : ℝ := (83901191/100000000000000)
theorem h204 : Model (fun x => f204 ((63/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8326044498970827/100000000000000),(620661715587/4000000000000),(49722198231/100000000000000),(-747046029/100000000000000)⟩
def e205 : ℝ := (304884937/100000000000000)
theorem h205 : Model (fun x => f205 ((63/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6797546059009223/50000000000000),(620661715587/4000000000000),(49722198231/100000000000000),(-747046029/100000000000000)⟩
def e206 : ℝ := (152442469/50000000000000)
theorem h206 : Model (fun x => f206 ((63/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13982195194891591/100000000000000),(17313981433749/50000000000000),(124343343117/100000000000000),(-19811071/1250000000000)⟩
def e207 : ℝ := (682119281/100000000000000)
theorem h207 : Model (fun x => f207 ((63/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(4079477370151469/25000000000000),(17313981433749/50000000000000),(124343343117/100000000000000),(-19811071/1250000000000)⟩
def e208 : ℝ := (341059641/50000000000000)
theorem h208 : Model (fun x => f208 ((63/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(16782541342842989/100000000000000),(29011347263877/50000000000000),(237728116939/100000000000000),(-49204657/2000000000000)⟩
def e209 : ℝ := (1146593073/100000000000000)
theorem h209 : Model (fun x => f209 ((63/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(17184922295223941/100000000000000),(29011347263877/50000000000000),(237728116939/100000000000000),(-49204657/2000000000000)⟩
def e210 : ℝ := (573296537/50000000000000)
theorem h210 : Model (fun x => f210 ((63/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(17674241252282741/100000000000000),(2602318633351/3125000000000),(77955625813/20000000000000),(-317569973/10000000000000)⟩
def e211 : ℝ := (1651297657/100000000000000)
theorem h211 : Model (fun x => f211 ((63/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(17656622204663693/100000000000000),(2602318633351/3125000000000),(77955625813/20000000000000),(-317569973/10000000000000)⟩
def e212 : ℝ := (825648829/50000000000000)
theorem h212 : Model (fun x => f212 ((63/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(1815937222086647/10000000000000),(109892469583193/100000000000000),(116527021677/20000000000000),(-3639096897/100000000000000)⟩
def e213 : ℝ := (2186612367/100000000000000)
theorem h213 : Model (fun x => f213 ((63/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(18162705554199803/100000000000000),(109892469583193/100000000000000),(116527021677/20000000000000),(-3639096897/100000000000000)⟩
def e214 : ℝ := (136663273/6250000000000)
theorem h214 : Model (fun x => f214 ((63/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(51716010037573/10000000000000),(14035589707281/50000000000000),(118417030209/50000000000000),(-145281733/100000000000000)⟩
def e215 : ℝ := (141849103/25000000000000)
theorem h215 : Model (fun x => f215 ((63/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(105775822761007/100000000000000),(141236258653/50000000000000),(486895797/50000000000000),(-13235589/100000000000000)⟩
def e216 : ℝ := (2779789/50000000000000)
theorem h216 : Model (fun x => f216 ((63/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(202847373695689/100000000000000),(34331518049/25000000000000),(381734149/100000000000000),(-1388857/20000000000000)⟩
def e217 : ℝ := (672659/25000000000000)
theorem h217 : Model (fun x => f217 ((63/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(82294114030477/20000000000000),(278562330849/50000000000000),(434314973/25000000000000),(-27124159/100000000000000)⟩
def e218 : ℝ := (218817/2000000000000)
theorem h218 : Model (fun x => f218 ((63/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(83465724508479/10000000000000),(847584558349/50000000000000),(5859787159/100000000000000),(-2471309/3125000000000)⟩
def e219 : ℝ := (33364041/100000000000000)
theorem h219 : Model (fun x => f219 ((63/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(846540150507643/50000000000000),(573101005487/12500000000000),(4350126313/25000000000000),(-25482307/12500000000000)⟩
def e220 : ℝ := (45216027/50000000000000)
theorem h220 : Model (fun x => f220 ((63/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(447717404600863/25000000000000),(9632104976733/100000000000000),(47843423941/100000000000000),(-345923989/100000000000000)⟩
def e221 : ℝ := (19131313/10000000000000)
theorem h221 : Model (fun x => f221 ((63/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(102847373695689/12500000000000),(34331518049/3125000000000),(381734149/12500000000000),(-1388857/2500000000000)⟩
def e222 : ℝ := (672659/3125000000000)
theorem h222 : Model (fun x => f222 ((63/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(928554812326519/100000000000000),(690540547437/50000000000000),(2013832393/50000000000000),(-68789869/100000000000000)⟩
def e223 : ℝ := (13542333/50000000000000)
theorem h223 : Model (fun x => f223 ((63/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1028554812326519/100000000000000),(690540547437/50000000000000),(2013832393/50000000000000),(-68789869/100000000000000)⟩
def e224 : ℝ := (13542333/50000000000000)
theorem h224 : Model (fun x => f224 ((63/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(71953420478837/390625000000),(123804841000141/100000000000000),(348626622591/50000000000000),(-3741249317/100000000000000)⟩
def e225 : ℝ := (2467606929/100000000000000)
theorem h225 : Model (fun x => f225 ((63/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(542885935651/100000000000000),(-3648839899/100000000000000),(1987371/50000000000000),(55417/25000000000000)⟩
def e226 : ℝ := (38061/50000000000000)
theorem h226 : Model (fun x => f226 ((63/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (18295567339480703/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1403794724869/50000000000000),(1043157351/781250000000),(282022189/100000000000000),(-286731/4000000000000)⟩
def e227 : ℝ := (3593727/100000000000000)
theorem h227 : Model (fun x => f227 ((63/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(5696287152959/100000000000000),(274875000309/100000000000000),(48427789/6250000000000),(-13666549/100000000000000)⟩
def e228 : ℝ := (4829643/100000000000000)
theorem h228 : Model (fun x => f228 ((63/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(1926708629167/25000000000000),(64623743323/20000000000000),(-733788677/100000000000000),(-2019989/50000000000000)⟩
def e229 : ℝ := (9584839/20000000000000)
theorem h229 : Model (fun x => f229 ((63/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(4893228264551/100000000000000),(63742225397/50000000000000),(-622365071/25000000000000),(36950177/100000000000000)⟩
def e230 : ℝ := (16073047/50000000000000)
theorem h230 : Model (fun x => f230 ((63/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-111519057662741/100000000000000),(-2640506361229/100000000000000),(58478824781/100000000000000),(-40724489/4000000000000)⟩
def e231 : ℝ := (8122183/10000000000000)
theorem h231 : Model (fun x => f231 ((63/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((63/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-3969/320),(-63/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((63/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1323/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((63/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1323/64),(21/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((63/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((63/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2987/64),(21/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((63/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((63/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(373375/32),(525/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((63/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(11151/1600),(57/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((63/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(20751/1600),(57/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((63/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((63/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3921939/1600),(10773/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((63/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(40796147007/100000000000000),(-28015281/12500000000000),(3197247/100000000000000),(-14183/50000000000000)⟩
def e244 : ℝ := (79/25000000000000)
theorem h244 : Model (fun x => f244 ((63/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (975051/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(238004084199041/50000000000000),(-1276427812177/100000000000000),(-192062303/10000000000000),(-50968429/100000000000000)⟩
def e245 : ℝ := (1429693/20000000000000)
theorem h245 : Model (fun x => f245 ((63/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(567/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((63/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(49329/1600),(423/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((63/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(82929/1600),(423/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((63/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(20449/1600),(143/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((63/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1695815121/2560000),(10254387/640000),(172667/1280000),(283/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((63/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((63/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(95481/160),(927/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((63/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(41893151517/25000000000000),(-813459253/25000000000000),(1895439/4000000000000),(-613411/100000000000000)⟩
def e253 : ℝ := (3827/50000000000000)
theorem h253 : Model (fun x => f253 ((63/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (46809/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(111004749701363/100000000000000),(264748321613/50000000000000),(1860138847/100000000000000),(-11931057/100000000000000)⟩
def e254 : ℝ := (10197697/100000000000000)
theorem h254 : Model (fun x => f254 ((63/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(211004749701363/100000000000000),(264748321613/50000000000000),(1860138847/100000000000000),(-11931057/100000000000000)⟩
def e255 : ℝ := (10197697/100000000000000)
theorem h255 : Model (fun x => f255 ((63/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(105502374850681/100000000000000),(264748321613/100000000000000),(930069423/100000000000000),(-5965529/100000000000000)⟩
def e256 : ℝ := (101977/2000000000000)
theorem h256 : Model (fun x => f256 ((63/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(5502374850681/100000000000000),(264748321613/100000000000000),(930069423/100000000000000),(-5965529/100000000000000)⟩
def e257 : ℝ := (101977/2000000000000)
theorem h257 : Model (fun x => f257 ((63/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(97338500606283/25000000000000),(977047377381/100000000000000),(3432399061/100000000000000),(-22015643/100000000000000)⟩
def e258 : ℝ := (9408593/50000000000000)
theorem h258 : Model (fun x => f258 ((63/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2745068288139417/100000000000000),(977047377381/100000000000000),(3432399061/100000000000000),(-22015643/100000000000000)⟩
def e259 : ℝ := (18817187/100000000000000)
theorem h259 : Model (fun x => f259 ((63/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2896112235260019/100000000000000),(8298330406533/100000000000000),(6347803969/20000000000000),(-84405217/50000000000000)⟩
def e260 : ℝ := (32000909/20000000000000)
theorem h260 : Model (fun x => f260 ((63/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8178493187640971/100000000000000),(8298330406533/100000000000000),(6347803969/20000000000000),(-84405217/50000000000000)⟩
def e261 : ℝ := (80002273/50000000000000)
theorem h261 : Model (fun x => f261 ((63/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4314252269981193/50000000000000),(30407359099361/100000000000000),(32880193641/25000000000000),(-126195161/25000000000000)⟩
def e262 : ℝ := (2936589/500000000000)
theorem h262 : Model (fun x => f262 ((63/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(2779510431802001/20000000000000),(30407359099361/100000000000000),(32880193641/25000000000000),(-126195161/25000000000000)⟩
def e263 : ℝ := (587317801/100000000000000)
theorem h263 : Model (fun x => f263 ((63/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(2932449514773529/20000000000000),(6887402206547/10000000000000),(2788139173/800000000000),(-730609479/100000000000000)⟩
def e264 : ℝ := (1333306863/100000000000000)
theorem h264 : Model (fun x => f264 ((63/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(1699796185958193/10000000000000),(6887402206547/10000000000000),(2788139173/800000000000),(-730609479/100000000000000)⟩
def e265 : ℝ := (83331679/6250000000000)
theorem h265 : Model (fun x => f265 ((63/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(8966626719035957/50000000000000),(117665547665913/100000000000000),(354064896721/50000000000000),(-110779259/50000000000000)⟩
def e266 : ℝ := (456654437/20000000000000)
theorem h266 : Model (fun x => f266 ((63/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(9167817195226433/50000000000000),(117665547665913/100000000000000),(354064896721/50000000000000),(-110779259/50000000000000)⟩
def e267 : ℝ := (1141636093/50000000000000)
theorem h267 : Model (fun x => f267 ((63/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(483613243146649/2500000000000),(86341615737209/50000000000000),(1229145440647/100000000000000),(820782969/50000000000000)⟩
def e268 : ℝ := (1678489581/50000000000000)
theorem h268 : Model (fun x => f268 ((63/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(37747872418451/195312500000),(86341615737209/50000000000000),(1229145440647/100000000000000),(820782969/50000000000000)⟩
def e269 : ℝ := (3356979163/100000000000000)
theorem h269 : Model (fun x => f269 ((63/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(407806995016407/2000000000000),(29169072726839/12500000000000),(386741454783/20000000000000),(2719577223/50000000000000)⟩
def e270 : ℝ := (2275232147/50000000000000)
theorem h270 : Model (fun x => f270 ((63/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(20393683084153683/100000000000000),(29169072726839/12500000000000),(386741454783/20000000000000),(2719577223/50000000000000)⟩
def e271 : ℝ := (910092859/20000000000000)
theorem h271 : Model (fun x => f271 ((63/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1122136889150057/100000000000000),(33415933727779/50000000000000),(913872277109/100000000000000),(6372490151/100000000000000)⟩
def e272 : ℝ := (1332843459/100000000000000)
theorem h272 : Model (fun x => f272 ((63/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(13913438873917/12500000000000),(279315766679/50000000000000),(665851849/25000000000000),(-478929/6250000000000)⟩
def e273 : ℝ := (10808959/100000000000000)
theorem h273 : Model (fun x => f273 ((63/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(205502374850681/100000000000000),(264748321613/100000000000000),(930069423/100000000000000),(-5965529/100000000000000)⟩
def e274 : ℝ := (101977/2000000000000)
theorem h274 : Model (fun x => f274 ((63/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(211156130346349/50000000000000),(136016022073/12500000000000),(2261773121/50000000000000),(-9796961/50000000000000)⟩
def e275 : ℝ := (21006659/100000000000000)
theorem h275 : Model (fun x => f275 ((63/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(867861725009093/100000000000000),(3354193866449/100000000000000),(3220918649/20000000000000),(-5420347/12500000000000)⟩
def e276 : ℝ := (64888949/100000000000000)
theorem h276 : Model (fun x => f276 ((63/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(445869113828443/25000000000000),(9190597403531/100000000000000),(50047210081/100000000000000),(-33525553/50000000000000)⟩
def e277 : ℝ := (89055017/50000000000000)
theorem h277 : Model (fun x => f277 ((63/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(992571625763133/50000000000000),(10096443542251/50000000000000),(77274561439/50000000000000),(62612851/20000000000000)⟩
def e278 : ℝ := (393283423/100000000000000)
theorem h278 : Model (fun x => f278 ((63/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(105502374850681/12500000000000),(264748321613/12500000000000),(930069423/12500000000000),(-5965529/12500000000000)⟩
def e279 : ℝ := (101977/250000000000)
theorem h279 : Model (fun x => f279 ((63/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(59707906862299/6250000000000),(1338309053131/50000000000000),(505198139/5000000000000),(-6923387/12500000000000)⟩
def e280 : ℝ := (51599759/100000000000000)
theorem h280 : Model (fun x => f280 ((63/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(65957906862299/6250000000000),(1338309053131/50000000000000),(505198139/5000000000000),(-6923387/12500000000000)⟩
def e281 : ℝ := (51599759/100000000000000)
theorem h281 : Model (fun x => f281 ((63/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(2618717873849817/12500000000000),(26623559420167/10000000000000),(1186031235767/50000000000000),(4190654239/50000000000000)⟩
def e282 : ℝ := (5208684609/100000000000000)
theorem h282 : Model (fun x => f282 ((63/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(477332824769/100000000000000),(-379130511/6250000000000),(11521509/50000000000000),(101519/50000000000000)⟩
def e283 : ℝ := (124587/100000000000000)
theorem h283 : Model (fun x => f283 ((63/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (4136224348826449/20000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(2678163855377/50000000000000),(12547031381/5000000000000),(11334131/2000000000000),(-1834967/25000000000000)⟩
def e284 : ℝ := (1992333/25000000000000)
theorem h284 : Model (fun x => f284 ((63/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(111004749701363/50000000000000),(264748321613/25000000000000),(1860138847/50000000000000),(-11931057/50000000000000)⟩
def e285 : ℝ := (10197697/50000000000000)
theorem h285 : Model (fun x => f285 ((63/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(23696149053879/50000000000000),(-1486581629/1250000000000),(-119357769/100000000000000),(4027679/100000000000000)⟩
def e286 : ℝ := (2317849/100000000000000)
theorem h286 : Model (fun x => f286 ((63/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (26309171348817/12500000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(105215403784481/100000000000000),(59463265159/25000000000000),(238715537/100000000000000),(-8055363/100000000000000)⟩
def e287 : ℝ := (14927377/100000000000000)
theorem h287 : Model (fun x => f287 ((63/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(5215403784481/100000000000000),(59463265159/25000000000000),(238715537/100000000000000),(-8055363/100000000000000)⟩
def e288 : ℝ := (14927377/100000000000000)
theorem h288 : Model (fun x => f288 ((63/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(77658988507593/20000000000000),(877791057109/100000000000000),(176194801/20000000000000),(-14864063/50000000000000)⟩
def e289 : ℝ := (13772283/25000000000000)
theorem h289 : Model (fun x => f289 ((63/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(10976036913009/400000000000),(877791057109/100000000000000),(176194801/20000000000000),(-14864063/50000000000000)⟩
def e290 : ℝ := (55089133/100000000000000)
theorem h290 : Model (fun x => f290 ((63/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(115484815575561/4000000000000),(7450281338653/100000000000000),(597821851/6250000000000),(-1985021/800000000000)⟩
def e291 : ℝ := (467972661/100000000000000)
theorem h291 : Model (fun x => f291 ((63/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8169501341769977/100000000000000),(7450281338653/100000000000000),(597821851/6250000000000),(-1985021/800000000000)⟩
def e292 : ℝ := (233986331/50000000000000)
theorem h292 : Model (fun x => f292 ((63/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4297786911960937/50000000000000),(13635126286821/50000000000000),(47286601979/100000000000000),(-878615491/100000000000000)⟩
def e293 : ℝ := (214408547/12500000000000)
theorem h293 : Model (fun x => f293 ((63/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(13864621442969493/100000000000000),(13635126286821/50000000000000),(47286601979/100000000000000),(-878615491/100000000000000)⟩
def e294 : ℝ := (1715268377/100000000000000)
theorem h294 : Model (fun x => f294 ((63/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1823464679301261/12500000000000),(61669932806103/100000000000000),(18464115641/12500000000000),(-1863713463/100000000000000)⟩
def e295 : ℝ := (1943346361/50000000000000)
theorem h295 : Model (fun x => f295 ((63/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(16923431720124373/100000000000000),(61669932806103/100000000000000),(18464115641/12500000000000),(-1863713463/100000000000000)⟩
def e296 : ℝ := (3886692723/100000000000000)
theorem h296 : Model (fun x => f296 ((63/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(17806057018519797/100000000000000),(52569584563259/50000000000000),(85624858549/25000000000000),(-1412801039/50000000000000)⟩
def e297 : ℝ := (166079281/2500000000000)
theorem h297 : Model (fun x => f297 ((63/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(18208437970900749/100000000000000),(52569584563259/50000000000000),(85624858549/25000000000000),(-1412801039/50000000000000)⟩
def e298 : ℝ := (6643171241/100000000000000)
theorem h298 : Model (fun x => f298 ((63/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(9579040766964991/50000000000000),(153931928339909/100000000000000),(26156210593/4000000000000),(-843523873/25000000000000)⟩
def e299 : ℝ := (9753653153/100000000000000)
theorem h299 : Model (fun x => f299 ((63/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(9570231243155467/50000000000000),(153931928339909/100000000000000),(26156210593/4000000000000),(-843523873/25000000000000)⟩
def e300 : ℝ := (4876826577/50000000000000)
theorem h300 : Model (fun x => f300 ((63/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(503467872279729/2500000000000),(207486275799649/100000000000000),(549916062707/50000000000000),(-1584554407/50000000000000)⟩
def e301 : ℝ := (659237037/5000000000000)
theorem h301 : Model (fun x => f301 ((63/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(20142048224522493/100000000000000),(207486275799649/100000000000000),(549916062707/50000000000000),(-1584554407/50000000000000)⟩
def e302 : ℝ := (13184740741/100000000000000)
theorem h302 : Model (fun x => f302 ((63/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(525244572686867/50000000000000),(58729725257139/100000000000000),(299477671131/50000000000000),(330872357/25000000000000)⟩
def e303 : ℝ := (1889285603/50000000000000)
theorem h303 : Model (fun x => f303 ((63/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(110702811935313/100000000000000),(500516116323/100000000000000),(133508977/12500000000000),(-15815381/100000000000000)⟩
def e304 : ℝ := (15760339/50000000000000)
theorem h304 : Model (fun x => f304 ((63/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(205215403784481/100000000000000),(59463265159/25000000000000),(238715537/100000000000000),(-8055363/100000000000000)⟩
def e305 : ℝ := (14927377/100000000000000)
theorem h305 : Model (fun x => f305 ((63/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(16845344780171/4000000000000),(195244447519/20000000000000),(154550289/10000000000000),(-31926107/100000000000000)⟩
def e306 : ℝ := (7671929/12500000000000)
theorem h306 : Model (fun x => f306 ((63/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(864231057737897/100000000000000),(375629701259/12500000000000),(812361981/12500000000000),(-11679339/12500000000000)⟩
def e307 : ℝ := (4731481/2500000000000)
theorem h307 : Model (fun x => f307 ((63/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(443383813691929/25000000000000),(8222400087181/100000000000000),(4509472619/20000000000000),(-238728057/100000000000000)⟩
def e308 : ℝ := (5187459/1000000000000)
theorem h308 : Model (fun x => f308 ((63/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(981676698845989/50000000000000),(17979257883863/100000000000000),(85057632751/100000000000000),(-172047853/50000000000000)⟩
def e309 : ℝ := (1140758377/100000000000000)
theorem h309 : Model (fun x => f309 ((63/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(105215403784481/12500000000000),(59463265159/3125000000000),(238715537/12500000000000),(-8055363/12500000000000)⟩
def e310 : ℝ := (14927377/12500000000000)
theorem h310 : Model (fun x => f310 ((63/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(952426042211161/100000000000000),(2403340601411/100000000000000),(186112257/6250000000000),(-16051657/20000000000000)⟩
def e311 : ℝ := (75469847/50000000000000)
theorem h311 : Model (fun x => f311 ((63/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1052426042211161/100000000000000),(2403340601411/100000000000000),(186112257/6250000000000),(-16051657/20000000000000)⟩
def e312 : ℝ := (75469847/50000000000000)
theorem h312 : Model (fun x => f312 ((63/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(516571061448701/2500000000000),(236404461521991/100000000000000),(173217017957/12500000000000),(-2617496321/100000000000000)⟩
def e313 : ℝ := (1504408309/10000000000000)
theorem h313 : Model (fun x => f313 ((63/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(483960520937/100000000000000),(-2768506477/50000000000000),(7723199/25000000000000),(15839/20000000000000)⟩
def e314 : ℝ := (364289/100000000000000)
theorem h314 : Model (fun x => f314 ((63/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (10212517299351491/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(5083952740337/100000000000000),(226062964239/100000000000000),(-28639633/100000000000000),(-194597/2500000000000)⟩
def e315 : ℝ := (709353/3125000000000)
theorem h315 : Model (fun x => f315 ((63/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(10440280451091/100000000000000),(477003591859/100000000000000),(538066917/100000000000000),(-3780937/25000000000000)⟩
def e316 : ℝ := (7667157/25000000000000)
theorem h316 : Model (fun x => f316 ((63/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(49696587750861/100000000000000),(1068656708727/50000000000000),(-1863941233/50000000000000),(-93341/100000000000)⟩
def e317 : ℝ := (147218139/100000000000000)
theorem h317 : Model (fun x => f317 ((63/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(6310677809633/20000000000000),(107022118353/12500000000000),(-1595701977/10000000000000),(194021901/100000000000000)⟩
def e318 : ℝ := (102190887/100000000000000)
theorem h318 : Model (fun x => f318 ((63/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-4997854288411/6250000000000),(-356865882881/20000000000000),(42521805011/100000000000000),(-206022581/25000000000000)⟩
def e319 : ℝ := (183412717/100000000000000)
theorem h319 : Model (fun x => f319 ((63/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((63/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-43659/1600),(-693/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((63/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((63/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(6111/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((63/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(200781/1600),(1247/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((63/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((63/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(373581/1600),(1247/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((63/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1867905/32),(6235/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((63/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((63/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(949350276990106021/100000000000000),(2607728099293337/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (61621/50000000000000)
theorem h329 : Model (fun x => f329 ((63/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10533519863/100000000000000),(-14467029/25000000000000),(33021/4000000000000),(-1831/25000000000000)⟩
def e330 : ℝ := (83/100000000000000)
theorem h330 : Model (fun x => f330 ((63/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (236022267793904757/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(614862950615531/100000000000000),(363450773041/50000000000000),(7532602379/100000000000000),(-158979/2500000000000)⟩
def e331 : ℝ := (4581449/50000000000000)
theorem h331 : Model (fun x => f331 ((63/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((63/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(423/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((63/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((63/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((63/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(565806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((63/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((63/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((63/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1255098271203401/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (129/12500000000000)
theorem h339 : Model (fun x => f339 ((63/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3664193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((63/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((63/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((63/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2064803457592939/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (129/12500000000000)
theorem h343 : Model (fun x => f343 ((63/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(605384495751/12500000000000),(-6608652327/100000000000000),(9017881/100000000000000),(-6153/50000000000000)⟩
def e344 : ℝ := (11/50000000000000)
theorem h344 : Model (fun x => f344 ((63/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1030992957978713/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(121570725444867/100000000000000),(454211573779/50000000000000),(-619797507/50000000000000),(845741/50000000000000)⟩
def e345 : ℝ := (3339/100000000000000)
theorem h345 : Model (fun x => f345 ((63/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(221570725444867/100000000000000),(454211573779/50000000000000),(-619797507/50000000000000),(845741/50000000000000)⟩
def e346 : ℝ := (3339/100000000000000)
theorem h346 : Model (fun x => f346 ((63/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(110785362722433/100000000000000),(454211573779/100000000000000),(-619797507/100000000000000),(845741/100000000000000)⟩
def e347 : ℝ := (167/10000000000000)
theorem h347 : Model (fun x => f347 ((63/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(10785362722433/100000000000000),(454211573779/100000000000000),(-619797507/100000000000000),(845741/100000000000000)⟩
def e348 : ℝ := (167/10000000000000)
theorem h348 : Model (fun x => f348 ((63/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(408850743380407/100000000000000),(167625699847/10000000000000),(-2287347943/100000000000000),(3121187/100000000000000)⟩
def e349 : ℝ := (1233/20000000000000)
theorem h349 : Model (fun x => f349 ((63/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(691141257273673/25000000000000),(167625699847/10000000000000),(-2287347943/100000000000000),(3121187/100000000000000)⟩
def e350 : ℝ := (3083/50000000000000)
theorem h350 : Model (fun x => f350 ((63/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3062733395180089/100000000000000),(1441402172271/10000000000000),(-1506874819/12500000000000),(75751/1250000000000)⟩
def e351 : ℝ := (47813/50000000000000)
theorem h351 : Model (fun x => f351 ((63/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8345114347561041/100000000000000),(1441402172271/10000000000000),(-1506874819/12500000000000),(75751/1250000000000)⟩
def e352 : ℝ := (95627/100000000000000)
theorem h352 : Model (fun x => f352 ((63/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(9245165199547297/100000000000000),(13468275365027/25000000000000),(392170357/100000000000000),(-66801211/100000000000000)⟩
def e353 : ℝ := (470269/100000000000000)
theorem h353 : Model (fun x => f353 ((63/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3628553204648729/25000000000000),(13468275365027/25000000000000),(392170357/100000000000000),(-66801211/100000000000000)⟩
def e354 : ℝ := (47027/10000000000000)
theorem h354 : Model (fun x => f354 ((63/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(4019905829346561/25000000000000),(62804372663689/50000000000000),(155173600127/100000000000000),(-70844043/25000000000000)⟩
def e355 : ℝ := (916613/100000000000000)
theorem h355 : Model (fun x => f355 ((63/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(18415337603100529/100000000000000),(62804372663689/50000000000000),(155173600127/100000000000000),(-70844043/25000000000000)⟩
def e356 : ℝ := (458307/50000000000000)
theorem h356 : Model (fun x => f356 ((63/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(31877341500243/156250000000),(222800698865791/100000000000000),(78537661417/12500000000000),(-231896681/100000000000000)⟩
def e357 : ℝ := (2518917/100000000000000)
theorem h357 : Model (fun x => f357 ((63/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(2600484939067059/12500000000000),(222800698865791/100000000000000),(78537661417/12500000000000),(-231896681/100000000000000)⟩
def e358 : ℝ := (1259459/50000000000000)
theorem h358 : Model (fun x => f358 ((63/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(1440478336143841/6250000000000),(341324190927561/100000000000000),(1579110498727/100000000000000),(278388673/20000000000000)⟩
def e359 : ℝ := (6223141/100000000000000)
theorem h359 : Model (fun x => f359 ((63/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(2878754291335301/12500000000000),(341324190927561/100000000000000),(1579110498727/100000000000000),(278388673/20000000000000)⟩
def e360 : ℝ := (3111571/50000000000000)
theorem h360 : Model (fun x => f360 ((63/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(510278141366947/2000000000000),(30171395272109/6250000000000),(157850884723/5000000000000),(679382777/10000000000000)⟩
def e361 : ℝ := (7895907/100000000000000)
theorem h361 : Model (fun x => f361 ((63/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(25517240401680683/100000000000000),(30171395272109/6250000000000),(157850884723/5000000000000),(679382777/10000000000000)⟩
def e362 : ℝ := (1973977/25000000000000)
theorem h362 : Model (fun x => f362 ((63/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(2752126934076481/100000000000000),(167967769909699/100000000000000),(1187506049219/50000000000000),(6148031797/50000000000000)⟩
def e363 : ℝ := (16711221/100000000000000)
theorem h363 : Model (fun x => f363 ((63/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(12273396593541/10000000000000),(251599969769/25000000000000),(86223963/12500000000000),(-375647/10000000000000)⟩
def e364 : ℝ := (15253/100000000000000)
theorem h364 : Model (fun x => f364 ((63/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(210785362722433/100000000000000),(454211573779/100000000000000),(-619797507/100000000000000),(845741/100000000000000)⟩
def e365 : ℝ := (167/10000000000000)
theorem h365 : Model (fun x => f365 ((63/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(111076172845069/25000000000000),(957411513317/50000000000000),(-54980331/10000000000000),(-516247/25000000000000)⟩
def e366 : ℝ := (18593/100000000000000)
theorem h366 : Model (fun x => f366 ((63/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(936529255318701/100000000000000),(242169999731/4000000000000),(2392326751/50000000000000),(-7480161/50000000000000)⟩
def e367 : ℝ := (56961/100000000000000)
theorem h367 : Model (fun x => f367 ((63/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(246758323478153/12500000000000),(17015297077931/100000000000000),(31779868437/100000000000000),(-19702599/50000000000000)⟩
def e368 : ℝ := (36521/20000000000000)
theorem h368 : Model (fun x => f368 ((63/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(60571255336093/2500000000000),(40750552672189/100000000000000),(27982946209/12500000000000),(314683883/100000000000000)⟩
def e369 : ℝ := (673833/50000000000000)
theorem h369 : Model (fun x => f369 ((63/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(110785362722433/12500000000000),(454211573779/12500000000000),(-619797507/12500000000000),(845741/12500000000000)⟩
def e370 : ℝ := (167/1250000000000)
theorem h370 : Model (fun x => f370 ((63/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(504508433857437/50000000000000),(1160023117327/25000000000000),(-66696693/1562500000000),(1504729/50000000000000)⟩
def e371 : ℝ := (28613/100000000000000)
theorem h371 : Model (fun x => f371 ((63/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(554508433857437/50000000000000),(1160023117327/25000000000000),(-66696693/1562500000000),(1504729/50000000000000)⟩
def e372 : ℝ := (28613/100000000000000)
theorem h372 : Model (fun x => f372 ((63/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(13434908773278341/50000000000000),(22574119724729/4000000000000),(4270126572077/100000000000000),(2442163059/20000000000000)⟩
def e373 : ℝ := (10996147/50000000000000)
theorem h373 : Model (fun x => f373 ((63/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(37216478983/10000000000000),(-3908331583/50000000000000),(1050311/1000000000000),(-141613/12500000000000)⟩
def e374 : ℝ := (5671/50000000000000)
theorem h374 : Model (fun x => f374 ((63/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (26301182194058791/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(512122371003/5000000000000),(409992405529/100000000000000),(-55997073/4000000000000),(5354363/100000000000000)⟩
def e375 : ℝ := (778673/100000000000000)
theorem h375 : Model (fun x => f375 ((63/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(121570725444867/50000000000000),(454211573779/25000000000000),(-619797507/25000000000000),(845741/25000000000000)⟩
def e376 : ℝ := (3339/50000000000000)
theorem h376 : Model (fun x => f376 ((63/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(22566158006483/50000000000000),(-92519534083/50000000000000),(252785613/25000000000000),(-2762683/50000000000000)⟩
def e377 : ℝ := (7643/25000000000000)
theorem h377 : Model (fun x => f377 ((63/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (110330530503737/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(21947073594813/20000000000000),(370078136329/100000000000000),(-404456981/20000000000000),(11050729/100000000000000)⟩
def e378 : ℝ := (41961/20000000000000)
theorem h378 : Model (fun x => f378 ((63/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1947073594813/20000000000000),(370078136329/100000000000000),(-404456981/20000000000000),(11050729/100000000000000)⟩
def e379 : ℝ := (41961/20000000000000)
theorem h379 : Model (fun x => f379 ((63/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(40497576276143/10000000000000),(1365764550737/100000000000000),(-7463194293/100000000000000),(10195613/25000000000000)⟩
def e380 : ℝ := (774283/100000000000000)
theorem h380 : Model (fun x => f380 ((63/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(552138009695143/20000000000000),(1365764550737/100000000000000),(-7463194293/100000000000000),(10195613/25000000000000)⟩
def e381 : ℝ := (193571/25000000000000)
theorem h381 : Model (fun x => f381 ((63/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3029453383318219/100000000000000),(11715437036629/100000000000000),(-58964385849/100000000000000),(36823731/12500000000000)⟩
def e382 : ℝ := (710193/10000000000000)
theorem h382 : Model (fun x => f382 ((63/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8311834335699171/100000000000000),(11715437036629/100000000000000),(-58964385849/100000000000000),(36823731/12500000000000)⟩
def e383 : ℝ := (7101931/100000000000000)
theorem h383 : Model (fun x => f383 ((63/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(4560510996837083/50000000000000),(2726016221639/6250000000000),(-189437485837/100000000000000),(393326863/50000000000000)⟩
def e384 : ℝ := (14436447/50000000000000)
theorem h384 : Model (fun x => f384 ((63/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(2878013922544357/20000000000000),(2726016221639/6250000000000),(-189437485837/100000000000000),(393326863/50000000000000)⟩
def e385 : ℝ := (5774579/20000000000000)
theorem h385 : Model (fun x => f385 ((63/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(15790995841244361/100000000000000),(50558482174389/50000000000000),(-337473887297/100000000000000),(435166603/50000000000000)⟩
def e386 : ℝ := (73673257/100000000000000)
theorem h386 : Model (fun x => f386 ((63/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(9063355063479323/50000000000000),(50558482174389/50000000000000),(-337473887297/100000000000000),(435166603/50000000000000)⟩
def e387 : ℝ := (36836629/50000000000000)
theorem h387 : Model (fun x => f387 ((63/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(795656482376407/4000000000000),(22255507990993/12500000000000),(-181345078769/50000000000000),(-335593221/100000000000000)⟩
def e388 : ℝ := (3515953/2500000000000)
theorem h388 : Model (fun x => f388 ((63/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(20293793011791127/100000000000000),(22255507990993/12500000000000),(-181345078769/50000000000000),(-335593221/100000000000000)⟩
def e389 : ℝ := (140638121/100000000000000)
theorem h389 : Model (fun x => f389 ((63/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(22269468437384081/100000000000000),(27048019967581/10000000000000),(-149495538081/100000000000000),(-383555949/12500000000000)⟩
def e390 : ℝ := (223605961/100000000000000)
theorem h390 : Model (fun x => f390 ((63/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(22251849389765033/100000000000000),(27048019967581/10000000000000),(-149495538081/100000000000000),(-383555949/12500000000000)⟩
def e391 : ℝ := (111802981/50000000000000)
theorem h391 : Model (fun x => f391 ((63/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(6104537202223349/25000000000000),(189580835965807/50000000000000),(96735702997/25000000000000),(-6931311233/100000000000000)⟩
def e392 : ℝ := (157531831/50000000000000)
theorem h392 : Model (fun x => f392 ((63/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(24421482142226729/100000000000000),(189580835965807/50000000000000),(96735702997/25000000000000),(-6931311233/100000000000000)⟩
def e393 : ℝ := (315063663/100000000000000)
theorem h393 : Model (fun x => f393 ((63/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(297190143908293/12500000000000),(127291349955031/100000000000000),(189398561763/20000000000000),(-842355071/20000000000000)⟩
def e394 : ℝ := (92486287/100000000000000)
theorem h394 : Model (fun x => f394 ((63/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(60209254922017/50000000000000),(101526651173/12500000000000),(-613749059/20000000000000),(9285047/100000000000000)⟩
def e395 : ℝ := (292581/50000000000000)
theorem h395 : Model (fun x => f395 ((63/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(41947073594813/20000000000000),(370078136329/100000000000000),(-404456981/20000000000000),(11050729/100000000000000)⟩
def e396 : ℝ := (41961/20000000000000)
theorem h396 : Model (fun x => f396 ((63/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(109972311448041/25000000000000),(776184741021/50000000000000),(-1422663021/20000000000000),(6277301/20000000000000)⟩
def e397 : ℝ := (251193/25000000000000)
theorem h397 : Model (fun x => f397 ((63/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(461301664170267/50000000000000),(4883801768217/100000000000000),(-18069971379/100000000000000),(14180353/25000000000000)⟩
def e398 : ℝ := (3470263/100000000000000)
theorem h398 : Model (fun x => f398 ((63/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(193502548563599/10000000000000),(546296512517/4000000000000),(-38482906241/100000000000000),(863779/1562500000000)⟩
def e399 : ℝ := (5177711/50000000000000)
theorem h399 : Model (fun x => f399 ((63/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2330128854905141/100000000000000),(16081292795927/50000000000000),(5205765139/100000000000000),(-30339803/6250000000000)⟩
def e400 : ℝ := (6715193/25000000000000)
theorem h400 : Model (fun x => f400 ((63/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(21947073594813/2500000000000),(370078136329/12500000000000),(-404456981/2500000000000),(11050729/12500000000000)⟩
def e401 : ℝ := (41961/2500000000000)
theorem h401 : Model (fun x => f401 ((63/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(499150726818277/50000000000000),(235802393751/6250000000000),(-3849404907/20000000000000),(97690879/100000000000000)⟩
def e402 : ℝ := (1131801/50000000000000)
theorem h402 : Model (fun x => f402 ((63/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(549150726818277/50000000000000),(235802393751/6250000000000),(-3849404907/20000000000000),(97690879/100000000000000)⟩
def e403 : ℝ := (1131801/50000000000000)
theorem h403 : Model (fun x => f403 ((63/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(25591839085027953/100000000000000),(220577069480009/50000000000000),(411068434639/50000000000000),(-9049172237/100000000000000)⟩
def e404 : ℝ := (36170607/10000000000000)
theorem h404 : Model (fun x => f404 ((63/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(390749565389/100000000000000),(-3367885901/50000000000000),(2071179/2000000000000),(-357651/25000000000000)⟩
def e405 : ℝ := (2509/10000000000000)
theorem h405 : Model (fun x => f405 ((63/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (502997067966407/2000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(2322538391401/25000000000000),(337245997433/100000000000000),(-301443579/12500000000000),(68609/390625000000)⟩
def e406 : ℝ := (392757/25000000000000)
theorem h406 : Model (fun x => f406 ((63/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(305196890401/1562500000000),(373619201481/50000000000000),(-3811475457/100000000000000),(22918267/100000000000000)⟩
def e407 : ℝ := (2349701/100000000000000)
theorem h407 : Model (fun x => f407 ((63/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(120098726752411/100000000000000),(4736474871139/100000000000000),(-16532349787/100000000000000),(168254647/100000000000000)⟩
def e408 : ℝ := (16493271/100000000000000)
theorem h408 : Model (fun x => f408 ((63/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(190632899607/250000000000),(359383603183/20000000000000),(-19509619107/50000000000000),(363090667/50000000000000)⟩
def e409 : ℝ := (4023837/12500000000000)
theorem h409 : Model (fun x => f409 ((63/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-58007949559/1562500000000),(1258860151/10000000000000),(3502566797/100000000000000),(-9790899/10000000000000)⟩
def e410 : ℝ := (215603413/100000000000000)
theorem h410 : Model (fun x => f410 ((63/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1584526350585937/100000000000000),(28997149658203/25000000000000),(345303/10240000),(4977/10240000)⟩
def e411 : ℝ := (347656251/100000000000000)
theorem h411 : Model (fun x => f411 ((63/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(33489/1600),(183/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((63/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(6128487/64000),(100467/64000),(549/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((63/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(151730455323802457/100000000000000),(3398543858334857/25000000000000),(259287500969329/50000000000000),(10967390814331/100000000000000)⟩
def e414 : ℝ := (70673052563/50000000000000)
theorem h414 : Model (fun x => f414 ((63/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(32953173371/50000000000000),(-590482931/10000000000000),(151894033/50000000000000),(-2950087/25000000000000)⟩
def e415 : ℝ := (36677/6250000000000)
theorem h415 : Model (fun x => f415 ((63/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (68803298075802457/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5101121866009/100000000000000),(73462308901/100000000000000),(-1618918071/50000000000000),(19532523/25000000000000)⟩
def e416 : ℝ := (23203703/25000000000000)
theorem h416 : Model (fun x => f416 ((63/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1388613094233/100000000000000),(86050910411/100000000000000),(52946131/20000000000000),(-9889449/50000000000000)⟩
def e417 : ℝ := (12336729/4000000000000)
theorem h417 : Model (fun x => f417 ((63/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((63/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((4165178758679/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (31/20) (8/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (31/20) (8/5) ≤ (4167029268029/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(63/40)-(1/40)) (by norm_num : ((63/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel11


noncomputable section
namespace Hf4Quad.Panel12
open Hf4Quad.Dag

def p0 : Cubic := ⟨(13/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((13/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((13/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((13/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((13/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(17797619047619/6250000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((13/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-17797619047619/6250000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((13/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-193333333333333/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((13/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((13/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(169/64),(13/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((13/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(9989666005291/3125000000000),(4917989417989/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((13/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-9989666005291/3125000000000),(-4917989417989/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((13/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-102600529100529/20000000000000),(-1421693121693/10000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((13/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((13/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(2197/512),(507/2560),(39/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((13/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(4180561704282407/100000000000000),(192949001736111/100000000000000),(593689236111/20000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((13/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-4180561704282407/100000000000000),(-192949001736111/100000000000000),(-593689236111/20000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((13/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1173391087446263/25000000000000),(-207165932953041/100000000000000),(-380513444527/12500000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((13/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((13/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(28561/4096),(2197/5120),(507/51200),(13/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((13/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(973992435515873/50000000000000),(29968998015873/25000000000000),(2766369047619/100000000000000),(28373015873/100000000000000)⟩
def e19 : ℝ := (21825397/20000000000000)
theorem h19 : Model (fun x => f19 ((13/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1372789739376653/50000000000000),(-87289940889549/100000000000000),(-277738508597/100000000000000),(3287553737/25000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((13/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((13/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(566548156738281/50000000000000),(21790313720703/25000000000000),(2197/81920),(169/409600)⟩
def e22 : ℝ := (19897461/6250000000000)
theorem h22 : Model (fun x => f22 ((13/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(7381912649649157/100000000000000),(567839434588393/100000000000000),(17471982602719/100000000000000),(268799732349/100000000000000)⟩
def e23 : ℝ := (1037026191/50000000000000)
theorem h23 : Model (fun x => f23 ((13/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(4636333170895851/100000000000000),(120137373424711/25000000000000),(8597122047061/50000000000000),(281949947297/100000000000000)⟩
def e24 : ℝ := (1091589687/50000000000000)
theorem h24 : Model (fun x => f24 ((13/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((13/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(1841281509399413/100000000000000),(169964447021483/100000000000000),(653709411621/10000000000000),(134094238281/100000000000000)⟩
def e26 : ℝ := (1556787113/100000000000000)
theorem h26 : Model (fun x => f26 ((13/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(2067301250235743/50000000000000),(190827807714067/50000000000000),(14679062131849/100000000000000),(150554483403/50000000000000)⟩
def e27 : ℝ := (3495769583/100000000000000)
theorem h27 : Model (fun x => f27 ((13/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(8770935671367337/100000000000000),(431102554563489/50000000000000),(31873306225971/100000000000000),(583058914103/100000000000000)⟩
def e28 : ℝ := (5678948957/100000000000000)
theorem h28 : Model (fun x => f28 ((13/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((13/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(1496041226387023/50000000000000),(64444852828979/20000000000000),(7435944557189/50000000000000),(381330490111/100000000000000)⟩
def e30 : ℝ := (1184210939/20000000000000)
theorem h30 : Model (fun x => f30 ((13/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(710025915380507/100000000000000),(76464329348669/100000000000000),(705824578603/20000000000000),(90490330589/100000000000000)⟩
def e31 : ℝ := (8781723/625000000000)
theorem h31 : Model (fun x => f31 ((13/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(2370240396686961/25000000000000),(938669438475647/100000000000000),(17701214559493/50000000000000),(168387311173/25000000000000)⟩
def e32 : ℝ := (7084024637/100000000000000)
theorem h32 : Model (fun x => f32 ((13/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((13/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(362505/64),(5577/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((13/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((13/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(28717/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((13/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(821977/64),(45557/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((13/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((13/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(967897/64),(45557/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((13/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-967897/64),(-45557/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((13/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((13/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(21/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((13/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(441/64),(21/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((13/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((13/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(46305/32),(441/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((13/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(34553503941/50000000000000),(-32908099/2500000000000),(18804627/100000000000000),(-238789/100000000000000)⟩
def e46 : ℝ := (2923/100000000000000)
theorem h46 : Model (fun x => f46 ((13/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (113547/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-26128306878111/2500000000000),(368570717/160000000000),(-447547117/20000000000000),(21731181/100000000000000)⟩
def e47 : ℝ := (22035681/25000000000000)
theorem h47 : Model (fun x => f47 ((13/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((13/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(29/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((13/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((13/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((13/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(30208333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((13/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(55208333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((13/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((13/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(55208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((13/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((13/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1159374999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((13/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((13/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(5208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((13/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(60384114583329/25000000000000),(10572916666649/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (39/50000000000000)
theorem h60 : Model (fun x => f60 ((13/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(7619900173611/6250000000000),(920138888887/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((13/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((13/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(55208333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((13/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(306521267361109/25000000000000),(5086805555547/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((13/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(331521267361109/25000000000000),(5086805555547/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((13/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(400372363902873/12500000000000),(30498471860481/20000000000000),(1025485568569/100000000000000),(1019061053/50000000000000)⟩
def e66 : ℝ := (317047/50000000000000)
theorem h66 : Model (fun x => f66 ((13/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(105208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((13/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(110687934027777/25000000000000),(1753472222219/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((13/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(465811722366893/50000000000000),(5534396701379/100000000000000),(2739800347/25000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (9/20000000000000)
theorem h69 : Model (fun x => f69 ((13/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(7459925616708069/25000000000000),(1597920129897477/100000000000000),(18344216991533/100000000000000),(92685704569/100000000000000)⟩
def e70 : ℝ := (242455513/100000000000000)
theorem h70 : Model (fun x => f70 ((13/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((13/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(160017903645831/781250000000),(19322916666627/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((13/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(2133572048610943/100000000000000),(25361328124957/25000000000000),(337239583331/50000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (767/100000000000000)
theorem h73 : Model (fun x => f73 ((13/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(9938428707573237/50000000000000),(1063168655911719/100000000000000),(12131814532727/100000000000000),(11984419957/20000000000000)⟩
def e74 : ℝ := (148704431/100000000000000)
theorem h74 : Model (fun x => f74 ((13/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(39773247905583/80000000000),(665272196452299/25000000000000),(1523801576213/5000000000000),(76303902177/50000000000000)⟩
def e75 : ℝ := (48894993/12500000000000)
theorem h75 : Model (fun x => f75 ((13/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((13/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(53339301215277/781250000000),(6440972222209/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((13/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(271267361111/25000000000000),(17361111111/20000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((13/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(113028067129/100000000000000),(2712673611/20000000000000),(271267361/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/50000000000000)
theorem h79 : Model (fun x => f79 ((13/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(7716912791519/100000000000000),(492135193103/50000000000000),(44139971933/100000000000000),(196656273/25000000000000)⟩
def e80 : ℝ := (4262051/100000000000000)
theorem h80 : Model (fun x => f80 ((13/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(16237670665487/100000000000000),(2103222740939/100000000000000),(48489492109/50000000000000),(1839106847/100000000000000)⟩
def e81 : ℝ := (1532929/12500000000000)
theorem h81 : Model (fun x => f81 ((13/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(49732797552644237/100000000000000),(532638401710027/20000000000000),(15286505254239/50000000000000),(154446911201/100000000000000)⟩
def e82 : ℝ := (25213961/6250000000000)
theorem h82 : Model (fun x => f82 ((13/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(183964953/1562500000000),(941900559/50000000000000),(113028067/100000000000000),(3014081/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((13/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(1226433019/100000000000000),(245286603/100000000000000),(1226433/6250000000000),(784917/100000000000000)⟩
def e84 : ℝ := (15827/100000000000000)
theorem h84 : Model (fun x => f84 ((13/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(127753439/100000000000000),(1226433/4000000000000),(1533041/50000000000000),(40881/25000000000000)⟩
def e85 : ℝ := (4987/100000000000000)
theorem h85 : Model (fun x => f85 ((13/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(13307649/100000000000000),(3726141/100000000000000),(13973/3125000000000),(29809/100000000000000)⟩
def e86 : ℝ := (49/4000000000000)
theorem h86 : Model (fun x => f86 ((13/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(39922947/100000000000000),(11178423/100000000000000),(41919/3125000000000),(89427/100000000000000)⟩
def e87 : ℝ := (147/4000000000000)
theorem h87 : Model (fun x => f87 ((13/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-39922947/100000000000000),(-11178423/100000000000000),(-41919/3125000000000),(-89427/100000000000000)⟩
def e88 : ℝ := (147/4000000000000)
theorem h88 : Model (fun x => f88 ((13/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(4973279751272129/10000000000000),(41612374958933/1562500000000),(3057300916707/10000000000000),(77223410887/50000000000000)⟩
def e89 : ℝ := (403427051/100000000000000)
theorem h89 : Model (fun x => f89 ((13/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(160017903645831/625000000000),(19322916666627/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((13/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1960290998294001/100000000000000),(7763528706101/50000000000000),(46119972509/100000000000000),(60884451/100000000000000)⟩
def e91 : ℝ := (30267/100000000000000)
theorem h91 : Model (fun x => f91 ((13/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(501890649732478901/100000000000000),(1940806360814961/25000000000000),(48957732016897/100000000000000),(80657232783/50000000000000)⟩
def e92 : ℝ := (58771047/20000000000000)
theorem h92 : Model (fun x => f92 ((13/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(19924658897/100000000000000),(-61638773/20000000000000),(2823547/100000000000000),(-1251/6250000000000)⟩
def e93 : ℝ := (19/12500000000000)
theorem h93 : Model (fun x => f93 ((13/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (494078304948881359/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(1981818052869/20000000000000),(377358490421/100000000000000),(-355998823/50000000000000),(223853/12500000000000)⟩
def e94 : ℝ := (154467/50000000000000)
theorem h94 : Model (fun x => f94 ((13/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(30208333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((13/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(11320754716981/25000000000000),(-170879316483/100000000000000),(644827609/100000000000000),(-76041/3125000000000)⟩
def e96 : ℝ := (461/5000000000000)
theorem h96 : Model (fun x => f96 ((13/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (109999999999997/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(27358490566037/25000000000000),(85439658241/25000000000000),(-64482761/5000000000000),(2433311/50000000000000)⟩
def e97 : ℝ := (31499/50000000000000)
theorem h97 : Model (fun x => f97 ((13/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(574528301886777/25000000000000),(1794232823061/25000000000000),(-1354137981/5000000000000),(51099531/50000000000000)⟩
def e98 : ℝ := (661479/50000000000000)
theorem h98 : Model (fun x => f98 ((13/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(2358490566037/25000000000000),(85439658241/25000000000000),(-64482761/5000000000000),(2433311/50000000000000)⟩
def e99 : ℝ := (31499/50000000000000)
theorem h99 : Model (fun x => f99 ((13/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(43360626557479/20000000000000),(1066383658989/12500000000000),(-7664931993/100000000000000),(-12726687/20000000000000)⟩
def e100 : ℝ := (658029/25000000000000)
theorem h100 : Model (fun x => f100 ((13/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(119757920968309/100000000000000),(46750001679/6250000000000),(-827325991/50000000000000),(918229/50000000000000)⟩
def e101 : ℝ := (188339/100000000000000)
theorem h101 : Model (fun x => f101 ((13/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(27358490566037/2500000000000),(85439658241/2500000000000),(-64482761/500000000000),(2433311/5000000000000)⟩
def e102 : ℝ := (31499/5000000000000)
theorem h102 : Model (fun x => f102 ((13/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1214097543609789/100000000000000),(520698294563/12500000000000),(-7275602091/50000000000000),(25251339/50000000000000)⟩
def e103 : ℝ := (818319/100000000000000)
theorem h103 : Model (fun x => f103 ((13/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1314097543609789/100000000000000),(520698294563/12500000000000),(-7275602091/50000000000000),(25251339/50000000000000)⟩
def e104 : ℝ := (818319/100000000000000)
theorem h104 : Model (fun x => f104 ((13/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1424502321214113/50000000000000),(12113769346571/10000000000000),(22309690809/10000000000000),(-2287376689/100000000000000)⟩
def e105 : ℝ := (39321091/100000000000000)
theorem h105 : Model (fun x => f105 ((13/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(52358490566037/25000000000000),(85439658241/25000000000000),(-64482761/5000000000000),(2433311/50000000000000)⟩
def e106 : ℝ := (31499/50000000000000)
theorem h106 : Model (fun x => f106 ((13/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(87725169099321/20000000000000),(178939661599/12500000000000),(-2116981211/50000000000000),(5784851/50000000000000)⟩
def e107 : ℝ := (62867/20000000000000)
theorem h107 : Model (fun x => f107 ((13/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(918631487738159/100000000000000),(2248562540093/50000000000000),(-2407945611/25000000000000),(12645577/100000000000000)⟩
def e108 : ℝ := (550401/50000000000000)
theorem h108 : Model (fun x => f108 ((13/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(26171853732467629/100000000000000),(248186459601209/20000000000000),(451421381957/6250000000000),(-22287061519/100000000000000)⟩
def e109 : ℝ := (1578033/312500000000)
theorem h109 : Model (fun x => f109 ((13/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2514916340334489/12500000000000),(981750035259/781250000000),(-17373845811/6250000000000),(19282809/6250000000000)⟩
def e110 : ℝ := (3955119/12500000000000)
theorem h110 : Model (fun x => f110 ((13/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(94902503408819/5000000000000),(80614644404711/100000000000000),(28754582427/20000000000000),(-1562420379/100000000000000)⟩
def e111 : ℝ := (6655047/25000000000000)
theorem h111 : Model (fun x => f111 ((13/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(871804278965191/5000000000000),(82590919288027/10000000000000),(1190817145073/25000000000000),(-15411845667/100000000000000)⟩
def e112 : ℝ := (341610497/100000000000000)
theorem h112 : Model (fun x => f112 ((13/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(43607939311771449/100000000000000),(413368298177263/20000000000000),(2996502672901/25000000000000),(-18849453593/50000000000000)⟩
def e113 : ℝ := (846581057/100000000000000)
theorem h113 : Model (fun x => f113 ((13/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(838305446778163/12500000000000),(327250011753/781250000000),(-5791281937/6250000000000),(6427603/6250000000000)⟩
def e114 : ℝ := (1318373/12500000000000)
theorem h114 : Model (fun x => f114 ((13/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(889996440013/100000000000000),(8060345117/12500000000000),(462329229/50000000000000),(-3948393/50000000000000)⟩
def e115 : ℝ := (62343/100000000000000)
theorem h115 : Model (fun x => f115 ((13/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(83961928303/100000000000000),(9124919/100000000000),(148064723/50000000000000),(1626827/100000000000000)⟩
def e116 : ℝ := (21311/50000000000000)
theorem h116 : Model (fun x => f116 ((13/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(87982177273/1562500000000),(647127517719/100000000000000),(11802100429/50000000000000),(56194023/25000000000000)⟩
def e117 : ℝ := (660761/20000000000000)
theorem h117 : Model (fun x => f117 ((13/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(11792931836743/100000000000000),(1374548749183/100000000000000),(12893552151/25000000000000),(135838797/25000000000000)⟩
def e118 : ℝ := (7431629/100000000000000)
theorem h118 : Model (fun x => f118 ((13/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(340779158153189/781250000000),(1034108019817749/50000000000000),(752349056263/6250000000000),(-18577775999/50000000000000)⟩
def e119 : ℝ := (427006343/50000000000000)
theorem h119 : Model (fun x => f119 ((13/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(990117079/12500000000000),(1147788553/100000000000000),(58039119/100000000000000),(131491/12500000000000)⟩
def e120 : ℝ := (6419/100000000000000)
theorem h120 : Model (fun x => f120 ((13/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(186814543/25000000000000),(135352423/100000000000000),(4647951/50000000000000),(11327/4000000000000)⟩
def e121 : ℝ := (3549/100000000000000)
theorem h121 : Model (fun x => f121 ((13/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(70496053/100000000000000),(3064583/20000000000000),(1329913/100000000000000),(28387/50000000000000)⟩
def e122 : ℝ := (1209/100000000000000)
theorem h122 : Model (fun x => f122 ((13/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(6650571/100000000000000),(421621/25000000000000),(176921/100000000000000),(4853/50000000000000)⟩
def e123 : ℝ := (299/100000000000000)
theorem h123 : Model (fun x => f123 ((13/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(19951713/100000000000000),(1264863/25000000000000),(530763/100000000000000),(14559/50000000000000)⟩
def e124 : ℝ := (897/100000000000000)
theorem h124 : Model (fun x => f124 ((13/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-19951713/100000000000000),(-1264863/25000000000000),(-530763/100000000000000),(-14559/50000000000000)⟩
def e125 : ℝ := (897/100000000000000)
theorem h125 : Model (fun x => f125 ((13/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(43619732223656479/100000000000000),(1034108017288023/50000000000000),(2407516873889/20000000000000),(-9288895279/25000000000000)⟩
def e126 : ℝ := (854013583/100000000000000)
theorem h126 : Model (fun x => f126 ((13/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2514916340334489/10000000000000),(981750035259/625000000000),(-17373845811/5000000000000),(19282809/5000000000000)⟩
def e127 : ℝ := (3955119/10000000000000)
theorem h127 : Model (fun x => f127 ((13/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1923926323376117/100000000000000),(12558009657879/100000000000000),(-16650089347/100000000000000),(-9862201/50000000000000)⟩
def e128 : ℝ := (655543/20000000000000)
theorem h128 : Model (fun x => f128 ((13/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(94502221645669/19531250000),(386271121647761/6250000000000),(2213391060889/25000000000000),(-16832731827/25000000000000)⟩
def e129 : ℝ := (1670694399/100000000000000)
theorem h129 : Model (fun x => f129 ((13/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(4133500707/20000000000000),(-3299881/1250000000000),(2993831/100000000000000),(-6107/20000000000000)⟩
def e130 : ℝ := (379/100000000000000)
theorem h130 : Model (fun x => f130 ((13/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (477662114313595841/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(9015109699281/100000000000000),(62459336317/20000000000000),(-1666124197/100000000000000),(9142399/100000000000000)⟩
def e131 : ℝ := (529847/100000000000000)
theorem h131 : Model (fun x => f131 ((13/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(9462099981813/50000000000000),(344827586003/50000000000000),(-2378121843/100000000000000),(10933223/100000000000000)⟩
def e132 : ℝ := (838781/100000000000000)
theorem h132 : Model (fun x => f132 ((13/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-197782921628943/100000000000000),(-7164215627517/100000000000000),(3252464031/12500000000000),(-131065013/100000000000000)⟩
def e133 : ℝ := (26287653/100000000000000)
theorem h133 : Model (fun x => f133 ((13/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(61538461538461/100000000000000),(-946745562131/100000000000000),(728265817/5000000000000),(-22408179/10000000000000)⟩
def e134 : ℝ := (21883/625000000000)
theorem h134 : Model (fun x => f134 ((13/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (8/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-7607035447267/6250000000000),(-2536247045297/100000000000000),(55031315927/100000000000000),(-463645511/50000000000000)⟩
def e135 : ℝ := (44768571/100000000000000)
theorem h135 : Model (fun x => f135 ((13/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(142805/2048),(2197/512),(507/5120),(13/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((13/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((13/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(19773/256),(4563/1280),(351/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((13/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(300989/2048),(20111/2560),(3939/25600),(83/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((13/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-169/64),(-13/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((13/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(295581/2048),(19903/2560),(3923/25600),(83/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((13/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((13/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(39/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((13/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-39/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((13/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(275613/2048),(19519/2560),(3923/25600),(83/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((13/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(281757/2048),(19519/2560),(3923/25600),(83/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((13/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((13/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(281757/32),(19519/40),(3923/400),(83/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((13/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((13/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(26990145/4096),(415233/1024),(95823/10240),(2457/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((13/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(15175909577/100000000000000),(-58368883/6250000000000),(2244957/6250000000000),(-110521/10000000000000)⟩
def e151 : ℝ := (8691/25000000000000)
theorem h151 : Model (fun x => f151 ((13/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (1580655573/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(66811230541981/50000000000000),(-817456207879/100000000000000),(938301699/10000000000000),(-103188789/100000000000000)⟩
def e152 : ℝ := (299969063/50000000000000)
theorem h152 : Model (fun x => f152 ((13/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(37/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((13/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1073/64),(33/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((13/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(63/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((13/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3174603174603/50000000000000),(-30234315949/50000000000000),(143972933/25000000000000),(-1371171/25000000000000)⟩
def e156 : ℝ := (2637/5000000000000)
theorem h156 : Model (fun x => f156 ((13/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (78/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(53224206349203/50000000000000),(147864701429/50000000000000),(575891729/50000000000000),(-10969381/100000000000000)⟩
def e157 : ℝ := (333969/20000000000000)
theorem h157 : Model (fun x => f157 ((13/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(103224206349203/50000000000000),(147864701429/50000000000000),(575891729/50000000000000),(-10969381/100000000000000)⟩
def e158 : ℝ := (333969/20000000000000)
theorem h158 : Model (fun x => f158 ((13/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(103224206349203/100000000000000),(147864701429/100000000000000),(575891729/100000000000000),(-5484691/100000000000000)⟩
def e159 : ℝ := (834923/100000000000000)
theorem h159 : Model (fun x => f159 ((13/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(3224206349203/100000000000000),(147864701429/100000000000000),(575891729/100000000000000),(-5484691/100000000000000)⟩
def e160 : ℝ := (834923/100000000000000)
theorem h160 : Model (fun x => f160 ((13/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((13/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((13/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(190473237906267/50000000000000),(109138232007/20000000000000),(1062657357/50000000000000),(-10120561/50000000000000)⟩
def e163 : ℝ := (1540633/50000000000000)
theorem h163 : Model (fun x => f163 ((13/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2736660761526819/100000000000000),(109138232007/20000000000000),(1062657357/50000000000000),(-10120561/50000000000000)⟩
def e164 : ℝ := (3081267/100000000000000)
theorem h164 : Model (fun x => f164 ((13/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((13/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2824896351556113/100000000000000),(230492031661/5000000000000),(9380463413/50000000000000),(-20588243/12500000000000)⟩
def e166 : ℝ := (6521657/25000000000000)
theorem h166 : Model (fun x => f166 ((13/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1621455460787413/20000000000000),(230492031661/5000000000000),(9380463413/50000000000000),(-20588243/12500000000000)⟩
def e167 : ℝ := (26086629/100000000000000)
theorem h167 : Model (fun x => f167 ((13/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((13/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8368672653518097/100000000000000),(4186568196773/25000000000000),(72871284349/100000000000000),(-560387033/100000000000000)⟩
def e169 : ℝ := (95084933/100000000000000)
theorem h169 : Model (fun x => f169 ((13/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3409430068141429/25000000000000),(4186568196773/25000000000000),(72871284349/100000000000000),(-560387033/100000000000000)⟩
def e170 : ℝ := (47542467/50000000000000)
theorem h170 : Model (fun x => f170 ((13/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((13/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(3519357128870081/25000000000000),(37451581540299/100000000000000),(11157570891/6250000000000),(-1122250577/100000000000000)⟩
def e172 : ℝ := (13351963/6250000000000)
theorem h172 : Model (fun x => f172 ((13/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(16413142801194609/100000000000000),(37451581540299/100000000000000),(11157570891/6250000000000),(-1122250577/100000000000000)⟩
def e173 : ℝ := (213631409/100000000000000)
theorem h173 : Model (fun x => f173 ((13/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((13/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(211779204918681/1250000000000),(629283424083/1000000000000),(334176625087/100000000000000),(-315798823/20000000000000)⟩
def e175 : ℝ := (360889497/100000000000000)
theorem h175 : Model (fun x => f175 ((13/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(2168089668234429/12500000000000),(629283424083/1000000000000),(334176625087/100000000000000),(-315798823/20000000000000)⟩
def e176 : ℝ := (180444749/50000000000000)
theorem h176 : Model (fun x => f176 ((13/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((13/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(17903946823792461/100000000000000),(90603996536859/100000000000000),(6723584591/1250000000000),(-1724679907/100000000000000)⟩
def e178 : ℝ := (104458701/20000000000000)
theorem h178 : Model (fun x => f178 ((13/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(17886327776173413/100000000000000),(90603996536859/100000000000000),(6723584591/1250000000000),(-1724679907/100000000000000)⟩
def e179 : ℝ := (261146753/50000000000000)
theorem h179 : Model (fun x => f179 ((13/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((13/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(3692603978394411/20000000000000),(119972821508683/100000000000000),(198051639457/25000000000000),(-361042843/25000000000000)⟩
def e181 : ℝ := (694468127/100000000000000)
theorem h181 : Model (fun x => f181 ((13/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(4616588306326347/25000000000000),(119972821508683/100000000000000),(198051639457/25000000000000),(-361042843/25000000000000)⟩
def e182 : ℝ := (21702129/3125000000000)
theorem h182 : Model (fun x => f182 ((13/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(595393333156549/100000000000000),(31173389389823/100000000000000),(19330376833/6250000000000),(802921939/100000000000000)⟩
def e183 : ℝ := (182815293/100000000000000)
theorem h183 : Model (fun x => f183 ((13/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(26638091941057/25000000000000),(305264329041/100000000000000),(175944879/12500000000000),(-9619977/100000000000000)⟩
def e184 : ℝ := (869567/50000000000000)
theorem h184 : Model (fun x => f184 ((13/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(203224206349203/100000000000000),(147864701429/100000000000000),(575891729/100000000000000),(-5484691/100000000000000)⟩
def e185 : ℝ := (834923/100000000000000)
theorem h185 : Model (fun x => f185 ((13/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(206500390231317/50000000000000),(600993731899/100000000000000),(255934249/10000000000000),(-20589359/100000000000000)⟩
def e186 : ℝ := (170449/5000000000000)
theorem h186 : Model (fun x => f186 ((13/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(419658779155601/50000000000000),(183204711279/10000000000000),(1693659677/20000000000000),(-57248941/100000000000000)⟩
def e187 : ℝ := (10435141/100000000000000)
theorem h187 : Model (fun x => f187 ((13/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1705696446627449/100000000000000),(1241054401637/25000000000000),(990085743/4000000000000),(-139305449/100000000000000)⟩
def e188 : ℝ := (28382411/100000000000000)
theorem h188 : Model (fun x => f188 ((13/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(227182493843981/12500000000000),(10496374214019/100000000000000),(65536665013/100000000000000),(-83543551/50000000000000)⟩
def e189 : ℝ := (60639051/100000000000000)
theorem h189 : Model (fun x => f189 ((13/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((13/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(103224206349203/12500000000000),(147864701429/12500000000000),(575891729/12500000000000),(-5484691/12500000000000)⟩
def e191 : ℝ := (834923/12500000000000)
theorem h191 : Model (fun x => f191 ((13/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(233086504639463/25000000000000),(1488181940473/100000000000000),(11747447/195312500000),(-10699501/20000000000000)⟩
def e192 : ℝ := (4209259/50000000000000)
theorem h192 : Model (fun x => f192 ((13/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(258086504639463/25000000000000),(1488181940473/100000000000000),(11747447/195312500000),(-10699501/20000000000000)⟩
def e193 : ℝ := (4209259/50000000000000)
theorem h193 : Model (fun x => f193 ((13/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(93812377202351/500000000000),(8462875753361/6250000000000),(471042465689/50000000000000),(-109058329/10000000000000)⟩
def e194 : ℝ := (785008529/100000000000000)
theorem h194 : Model (fun x => f194 ((13/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(532978712309/100000000000000),(-384642859/10000000000000),(997647/100000000000000),(216913/100000000000000)⟩
def e195 : ℝ := (24491/100000000000000)
theorem h195 : Model (fun x => f195 ((13/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (18626125467893227/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(3173319720231/100000000000000),(143246149963/100000000000000),(227653229/50000000000000),(-3007289/50000000000000)⟩
def e196 : ℝ := (1175433/100000000000000)
theorem h196 : Model (fun x => f196 ((13/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(53224206349203/25000000000000),(147864701429/25000000000000),(575891729/25000000000000),(-10969381/50000000000000)⟩
def e197 : ℝ := (333969/10000000000000)
theorem h197 : Model (fun x => f197 ((13/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(48438250840943/100000000000000),(-69385929441/100000000000000),(-170846151/100000000000000),(3205543/100000000000000)⟩
def e198 : ℝ := (400283/100000000000000)
theorem h198 : Model (fun x => f198 ((13/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (6442234964777/3125000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(3222609322441/3125000000000),(138771858881/100000000000000),(341692299/100000000000000),(-641109/10000000000000)⟩
def e199 : ℝ := (1252469/50000000000000)
theorem h199 : Model (fun x => f199 ((13/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(97609322441/3125000000000),(138771858881/100000000000000),(341692299/100000000000000),(-641109/10000000000000)⟩
def e200 : ℝ := (1252469/50000000000000)
theorem h200 : Model (fun x => f200 ((13/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(380574815221603/100000000000000),(128033560277/25000000000000),(1261007293/100000000000000),(-946399/4000000000000)⟩
def e201 : ℝ := (9244417/100000000000000)
theorem h201 : Model (fun x => f201 ((13/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(171018068808493/6250000000000),(128033560277/25000000000000),(1261007293/100000000000000),(-946399/4000000000000)⟩
def e202 : ℝ := (4622209/50000000000000)
theorem h202 : Model (fun x => f202 ((13/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1410878522491151/50000000000000),(2162664997621/50000000000000),(11360782177/100000000000000),(-39265021/20000000000000)⟩
def e203 : ℝ := (39081379/50000000000000)
theorem h203 : Model (fun x => f203 ((13/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4052068998681627/50000000000000),(2162664997621/50000000000000),(11360782177/100000000000000),(-39265021/20000000000000)⟩
def e204 : ℝ := (78162759/100000000000000)
theorem h204 : Model (fun x => f204 ((13/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(835727061140837/10000000000000),(7853347275059/50000000000000),(45409192291/100000000000000),(-691476009/100000000000000)⟩
def e205 : ℝ := (142168761/50000000000000)
theorem h205 : Model (fun x => f205 ((13/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13626318230455989/100000000000000),(7853347275059/50000000000000),(45409192291/100000000000000),(-691476009/100000000000000)⟩
def e206 : ℝ := (284337523/100000000000000)
theorem h206 : Model (fun x => f206 ((13/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(1405193605120487/10000000000000),(17553393997833/50000000000000),(4607363987/4000000000000),(-1469986031/100000000000000)⟩
def e207 : ℝ := (127431301/20000000000000)
theorem h207 : Model (fun x => f207 ((13/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(3277530067383831/20000000000000),(17553393997833/50000000000000),(4607363987/4000000000000),(-1469986031/100000000000000)⟩
def e208 : ℝ := (318578253/50000000000000)
theorem h208 : Model (fun x => f208 ((13/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(168995183195709/1000000000000),(29472397463857/50000000000000),(111747777287/50000000000000),(-91469109/4000000000000)⟩
def e209 : ℝ := (33538653/3125000000000)
theorem h209 : Model (fun x => f209 ((13/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(4325474817987963/25000000000000),(29472397463857/50000000000000),(111747777287/50000000000000),(-91469109/4000000000000)⟩
def e210 : ℝ := (1073236897/100000000000000)
theorem h210 : Model (fun x => f210 ((13/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(178423238047127/1000000000000),(84796101847301/100000000000000),(371394479489/100000000000000),(-2955835201/100000000000000)⟩
def e211 : ℝ := (774673773/50000000000000)
theorem h211 : Model (fun x => f211 ((13/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(4456176189273413/25000000000000),(84796101847301/100000000000000),(371394479489/100000000000000),(-2955835201/100000000000000)⟩
def e212 : ℝ := (1549347547/100000000000000)
theorem h212 : Model (fun x => f212 ((13/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(18381459110389901/100000000000000),(56090190396897/50000000000000),(140393437519/25000000000000),(-846446439/25000000000000)⟩
def e213 : ℝ := (41136629/2000000000000)
theorem h213 : Model (fun x => f213 ((13/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(9192396221861617/50000000000000),(56090190396897/50000000000000),(140393437519/25000000000000),(-846446439/25000000000000)⟩
def e214 : ℝ := (2056831451/100000000000000)
theorem h214 : Model (fun x => f214 ((13/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(574248682768077/100000000000000),(14508435266457/50000000000000),(236034966333/100000000000000),(-121802497/100000000000000)⟩
def e215 : ℝ := (540477903/100000000000000)
theorem h215 : Model (fun x => f215 ((13/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(13293069881707/12500000000000),(143106395559/50000000000000),(112163299/12500000000000),(-383573/3125000000000)⟩
def e216 : ℝ := (2595001/50000000000000)
theorem h216 : Model (fun x => f216 ((13/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(6347609322441/3125000000000),(138771858881/100000000000000),(341692299/100000000000000),(-641109/10000000000000)⟩
def e217 : ℝ := (1252469/50000000000000)
theorem h217 : Model (fun x => f217 ((13/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(10314788892247/2500000000000),(7046956361/1250000000000),(158069099/10000000000000),(-6274129/25000000000000)⟩
def e218 : ℝ := (5099939/50000000000000)
theorem h218 : Model (fun x => f218 ((13/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(167614080336481/20000000000000),(1717682914249/100000000000000),(1080576759/20000000000000),(-73308671/100000000000000)⟩
def e219 : ℝ := (249181/800000000000)
theorem h219 : Model (fun x => f219 ((13/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(851158959132977/50000000000000),(4652023500581/100000000000000),(8110904553/50000000000000),(-189269713/100000000000000)⟩
def e220 : ℝ := (10567723/12500000000000)
theorem h220 : Model (fun x => f220 ((13/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(226290310483913/12500000000000),(306857047073/3125000000000),(45840705161/100000000000000),(-161027233/50000000000000)⟩
def e221 : ℝ := (179711831/100000000000000)
theorem h221 : Model (fun x => f221 ((13/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(3222609322441/390625000000),(138771858881/12500000000000),(341692299/12500000000000),(-641109/1250000000000)⟩
def e222 : ℝ := (1252469/6250000000000)
theorem h222 : Model (fun x => f222 ((13/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(116416568199819/12500000000000),(698193831083/50000000000000),(226927799/6250000000000),(-3972691/6250000000000)⟩
def e223 : ℝ := (12614753/50000000000000)
theorem h223 : Model (fun x => f223 ((13/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(128916568199819/12500000000000),(698193831083/50000000000000),(226927799/6250000000000),(-3972691/6250000000000)⟩
def e224 : ℝ := (12614753/50000000000000)
theorem h224 : Model (fun x => f224 ((13/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(3734088991290571/20000000000000),(31637512711961/25000000000000),(337808678601/50000000000000),(-3475506767/100000000000000)⟩
def e225 : ℝ := (581070627/25000000000000)
theorem h225 : Model (fun x => f225 ((13/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(133901468649/25000000000000),(-3630387537/100000000000000),(5225429/100000000000000),(39131/20000000000000)⟩
def e226 : ℝ := (34903/50000000000000)
theorem h226 : Model (fun x => f226 ((13/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (9271606744229267/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(615141935939/20000000000000),(134568610587/100000000000000),(240799251/100000000000000),(-1645391/25000000000000)⟩
def e227 : ℝ := (3409751/100000000000000)
theorem h227 : Model (fun x => f227 ((13/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(3124514699963/50000000000000),(5556295211/2000000000000),(696105709/100000000000000),(-6298071/50000000000000)⟩
def e228 : ℝ := (143287/3125000000000)
theorem h228 : Model (fun x => f228 ((13/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(8350106878041/100000000000000),(320139841539/100000000000000),(-754512937/100000000000000),(-1451263/50000000000000)⟩
def e229 : ℝ := (11361591/25000000000000)
theorem h229 : Model (fun x => f229 ((13/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(5138527309563/100000000000000),(117954866953/100000000000000),(-455801183/20000000000000),(33275459/100000000000000)⟩
def e230 : ℝ := (7377161/25000000000000)
theorem h230 : Model (fun x => f230 ((13/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-116574039846709/100000000000000),(-302286522293/12500000000000),(13188077503/25000000000000),(-894015563/100000000000000)⟩
def e231 : ℝ := (14855443/20000000000000)
theorem h231 : Model (fun x => f231 ((13/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((13/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-845/64),(-13/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((13/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(273/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((13/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1339/64),(19/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((13/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((13/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3003/64),(19/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((13/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((13/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(375375/32),(475/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((13/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(455/64),(11/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((13/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(839/64),(11/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((13/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((13/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(158571/64),(2079/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((13/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(20180234721/50000000000000),(-52915991/25000000000000),(606851/20000000000000),(-6501/25000000000000)⟩
def e244 : ℝ := (143/50000000000000)
theorem h244 : Model (fun x => f244 ((13/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (61614/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(47344722552471/10000000000000),(-321179019661/25000000000000),(-1111078613/50000000000000),(-49597193/100000000000000)⟩
def e245 : ℝ := (1631613/25000000000000)
theorem h245 : Model (fun x => f245 ((13/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(117/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((13/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(2041/64),(17/32),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((13/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(3385/64),(17/32),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((13/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(841/64),(29/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((13/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2846785/4096),(16965/1024),(7043/51200),(57/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((13/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((13/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(19845/32),(189/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((13/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(161249685059/100000000000000),(-3071422573/100000000000000),(8775493/20000000000000),(-22287/4000000000000)⟩
def e253 : ℝ := (213/3125000000000)
theorem h253 : Model (fun x => f253 ((13/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (48663/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(28017772502483/25000000000000),(107359566339/20000000000000),(895690423/50000000000000),(-11004777/100000000000000)⟩
def e254 : ℝ := (1907121/20000000000000)
theorem h254 : Model (fun x => f254 ((13/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(53017772502483/25000000000000),(107359566339/20000000000000),(895690423/50000000000000),(-11004777/100000000000000)⟩
def e255 : ℝ := (1907121/20000000000000)
theorem h255 : Model (fun x => f255 ((13/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(53017772502483/50000000000000),(268398915847/100000000000000),(895690423/100000000000000),(-5502389/100000000000000)⟩
def e256 : ℝ := (1191951/25000000000000)
theorem h256 : Model (fun x => f256 ((13/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(3017772502483/50000000000000),(268398915847/100000000000000),(895690423/100000000000000),(-5502389/100000000000000)⟩
def e257 : ℝ := (1191951/25000000000000)
theorem h257 : Model (fun x => f257 ((13/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(391321654184993/100000000000000),(495259904241/50000000000000),(165276209/5000000000000),(-5076609/25000000000000)⟩
def e258 : ℝ := (1759547/10000000000000)
theorem h258 : Model (fun x => f258 ((13/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1373517969949639/50000000000000),(495259904241/50000000000000),(165276209/5000000000000),(-5076609/25000000000000)⟩
def e259 : ℝ := (17595471/100000000000000)
theorem h259 : Model (fun x => f259 ((13/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2912834530354489/100000000000000),(8423317757923/100000000000000),(7692128209/25000000000000),(-77470331/50000000000000)⟩
def e260 : ℝ := (74902639/50000000000000)
theorem h260 : Model (fun x => f260 ((13/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8195215482735441/100000000000000),(8423317757923/100000000000000),(7692128209/25000000000000),(-77470331/50000000000000)⟩
def e261 : ℝ := (149805279/100000000000000)
theorem h261 : Model (fun x => f261 ((13/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(217246035036247/2500000000000),(30927580399101/100000000000000),(128637414039/100000000000000),(-228597803/50000000000000)⟩
def e262 : ℝ := (550992013/100000000000000)
theorem h262 : Model (fun x => f262 ((13/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(13958889020497499/100000000000000),(30927580399101/100000000000000),(128637414039/100000000000000),(-228597803/50000000000000)⟩
def e263 : ℝ := (275496007/50000000000000)
theorem h263 : Model (fun x => f263 ((13/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(14801384049522883/100000000000000),(4391233451771/6250000000000),(344439105659/100000000000000),(-630585427/100000000000000)⟩
def e264 : ℝ := (156816537/12500000000000)
theorem h264 : Model (fun x => f264 ((13/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(1071068645952323/6250000000000),(4391233451771/6250000000000),(344439105659/100000000000000),(-630585427/100000000000000)⟩
def e265 : ℝ := (1254532297/100000000000000)
theorem h265 : Model (fun x => f265 ((13/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(9085707808902843/50000000000000),(120496079307823/100000000000000),(353649799547/50000000000000),(-57813963/100000000000000)⟩
def e266 : ℝ := (2156556211/100000000000000)
theorem h266 : Model (fun x => f266 ((13/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(9286898285093319/50000000000000),(120496079307823/100000000000000),(353649799547/50000000000000),(-57813963/100000000000000)⟩
def e267 : ℝ := (539139053/25000000000000)
theorem h267 : Model (fun x => f267 ((13/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(19694826421311083/100000000000000),(88810271514837/50000000000000),(309940718071/25000000000000),(236793801/12500000000000)⟩
def e268 : ℝ := (796088591/25000000000000)
theorem h268 : Model (fun x => f268 ((13/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(3935441474738407/20000000000000),(88810271514837/50000000000000),(309940718071/25000000000000),(236793801/12500000000000)⟩
def e269 : ℝ := (636870873/20000000000000)
theorem h269 : Model (fun x => f269 ((13/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(10432417040225853/50000000000000),(964617288409/400000000000),(245945974021/12500000000000),(2922204293/50000000000000)⟩
def e270 : ℝ := (4338288443/100000000000000)
theorem h270 : Model (fun x => f270 ((13/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(20868167413785039/100000000000000),(964617288409/400000000000),(245945974021/12500000000000),(2922204293/50000000000000)⟩
def e271 : ℝ := (1084572111/25000000000000)
theorem h271 : Model (fun x => f271 ((13/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(251901527194129/20000000000000),(70564912737637/100000000000000),(952923202621/100000000000000),(830677619/12500000000000)⟩
def e272 : ℝ := (260032877/20000000000000)
theorem h272 : Model (fun x => f272 ((13/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(112435368045001/100000000000000),(569196506411/100000000000000),(2619880223/100000000000000),(-686093/10000000000000)⟩
def e273 : ℝ := (10158429/100000000000000)
theorem h273 : Model (fun x => f273 ((13/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(103017772502483/50000000000000),(268398915847/100000000000000),(895690423/100000000000000),(-5502389/100000000000000)⟩
def e274 : ℝ := (1191951/25000000000000)
theorem h274 : Model (fun x => f274 ((13/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(424506458054933/100000000000000),(221198867621/20000000000000),(4411261069/100000000000000),(-4466427/25000000000000)⟩
def e275 : ℝ := (19694037/100000000000000)
theorem h275 : Model (fun x => f275 ((13/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(437317097217379/50000000000000),(1709056096679/50000000000000),(15859506287/100000000000000),(-9605411/25000000000000)⟩
def e276 : ℝ := (12198407/20000000000000)
theorem h276 : Model (fun x => f276 ((13/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1802057329303447/100000000000000),(2347508695489/25000000000000),(24842205499/50000000000000),(-54105573/100000000000000)⟩
def e277 : ℝ := (41961117/25000000000000)
theorem h277 : Model (fun x => f277 ((13/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1013074895292123/50000000000000),(5203741882141/25000000000000),(156522343873/100000000000000),(344337903/100000000000000)⟩
def e278 : ℝ := (374050277/100000000000000)
theorem h278 : Model (fun x => f278 ((13/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(53017772502483/6250000000000),(268398915847/12500000000000),(895690423/12500000000000),(-5502389/12500000000000)⟩
def e279 : ℝ := (1191951/3125000000000)
theorem h279 : Model (fun x => f279 ((13/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(960719728084729/100000000000000),(2716387833187/100000000000000),(9785403607/100000000000000),(-25440021/50000000000000)⟩
def e280 : ℝ := (48300861/100000000000000)
theorem h280 : Model (fun x => f280 ((13/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1060719728084729/100000000000000),(2716387833187/100000000000000),(9785403607/100000000000000),(-25440021/50000000000000)⟩
def e281 : ℝ := (48300861/100000000000000)
theorem h281 : Model (fun x => f281 ((13/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(537294263731863/2500000000000),(275826553363483/100000000000000),(60598639011/2500000000000),(2227534173/25000000000000)⟩
def e282 : ℝ := (4980725433/100000000000000)
theorem h282 : Model (fun x => f282 ((13/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(465294377541/100000000000000),(-47772907/800000000000),(12080933/50000000000000),(170509/100000000000000)⟩
def e283 : ℝ := (113157/100000000000000)
theorem h283 : Model (fun x => f283 ((13/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (2651688269936059/12500000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(586041821487/10000000000000),(63280411259/25000000000000),(32772179/6250000000000),(-3393373/50000000000000)⟩
def e284 : ℝ := (3841613/50000000000000)
theorem h284 : Model (fun x => f284 ((13/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(28017772502483/12500000000000),(107359566339/10000000000000),(895690423/25000000000000),(-11004777/50000000000000)⟩
def e285 : ℝ := (1907121/10000000000000)
theorem h285 : Model (fun x => f285 ((13/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(4715399915911/10000000000000),(-14919622297/12500000000000),(-96195119/100000000000000),(184931/5000000000000)⟩
def e286 : ℝ := (536461/25000000000000)
theorem h286 : Model (fun x => f286 ((13/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (211532480257009/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(105692001681777/100000000000000),(238713956749/100000000000000),(192390237/100000000000000),(-7397241/100000000000000)⟩
def e287 : ℝ := (6955583/50000000000000)
theorem h287 : Model (fun x => f287 ((13/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(5692001681777/100000000000000),(238713956749/100000000000000),(192390237/100000000000000),(-7397241/100000000000000)⟩
def e288 : ℝ := (6955583/50000000000000)
theorem h288 : Model (fun x => f288 ((13/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(390053815730367/100000000000000),(220242043429/25000000000000),(177502897/25000000000000),(-13649671/50000000000000)⟩
def e289 : ℝ := (5133883/10000000000000)
theorem h289 : Model (fun x => f289 ((13/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(686442025361163/25000000000000),(220242043429/25000000000000),(177502897/25000000000000),(-13649671/50000000000000)⟩
def e290 : ℝ := (51338831/100000000000000)
theorem h290 : Model (fun x => f290 ((13/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(2902057267956577/100000000000000),(748564457509/10000000000000),(4068004601/50000000000000),(-14285907/6250000000000)⟩
def e291 : ℝ := (218301897/50000000000000)
theorem h291 : Model (fun x => f291 ((13/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8184438220337529/100000000000000),(748564457509/10000000000000),(4068004601/50000000000000),(-14285907/6250000000000)⟩
def e292 : ℝ := (87320759/20000000000000)
theorem h292 : Model (fun x => f292 ((13/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(432514829074157/5000000000000),(27449123903641/100000000000000),(1688577977/4000000000000),(-406592079/50000000000000)⟩
def e293 : ℝ := (801588263/50000000000000)
theorem h293 : Model (fun x => f293 ((13/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(13919344200530759/100000000000000),(27449123903641/100000000000000),(1688577977/4000000000000),(-406592079/50000000000000)⟩
def e294 : ℝ := (1603176527/100000000000000)
theorem h294 : Model (fun x => f294 ((13/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(14711633506517299/100000000000000),(15559736448117/25000000000000),(27384329131/20000000000000),(-867768417/50000000000000)⟩
def e295 : ℝ := (3642322547/100000000000000)
theorem h295 : Model (fun x => f295 ((13/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(532729618507237/3125000000000),(15559736448117/25000000000000),(27384329131/20000000000000),(-867768417/50000000000000)⟩
def e296 : ℝ := (910580637/25000000000000)
theorem h296 : Model (fun x => f296 ((13/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(900884155763189/5000000000000),(53237993034647/50000000000000),(81521427747/25000000000000),(-2648764287/100000000000000)⟩
def e297 : ℝ := (3123502767/50000000000000)
theorem h297 : Model (fun x => f297 ((13/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(4605016016911183/25000000000000),(53237993034647/50000000000000),(81521427747/25000000000000),(-2648764287/100000000000000)⟩
def e298 : ℝ := (1249401107/20000000000000)
theorem h298 : Model (fun x => f298 ((13/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(19468534424159471/100000000000000),(78253932379311/50000000000000),(63425795939/10000000000000),(-1589423511/50000000000000)⟩
def e299 : ℝ := (2302103951/25000000000000)
theorem h299 : Model (fun x => f299 ((13/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(19450915376540423/100000000000000),(78253932379311/50000000000000),(63425795939/10000000000000),(-1589423511/50000000000000)⟩
def e300 : ℝ := (1841683161/20000000000000)
theorem h300 : Model (fun x => f300 ((13/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(5139515451723531/25000000000000),(42369668954407/20000000000000),(216277542377/20000000000000),(-2983450013/100000000000000)⟩
def e301 : ℝ := (6250134473/50000000000000)
theorem h301 : Model (fun x => f301 ((13/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(20561395140227457/100000000000000),(42369668954407/20000000000000),(216277542377/20000000000000),(-2983450013/100000000000000)⟩
def e302 : ℝ := (12500268947/100000000000000)
theorem h302 : Model (fun x => f302 ((13/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(1170354957178561/100000000000000),(30570665624637/50000000000000),(6068222897/1000000000000),(1298204951/100000000000000)⟩
def e303 : ℝ := (3652131667/100000000000000)
theorem h303 : Model (fun x => f303 ((13/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(111707992195007/100000000000000),(504603118363/100000000000000),(244131429/25000000000000),(-735903/5000000000000)⟩
def e304 : ℝ := (29507431/100000000000000)
theorem h304 : Model (fun x => f304 ((13/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(205692001681777/100000000000000),(238713956749/100000000000000),(192390237/100000000000000),(-7397241/100000000000000)⟩
def e305 : ℝ := (6955583/50000000000000)
theorem h305 : Model (fun x => f305 ((13/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(423091995558561/100000000000000),(982031031861/100000000000000),(136130619/10000000000000),(-14756271/50000000000000)⟩
def e306 : ℝ := (57329763/100000000000000)
theorem h306 : Model (fun x => f306 ((13/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(870266394619779/100000000000000),(3029938929857/100000000000000),(744791347/12500000000000),(-43431557/50000000000000)⟩
def e307 : ℝ := (88597093/50000000000000)
theorem h307 : Model (fun x => f307 ((13/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(358013673411451/20000000000000),(2077447344853/25000000000000),(846520181/4000000000000),(-222993507/100000000000000)⟩
def e308 : ℝ := (486804817/100000000000000)
theorem h308 : Model (fun x => f308 ((13/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1999649431757607/100000000000000),(146523517379/800000000000),(83052701719/100000000000000),(-64925699/20000000000000)⟩
def e309 : ℝ := (107906973/10000000000000)
theorem h309 : Model (fun x => f309 ((13/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(105692001681777/12500000000000),(238713956749/12500000000000),(192390237/12500000000000),(-7397241/12500000000000)⟩
def e310 : ℝ := (6955583/6250000000000)
theorem h310 : Model (fun x => f310 ((13/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(957244005649223/100000000000000),(482862954471/20000000000000),(628911903/25000000000000),(-18473997/25000000000000)⟩
def e311 : ℝ := (140796759/100000000000000)
theorem h311 : Model (fun x => f311 ((13/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1057244005649223/100000000000000),(482862954471/20000000000000),(628911903/25000000000000),(-18473997/25000000000000)⟩
def e312 : ℝ := (140796759/100000000000000)
theorem h312 : Model (fun x => f312 ((13/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(422823475025121/2000000000000),(241916719670721/100000000000000),(85660388079/6250000000000),(-2443870441/100000000000000)⟩
def e313 : ℝ := (3573795141/25000000000000)
theorem h313 : Model (fun x => f313 ((13/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(473010634019/100000000000000),(-676577743/12500000000000),(3127127/10000000000000),(2387/5000000000000)⟩
def e314 : ℝ := (165263/50000000000000)
theorem h314 : Model (fun x => f314 ((13/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (1044893486316253/5000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(5535903403223/100000000000000),(112929054677/50000000000000),(-36515147/50000000000000),(-7025951/100000000000000)⟩
def e315 : ℝ := (2169561/10000000000000)
theorem h315 : Model (fun x => f315 ((13/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(11396321618093/100000000000000),(47897975439/10000000000000),(45132457/10000000000000),(-13812697/100000000000000)⟩
def e316 : ℝ := (7344709/25000000000000)
theorem h316 : Model (fun x => f316 ((13/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(26977784256367/50000000000000),(1060652990891/50000000000000),(-266874403/6250000000000),(-87490009/100000000000000)⟩
def e317 : ℝ := (70158341/50000000000000)
theorem h317 : Model (fun x => f317 ((13/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(16601713388533/50000000000000),(158919423059/20000000000000),(-2970451487/20000000000000),(87328131/50000000000000)⟩
def e318 : ℝ := (94211951/100000000000000)
theorem h318 : Model (fun x => f318 ((13/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-83370613069643/100000000000000),(-1623695063049/100000000000000),(37900052577/100000000000000),(-719359301/100000000000000)⟩
def e319 : ℝ := (84244583/50000000000000)
theorem h319 : Model (fun x => f319 ((13/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((13/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-1859/64),(-143/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((13/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((13/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(1261/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((13/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(8229/64),(49/32),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((13/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((13/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(15141/64),(49/32),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((13/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1892625/32),(6125/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((13/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((13/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(479799095462085533/50000000000000),(503245773547837/10000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (124541/100000000000000)
theorem h329 : Model (fun x => f329 ((13/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10421028399/100000000000000),(-54651401/100000000000000),(783441/100000000000000),(-1343/20000000000000)⟩
def e330 : ℝ := (19/25000000000000)
theorem h330 : Model (fun x => f330 ((13/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (477259991786395539/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(9630419371903/1562500000000),(756968439691/100000000000000),(75038687/1000000000000),(-132497/4000000000000)⟩
def e331 : ℝ := (8452879/100000000000000)
theorem h331 : Model (fun x => f331 ((13/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((13/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(85/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((13/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((13/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((13/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(575806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((13/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((13/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((13/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2554561459137839/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (207/20000000000000)
theorem h339 : Model (fun x => f339 ((13/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3674193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((13/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((13/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((13/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1035219270430951/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (517/50000000000000)
theorem h343 : Model (fun x => f343 ((13/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4829894634707/100000000000000),(-657272793/10000000000000),(178889/2000000000000),(-3043/25000000000000)⟩
def e344 : ℝ := (21/100000000000000)
theorem h344 : Model (fun x => f344 ((13/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2067620999226387/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(123382626855191/100000000000000),(112935623991/12500000000000),(-245900233/20000000000000),(1673157/100000000000000)⟩
def e345 : ℝ := (1647/50000000000000)
theorem h345 : Model (fun x => f345 ((13/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(223382626855191/100000000000000),(112935623991/12500000000000),(-245900233/20000000000000),(1673157/100000000000000)⟩
def e346 : ℝ := (1647/50000000000000)
theorem h346 : Model (fun x => f346 ((13/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(22338262685519/20000000000000),(112935623991/25000000000000),(-614750583/100000000000000),(418289/50000000000000)⟩
def e347 : ℝ := (1649/100000000000000)
theorem h347 : Model (fun x => f347 ((13/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(2338262685519/20000000000000),(112935623991/25000000000000),(-614750583/100000000000000),(418289/50000000000000)⟩
def e348 : ℝ := (1649/100000000000000)
theorem h348 : Model (fun x => f348 ((13/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(201266666449/48828125000),(1667144925581/100000000000000),(-226872239/10000000000000),(3087371/100000000000000)⟩
def e349 : ℝ := (761/12500000000000)
theorem h349 : Model (fun x => f349 ((13/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2767908418601837/100000000000000),(1667144925581/100000000000000),(-226872239/10000000000000),(3087371/100000000000000)⟩
def e350 : ℝ := (6089/100000000000000)
theorem h350 : Model (fun x => f350 ((13/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(618302653441873/20000000000000),(1795734330039/12500000000000),(-6009248439/50000000000000),(6106471/100000000000000)⟩
def e351 : ℝ := (94381/100000000000000)
theorem h351 : Model (fun x => f351 ((13/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8373894219590317/100000000000000),(1795734330039/12500000000000),(-6009248439/50000000000000),(6106471/100000000000000)⟩
def e352 : ℝ := (47191/50000000000000)
theorem h352 : Model (fun x => f352 ((13/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(9352912438897881/100000000000000),(6734234103511/12500000000000),(-1083977/20000000000000),(-32866201/50000000000000)⟩
def e353 : ℝ := (465957/100000000000000)
theorem h353 : Model (fun x => f353 ((13/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(29243920115891/200000000000),(6734234103511/12500000000000),(-1083977/20000000000000),(-32866201/50000000000000)⟩
def e354 : ℝ := (232979/50000000000000)
theorem h354 : Model (fun x => f354 ((13/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(16331459237577659/100000000000000),(201961669569/160000000000),(153476539543/100000000000000),(-141153857/50000000000000)⟩
def e355 : ℝ := (114843/12500000000000)
theorem h355 : Model (fun x => f355 ((13/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(2333396690411493/12500000000000),(201961669569/160000000000),(153476539543/100000000000000),(-141153857/50000000000000)⟩
def e356 : ℝ := (183749/20000000000000)
theorem h356 : Model (fun x => f356 ((13/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(20849611287973033/100000000000000),(225311081451247/100000000000000),(62688008413/10000000000000),(-48360863/20000000000000)⟩
def e357 : ℝ := (2506067/100000000000000)
theorem h357 : Model (fun x => f357 ((13/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(4250398448070797/20000000000000),(225311081451247/100000000000000),(62688008413/10000000000000),(-48360863/20000000000000)⟩
def e358 : ℝ := (626517/25000000000000)
theorem h358 : Model (fun x => f358 ((13/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(23736629262781937/100000000000000),(173828593179733/50000000000000),(317469951283/20000000000000),(338624407/25000000000000)⟩
def e359 : ℝ := (3116241/50000000000000)
theorem h359 : Model (fun x => f359 ((13/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(23719010215162889/100000000000000),(173828593179733/50000000000000),(317469951283/20000000000000),(338624407/25000000000000)⟩
def e360 : ℝ := (6232483/100000000000000)
theorem h360 : Model (fun x => f360 ((13/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(26492074041340857/100000000000000),(247725863217121/50000000000000),(799408572277/25000000000000),(6744793041/100000000000000)⟩
def e361 : ℝ := (2030541/25000000000000)
theorem h361 : Model (fun x => f361 ((13/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(2649540737467419/10000000000000),(247725863217121/50000000000000),(799408572277/25000000000000),(6744793041/100000000000000)⟩
def e362 : ℝ := (1624433/20000000000000)
theorem h362 : Model (fun x => f362 ((13/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(3097661120091279/100000000000000),(4440395720251/2500000000000),(1224565385497/50000000000000),(1551186277/12500000000000)⟩
def e363 : ℝ := (8201347/50000000000000)
theorem h363 : Model (fun x => f363 ((13/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(31187373737953/25000000000000),(201822850821/20000000000000),(26698673/4000000000000),(-368541/10000000000000)⟩
def e364 : ℝ := (15049/100000000000000)
theorem h364 : Model (fun x => f364 ((13/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(42338262685519/20000000000000),(112935623991/25000000000000),(-614750583/100000000000000),(418289/50000000000000)⟩
def e365 : ℝ := (1649/100000000000000)
theorem h365 : Model (fun x => f365 ((13/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(224066060903501/50000000000000),(1912599246033/100000000000000),(-562034341/100000000000000),(-1006127/50000000000000)⟩
def e366 : ℝ := (18347/100000000000000)
theorem h366 : Model (fun x => f366 ((13/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(14822762102253/1562500000000),(7591512121/125000000000),(2347675431/50000000000000),(-462733/3125000000000)⟩
def e367 : ℝ := (56719/100000000000000)
theorem h367 : Model (fun x => f367 ((13/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1004111992976229/50000000000000),(685677726633/4000000000000),(31543045927/100000000000000),(-19767021/50000000000000)⟩
def e368 : ℝ := (5661/3125000000000)
theorem h368 : Model (fun x => f368 ((13/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2505249279976839/100000000000000),(8329952404179/20000000000000),(225735811281/100000000000000),(309392351/100000000000000)⟩
def e369 : ℝ := (677101/50000000000000)
theorem h369 : Model (fun x => f369 ((13/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(22338262685519/2500000000000),(112935623991/3125000000000),(-614750583/12500000000000),(418289/6250000000000)⟩
def e370 : ℝ := (1649/12500000000000)
theorem h370 : Model (fun x => f370 ((13/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(254570000593143/25000000000000),(4623054221817/100000000000000),(-4250537839/100000000000000),(1503607/50000000000000)⟩
def e371 : ℝ := (28241/100000000000000)
theorem h371 : Model (fun x => f371 ((13/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(279570000593143/25000000000000),(4623054221817/100000000000000),(-4250537839/100000000000000),(1503607/50000000000000)⟩
def e372 : ℝ := (28241/100000000000000)
theorem h372 : Model (fun x => f372 ((13/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(14007850853781919/50000000000000),(145394998080111/25000000000000),(34746903589/800000000000),(381273783/3125000000000)⟩
def e373 : ℝ := (5473257/25000000000000)
theorem h373 : Model (fun x => f373 ((13/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(89235673127/25000000000000),(-7409799353/100000000000000),(6155163/6250000000000),(-1051091/100000000000000)⟩
def e374 : ℝ := (2601/25000000000000)
theorem h374 : Model (fun x => f374 ((13/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (5485953225928137/20000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(11056875006827/100000000000000),(10111406201/2500000000000),(-1368325759/100000000000000),(1036111/20000000000000)⟩
def e375 : ℝ := (98613/12500000000000)
theorem h375 : Model (fun x => f375 ((13/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(123382626855191/50000000000000),(112935623991/6250000000000),(-245900233/10000000000000),(1673157/50000000000000)⟩
def e376 : ℝ := (1647/25000000000000)
theorem h376 : Model (fun x => f376 ((13/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(22383119360671/50000000000000),(-181059849637/100000000000000),(978701891/100000000000000),(-5290281/100000000000000)⟩
def e377 : ℝ := (28959/100000000000000)
theorem h377 : Model (fun x => f377 ((13/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (222477910685647/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(55233761278657/50000000000000),(362119699271/100000000000000),(-391480757/20000000000000),(5290279/50000000000000)⟩
def e378 : ℝ := (200831/100000000000000)
theorem h378 : Model (fun x => f378 ((13/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(5233761278657/50000000000000),(362119699271/100000000000000),(-391480757/20000000000000),(5290279/50000000000000)⟩
def e379 : ℝ := (200831/100000000000000)
theorem h379 : Model (fun x => f379 ((13/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(203838880909329/50000000000000),(668197064131/50000000000000),(-56435563/781250000000),(39047297/100000000000000)⟩
def e380 : ℝ := (185291/25000000000000)
theorem h380 : Model (fun x => f380 ((13/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2763392047532943/100000000000000),(668197064131/50000000000000),(-56435563/781250000000),(39047297/100000000000000)⟩
def e381 : ℝ := (148233/20000000000000)
theorem h381 : Model (fun x => f381 ((13/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(122106029338219/4000000000000),(11483068457297/100000000000000),(-14307823519/25000000000000),(283199621/100000000000000)⟩
def e382 : ℝ := (339981/5000000000000)
theorem h382 : Model (fun x => f382 ((13/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8335031685836427/100000000000000),(11483068457297/100000000000000),(-14307823519/25000000000000),(283199621/100000000000000)⟩
def e383 : ℝ := (6799621/100000000000000)
theorem h383 : Model (fun x => f383 ((13/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(287734468990957/3125000000000),(42867852913229/100000000000000),(-184789765429/100000000000000),(38136033/5000000000000)⟩
def e384 : ℝ := (864719/3125000000000)
theorem h384 : Model (fun x => f384 ((13/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(14476550626758243/100000000000000),(42867852913229/100000000000000),(-184789765429/100000000000000),(38136033/5000000000000)⟩
def e385 : ℝ := (27671009/100000000000000)
theorem h385 : Model (fun x => f385 ((13/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(15991886829135143/100000000000000),(24944374170297/25000000000000),(-166132142831/50000000000000),(433000667/50000000000000)⟩
def e386 : ℝ := (70777357/100000000000000)
theorem h386 : Model (fun x => f386 ((13/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(4581900278712357/25000000000000),(24944374170297/25000000000000),(-166132142831/50000000000000),(433000667/50000000000000)⟩
def e387 : ℝ := (35388679/50000000000000)
theorem h387 : Model (fun x => f387 ((13/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(2530755861970103/12500000000000),(35317916538819/20000000000000),(-182237655857/50000000000000),(-65107561/25000000000000)⟩
def e388 : ℝ := (5428047/4000000000000)
theorem h388 : Model (fun x => f388 ((13/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(1290526740508861/6250000000000),(35317916538819/20000000000000),(-182237655857/50000000000000),(-65107561/25000000000000)⟩
def e389 : ℝ := (16962647/12500000000000)
theorem h389 : Model (fun x => f389 ((13/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(11404903345438361/50000000000000),(134923080962173/50000000000000),(-167334289631/100000000000000),(-2879380033/100000000000000)⟩
def e390 : ℝ := (108566233/50000000000000)
theorem h390 : Model (fun x => f390 ((13/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(11396093821628837/50000000000000),(134923080962173/50000000000000),(-167334289631/100000000000000),(-2879380033/100000000000000)⟩
def e391 : ℝ := (217132467/100000000000000)
theorem h391 : Model (fun x => f391 ((13/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(5035593005224201/20000000000000),(380627371144869/100000000000000),(346180922297/100000000000000),(-832146071/12500000000000)⟩
def e392 : ℝ := (154203131/50000000000000)
theorem h392 : Model (fun x => f392 ((13/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(12590649179727169/50000000000000),(380627371144869/100000000000000),(346180922297/100000000000000),(-832146071/12500000000000)⟩
def e393 : ℝ := (308406263/100000000000000)
theorem h393 : Model (fun x => f393 ((13/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(2635858086000423/100000000000000),(131028697825689/100000000000000),(921663570663/100000000000000),(-4229343999/100000000000000)⟩
def e394 : ℝ := (94299409/100000000000000)
theorem h394 : Model (fun x => f394 ((13/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(61015367699753/50000000000000),(800049320953/100000000000000),(-301328417/10000000000000),(9199871/100000000000000)⟩
def e395 : ℝ := (560529/100000000000000)
theorem h395 : Model (fun x => f395 ((13/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(105233761278657/50000000000000),(362119699271/100000000000000),(-391480757/20000000000000),(5290279/50000000000000)⟩
def e396 : ℝ := (200831/100000000000000)
theorem h396 : Model (fun x => f396 ((13/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(221482890257067/50000000000000),(304857743899/20000000000000),(-346404587/5000000000000),(30360987/100000000000000)⟩
def e397 : ℝ := (962191/100000000000000)
theorem h397 : Model (fun x => f397 ((13/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(466149552012383/50000000000000),(1203049764203/25000000000000),(-17732262273/100000000000000),(27921899/50000000000000)⟩
def e398 : ℝ := (208091/6250000000000)
theorem h398 : Model (fun x => f398 ((13/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(3065916917289/156250000000),(13504154847199/100000000000000),(-38143590297/100000000000000),(14442331/25000000000000)⟩
def e399 : ℝ := (62269/625000000000)
theorem h399 : Model (fun x => f399 ((13/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2394471014979603/100000000000000),(32177681855287/100000000000000),(1183365181/50000000000000),(-115267777/25000000000000)⟩
def e400 : ℝ := (26171697/100000000000000)
theorem h400 : Model (fun x => f400 ((13/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(55233761278657/6250000000000),(362119699271/12500000000000),(-391480757/2500000000000),(5290279/6250000000000)⟩
def e401 : ℝ := (200831/12500000000000)
theorem h401 : Model (fun x => f401 ((13/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(502885457929009/50000000000000),(3697006915121/100000000000000),(-373450289/2000000000000),(18768867/20000000000000)⟩
def e402 : ℝ := (2167177/100000000000000)
theorem h402 : Model (fun x => f402 ((13/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(552885457929009/50000000000000),(3697006915121/100000000000000),(-373450289/2000000000000),(18768867/20000000000000)⟩
def e403 : ℝ := (2167177/100000000000000)
theorem h403 : Model (fun x => f403 ((13/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(5295472814458947/20000000000000),(8886704127149/2000000000000),(384336896521/50000000000000),(-4386099461/50000000000000)⟩
def e404 : ℝ := (1423037/400000000000)
theorem h404 : Model (fun x => f404 ((13/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(47210137557/12500000000000),(-6338131291/100000000000000),(95400029/100000000000000),(-1291841/100000000000000)⟩
def e405 : ℝ := (22419/100000000000000)
theorem h405 : Model (fun x => f405 ((13/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (26032251064186071/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(77774514263/781250000000),(163903240863/50000000000000),(-2309212403/100000000000000),(6469/39062500000)⟩
def e406 : ℝ := (1544087/100000000000000)
theorem h406 : Model (fun x => f406 ((13/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(21012012832491/100000000000000),(366131364883/50000000000000),(-1838769081/50000000000000),(4348239/20000000000000)⟩
def e407 : ℝ := (2332991/100000000000000)
theorem h407 : Model (fun x => f407 ((13/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(25901375414361/20000000000000),(1168083124911/25000000000000),(-1554667863/10000000000000),(160415391/100000000000000)⟩
def e408 : ℝ := (16372877/100000000000000)
theorem h408 : Model (fun x => f408 ((13/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(39848269868247/50000000000000),(164918092691/10000000000000),(-34939201111/100000000000000),(318121667/50000000000000)⟩
def e409 : ℝ := (7310787/25000000000000)
theorem h409 : Model (fun x => f409 ((13/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3674073333149/100000000000000),(25485863861/100000000000000),(1480425733/50000000000000),(-83115967/100000000000000)⟩
def e410 : ℝ := (98866157/50000000000000)
theorem h410 : Model (fun x => f410 ((13/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(915193176269531/50000000000000),(32517852783203/25000000000000),(15041/409600),(1053/2048000)⟩
def e411 : ℝ := (89355469/25000000000000)
theorem h411 : Model (fun x => f411 ((13/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1369/64),(37/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((13/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(50653/512),(4107/2560),(111/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((13/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(90541562417149519/50000000000000),(7902330603599523/50000000000000),(587834811210631/100000000000000),(1213440284729/10000000000000)⟩
def e414 : ℝ := (9550248697/6250000000000)
theorem h414 : Model (fun x => f414 ((13/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(2208930293/4000000000000),(-2409901181/50000000000000),(60349619/25000000000000),(-285103/3125000000000)⟩
def e415 : ℝ := (110111/25000000000000)
theorem h415 : Model (fun x => f415 ((13/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (164678341609062919/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2617847906967/50000000000000),(30700114471/50000000000000),(-560948091/20000000000000),(66586247/100000000000000)⟩
def e416 : ℝ := (84628569/100000000000000)
theorem h416 : Model (fun x => f416 ((13/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(312324496157/20000000000000),(86886092803/100000000000000),(156111011/100000000000000),(-413243/2500000000000)⟩
def e417 : ℝ := (282360883/100000000000000)
theorem h417 : Model (fun x => f417 ((13/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((13/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((4684176470717/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (8/5) (33/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (8/5) (33/20) ≤ (937174127203/1200000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(13/8)-(1/40)) (by norm_num : ((13/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel12

