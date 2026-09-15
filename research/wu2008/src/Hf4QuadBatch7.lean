import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel22
open Hf4Quad.Dag

def p0 : Cubic := ⟨(17/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((17/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((17/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((17/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((17/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(46547619047619/12500000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((17/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-46547619047619/12500000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((17/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-280952380952381/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((17/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((17/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(289/64),(17/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((17/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(546653439153439/100000000000000),(12862433862433/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((17/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-546653439153439/100000000000000),(-12862433862433/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((17/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-41380291005291/5000000000000),(-3448677248677/20000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((17/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((17/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(4913/512),(867/2560),(51/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((17/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(9348702618634259/100000000000000),(82488552517361/25000000000000),(3881814236111/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((17/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-9348702618634259/100000000000000),(-82488552517361/25000000000000),(-3881814236111/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((17/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-10176308438740079/100000000000000),(-347197596312829/100000000000000),(-989368902943/25000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((17/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((17/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(83521/4096),(4913/5120),(867/51200),(17/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((17/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(113929935515873/2000000000000),(8377201140873/3125000000000),(295665922619/6250000000000),(37103174603/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((17/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-4479811662946429/100000000000000),(-79127159804893/100000000000000),(193294787533/25000000000000),(10940186839/50000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((17/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((17/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1083264923095703/25000000000000),(63721466064453/25000000000000),(4913/81920),(289/409600)⟩
def e22 : ℝ := (208007813/50000000000000)
theorem h22 : Model (fun x => f22 ((17/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(28229081477412467/100000000000000),(1660534204553671/100000000000000),(39071393048321/100000000000000),(459663447627/100000000000000)⟩
def e23 : ℝ := (1355132383/50000000000000)
theorem h23 : Model (fun x => f23 ((17/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(11874634907233019/50000000000000),(790703522374389/50000000000000),(39844572198453/100000000000000),(96308764261/20000000000000)⟩
def e24 : ℝ := (2819391759/100000000000000)
theorem h24 : Model (fun x => f24 ((17/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((17/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(368310073852539/4000000000000),(32497947692871/5000000000000),(3823287963867/20000000000000),(9370803833/3125000000000)⟩
def e26 : ℝ := (1329174807/50000000000000)
theorem h26 : Model (fun x => f26 ((17/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(2584503891253597/12500000000000),(182435568794371/12500000000000),(10731504046727/25000000000000),(673349273519/100000000000000)⟩
def e27 : ℝ := (2984665547/50000000000000)
theorem h27 : Model (fun x => f27 ((17/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(22212650472247407/50000000000000),(1520445797551873/50000000000000),(82770588385361/100000000000000),(144361636853/12500000000000)⟩
def e28 : ℝ := (8788722853/100000000000000)
theorem h28 : Model (fun x => f28 ((17/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((17/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(9783236336708067/50000000000000),(805678286552427/50000000000000),(28435704231261/50000000000000),(1115125656127/100000000000000)⟩
def e30 : ℝ := (6606047369/50000000000000)
theorem h30 : Model (fun x => f30 ((17/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(4643155023294781/100000000000000),(95594368126657/25000000000000),(13495675500233/100000000000000),(264621088239/100000000000000)⟩
def e31 : ℝ := (627050211/20000000000000)
theorem h31 : Model (fun x => f31 ((17/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(9813691193557919/20000000000000),(1711634533805187/50000000000000),(48133131942797/50000000000000),(1419514183063/100000000000000)⟩
def e32 : ℝ := (2980993477/25000000000000)
theorem h32 : Model (fun x => f32 ((17/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((17/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(619905/64),(7293/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((17/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((17/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(37553/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((17/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1220753/64),(54137/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((17/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((17/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1366673/64),(54137/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((17/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1366673/64),(-54137/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((17/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((17/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(25/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((17/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(625/64),(5/32),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((17/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((17/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(65625/32),(525/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((17/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(48761904761/100000000000000),(-780190477/100000000000000),(1872457/20000000000000),(-19973/20000000000000)⟩
def e46 : ℝ := (41/4000000000000)
theorem h46 : Model (fun x => f46 ((17/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (161427/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1041274666647347/100000000000000),(40374861541/25000000000000),(-656912617/50000000000000),(213979/2000000000000)⟩
def e47 : ℝ := (43608829/100000000000000)
theorem h47 : Model (fun x => f47 ((17/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((17/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(33/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((17/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((17/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((17/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(68749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((17/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(118749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((17/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((17/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(118749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((17/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((17/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2493749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((17/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((17/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(18749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((17/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(467578124999971/100000000000000),(601562499999/5000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (59/50000000000000)
theorem h60 : Model (fun x => f60 ((17/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(141015624999997/100000000000000),(989583333331/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((17/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((17/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(118749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((17/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1328515624999987/100000000000000),(5156249999991/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((17/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1428515624999987/100000000000000),(5156249999991/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((17/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1669856643676639/25000000000000),(97988891601397/50000000000000),(57464599609/5000000000000),(52218967/2500000000000)⟩
def e66 : ℝ := (6349/1000000000000)
theorem h66 : Model (fun x => f66 ((17/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(218749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((17/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(95703124999999/20000000000000),(1822916666663/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((17/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(261688232421871/25000000000000),(747680664061/12500000000000),(5696614583/50000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (13/20000000000000)
theorem h69 : Model (fun x => f69 ((17/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(69917093357065237/100000000000000),(490185886993139/20000000000000),(1225677695117/5000000000000),(113419788717/100000000000000)⟩
def e70 : ℝ := (277065681/100000000000000)
theorem h70 : Model (fun x => f70 ((17/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((17/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2961328124999937/12500000000000),(20781249999951/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((17/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1110498046874917/25000000000000),(32470703124941/25000000000000),(747395833327/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1343/100000000000000)
theorem h73 : Model (fun x => f73 ((17/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(11624170839785483/25000000000000),(1625247478482063/100000000000000),(4024585882791/25000000000000),(72545199901/100000000000000)⟩
def e74 : ℝ := (167448879/100000000000000)
theorem h74 : Model (fun x => f74 ((17/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(116413776716207169/100000000000000),(2038088456723879/50000000000000),(1269121794797/3125000000000),(92982494309/50000000000000)⟩
def e75 : ℝ := (347277/78125000000)
theorem h75 : Model (fun x => f75 ((17/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((17/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(987109374999979/12500000000000),(6927083333317/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((17/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(3515624999999/100000000000000),(156249999999/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((17/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(659179687499/100000000000000),(43945312499/100000000000000),(976562499/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((17/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(10410919189437/20000000000000),(23972511291/625000000000),(51055908163/50000000000000),(577573411/50000000000000)⟩
def e80 : ℝ := (2482761/50000000000000)
theorem h80 : Model (fun x => f80 ((17/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(56934714317233/50000000000000),(8607273101629/100000000000000),(239351272407/100000000000000),(1476174787/50000000000000)⟩
def e81 : ℝ := (3139177/20000000000000)
theorem h81 : Model (fun x => f81 ((17/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(23305529228968327/20000000000000),(4084784186549387/100000000000000),(40851248705911/100000000000000),(11807333637/6250000000000)⟩
def e82 : ℝ := (92042089/20000000000000)
theorem h82 : Model (fun x => f82 ((17/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(61798095703/50000000000000),(2746582031/25000000000000),(366210937/100000000000000),(5425347/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((17/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(362098217/1562500000000),(1287460327/50000000000000),(114440917/100000000000000),(2543131/100000000000000)⟩
def e84 : ℝ := (14193/50000000000000)
theorem h84 : Model (fun x => f84 ((17/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(4345178603/100000000000000),(579357147/100000000000000),(32186507/100000000000000),(476837/50000000000000)⟩
def e85 : ℝ := (401/2500000000000)
theorem h85 : Model (fun x => f85 ((17/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(203680247/25000000000000),(8111/6400000000),(4224479/50000000000000),(78231/25000000000000)⟩
def e86 : ℝ := (141/2000000000000)
theorem h86 : Model (fun x => f86 ((17/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(611040741/25000000000000),(24333/6400000000),(12673437/50000000000000),(234693/25000000000000)⟩
def e87 : ℝ := (423/2000000000000)
theorem h87 : Model (fun x => f87 ((17/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-611040741/25000000000000),(-24333/6400000000),(-12673437/50000000000000),(-234693/25000000000000)⟩
def e88 : ℝ := (423/2000000000000)
theorem h88 : Model (fun x => f88 ((17/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(116527643700678671/100000000000000),(2042391903173131/50000000000000),(40851223359037/100000000000000),(9445819971/5000000000000)⟩
def e89 : ℝ := (92046319/20000000000000)
theorem h89 : Model (fun x => f89 ((17/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2961328124999937/10000000000000),(20781249999951/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((17/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(14311075210571/625000000000),(1090367635089/6250000000000),(24922688801/50000000000000),(15823929/25000000000000)⟩
def e91 : ℝ := (30329/100000000000000)
theorem h91 : Model (fun x => f91 ((17/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(21189894760026649/3125000000000),(1984946131701919/20000000000000),(2968185146583/5000000000000),(46483410609/25000000000000)⟩
def e92 : ℝ := (32259781/10000000000000)
theorem h92 : Model (fun x => f92 ((17/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(737379783/5000000000000),(-215854533/100000000000000),(233533/12500000000000),(-3123/25000000000000)⟩
def e93 : ℝ := (89/100000000000000)
theorem h93 : Model (fun x => f93 ((17/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (668092351703171267/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(17185025725101/100000000000000),(350877198219/100000000000000),(-615573749/100000000000000),(1439321/100000000000000)⟩
def e94 : ℝ := (332703/100000000000000)
theorem h94 : Model (fun x => f94 ((17/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(68749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((17/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(8421052631579/20000000000000),(-147737765467/100000000000000),(129594531/25000000000000),(-1818871/100000000000000)⟩
def e96 : ℝ := (801/12500000000000)
theorem h96 : Model (fun x => f96 ((17/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (236666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(115789473684209/100000000000000),(29547553093/10000000000000),(-1036756251/100000000000000),(181887/5000000000000)⟩
def e97 : ℝ := (48051/100000000000000)
theorem h97 : Model (fun x => f97 ((17/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2431578947368389/100000000000000),(620498614953/10000000000000),(-21771881271/100000000000000),(3819627/5000000000000)⟩
def e98 : ℝ := (1009071/100000000000000)
theorem h98 : Model (fun x => f98 ((17/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(15789473684209/100000000000000),(29547553093/10000000000000),(-1036756251/100000000000000),(181887/5000000000000)⟩
def e99 : ℝ := (48051/100000000000000)
theorem h99 : Model (fun x => f99 ((17/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(383933518005497/100000000000000),(8164455459907/100000000000000),(-1031299643/10000000000000),(-3518083/12500000000000)⟩
def e100 : ℝ := (2012463/100000000000000)
theorem h100 : Model (fun x => f100 ((17/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(134072022160661/100000000000000),(342129562129/50000000000000),(-38196283/2500000000000),(2297517/100000000000000)⟩
def e101 : ℝ := (71943/50000000000000)
theorem h101 : Model (fun x => f101 ((17/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(115789473684209/10000000000000),(29547553093/1000000000000),(-1036756251/10000000000000),(181887/500000000000)⟩
def e102 : ℝ := (48051/10000000000000)
theorem h102 : Model (fun x => f102 ((17/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1291966759002751/100000000000000),(1819507216779/50000000000000),(-1189541383/10000000000000),(38674917/100000000000000)⟩
def e103 : ℝ := (156099/25000000000000)
theorem h103 : Model (fun x => f103 ((17/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1391966759002751/100000000000000),(1819507216779/50000000000000),(-1189541383/10000000000000),(38674917/100000000000000)⟩
def e104 : ℝ := (156099/25000000000000)
theorem h104 : Model (fun x => f104 ((17/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(133605673682659/2500000000000),(127617902190977/100000000000000),(21576349929/20000000000000),(-1589765591/100000000000000)⟩
def e105 : ℝ := (16947717/50000000000000)
theorem h105 : Model (fun x => f105 ((17/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(215789473684209/100000000000000),(29547553093/10000000000000),(-1036756251/100000000000000),(181887/5000000000000)⟩
def e106 : ℝ := (48051/100000000000000)
theorem h106 : Model (fun x => f106 ((17/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(465650969529079/100000000000000),(637605093059/50000000000000),(-1800681911/50000000000000),(9572997/100000000000000)⟩
def e107 : ℝ := (59997/25000000000000)
theorem h107 : Model (fun x => f107 ((17/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(200965155270443/20000000000000),(64494594117/1562500000000),(-551943469/6250000000000),(13734721/100000000000000)⟩
def e108 : ℝ := (85519/10000000000000)
theorem h108 : Model (fun x => f108 ((17/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(53700169913295411/100000000000000),(300585755013943/20000000000000),(2939847658611/50000000000000),(-2757179153/12500000000000)⟩
def e109 : ℝ := (223281191/50000000000000)
theorem h109 : Model (fun x => f109 ((17/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2815512465373881/12500000000000),(7184720804709/6250000000000),(-802121943/312500000000),(48247857/12500000000000)⟩
def e110 : ℝ := (1510803/6250000000000)
theorem h110 : Model (fun x => f110 ((17/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(3556436798366663/100000000000000),(16940815371121/20000000000000),(65617192643/100000000000000),(-1069919529/100000000000000)⟩
def e111 : ℝ := (22763617/100000000000000)
theorem h111 : Model (fun x => f111 ((17/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(111674980217699/312500000000),(997925804466899/100000000000000),(3841557371581/100000000000000),(-15034207773/100000000000000)⟩
def e112 : ℝ := (299242623/100000000000000)
theorem h112 : Model (fun x => f112 ((17/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(89436163582959091/100000000000000),(1250427289768307/50000000000000),(9721252688803/100000000000000),(-37091640997/100000000000000)⟩
def e113 : ℝ := (149161001/20000000000000)
theorem h113 : Model (fun x => f113 ((17/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(938504155124627/12500000000000),(2394906934903/6250000000000),(-267373981/312500000000),(16082619/12500000000000)⟩
def e114 : ℝ := (503601/6250000000000)
theorem h114 : Model (fun x => f114 ((17/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(2493074792243/100000000000000),(46654031199/50000000000000),(272830591/50000000000000),(-4977963/100000000000000)⟩
def e115 : ℝ := (5973/12500000000000)
theorem h115 : Model (fun x => f115 ((17/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(49205423531/12500000000000),(1381204871/6250000000000),(84003103/25000000000000),(-10077/20000000000000)⟩
def e116 : ℝ := (3247/12500000000000)
theorem h116 : Model (fun x => f116 ((17/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(14777438220323/50000000000000),(905029709159/50000000000000),(1334369513/4000000000000),(4262817/4000000000000)⟩
def e117 : ℝ := (2272631/100000000000000)
theorem h117 : Model (fun x => f117 ((17/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(7972039039911/12500000000000),(1996622560119/50000000000000),(123244151/160000000000),(310845369/100000000000000)⟩
def e118 : ℝ := (124023/2500000000000)
theorem h118 : Model (fun x => f118 ((17/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(89499939895278379/100000000000000),(626211956164213/25000000000000),(4899140141589/50000000000000),(-9195198907/25000000000000)⟩
def e119 : ℝ := (30030637/4000000000000)
theorem h119 : Model (fun x => f119 ((17/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(62154219197/100000000000000),(930495913/20000000000000),(114271427/100000000000000),(770083/100000000000000)⟩
def e120 : ℝ := (3611/50000000000000)
theorem h120 : Model (fun x => f120 ((17/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(9813824083/100000000000000),(183650509/20000000000000),(31145407/100000000000000),(206631/50000000000000)⟩
def e121 : ℝ := (2461/100000000000000)
theorem h121 : Model (fun x => f121 ((17/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(154955117/10000000000000),(43496173/25000000000000),(7529161/100000000000000),(29623/20000000000000)⟩
def e122 : ℝ := (67/5000000000000)
theorem h122 : Model (fun x => f122 ((17/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(122332987/50000000000000),(32049811/100000000000000),(105427/6250000000000),(8777/20000000000000)⟩
def e123 : ℝ := (293/50000000000000)
theorem h123 : Model (fun x => f123 ((17/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(366998961/50000000000000),(96149433/100000000000000),(316281/6250000000000),(26331/20000000000000)⟩
def e124 : ℝ := (879/50000000000000)
theorem h124 : Model (fun x => f124 ((17/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-366998961/50000000000000),(-96149433/100000000000000),(-316281/6250000000000),(-26331/20000000000000)⟩
def e125 : ℝ := (879/50000000000000)
theorem h125 : Model (fun x => f125 ((17/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(89499939161280457/100000000000000),(2504847728507419/100000000000000),(4899137611341/50000000000000),(-36780927283/100000000000000)⟩
def e126 : ℝ := (750767683/100000000000000)
theorem h126 : Model (fun x => f126 ((17/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2815512465373881/10000000000000),(7184720804709/5000000000000),(-802121943/250000000000),(48247857/10000000000000)⟩
def e127 : ℝ := (1510803/5000000000000)
theorem h127 : Model (fun x => f127 ((17/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2168308254233711/100000000000000),(2969014297597/25000000000000),(-4319490229/25000000000000),(-2696407/100000000000000)⟩
def e128 : ℝ := (1307761/50000000000000)
theorem h128 : Model (fun x => f128 ((17/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(15262247296420229/2500000000000),(6459456590946091/100000000000000),(5243609081579/100000000000000),(-2661460171/5000000000000)⟩
def e129 : ℝ := (1507876961/100000000000000)
theorem h129 : Model (fun x => f129 ((17/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(1638028759/10000000000000),(-173316149/100000000000000),(846563/50000000000000),(-7499/50000000000000)⟩
def e130 : ℝ := (7/4000000000000)
theorem h130 : Model (fun x => f130 ((17/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (604025136919701109/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(3665086856873/25000000000000),(255183413709/100000000000000),(-610486611/50000000000000),(1495053/25000000000000)⟩
def e131 : ℝ := (433451/100000000000000)
theorem h131 : Model (fun x => f131 ((17/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(31845373152593/100000000000000),(75757576491/12500000000000),(-1836546971/100000000000000),(7419533/100000000000000)⟩
def e132 : ℝ := (383077/50000000000000)
theorem h132 : Model (fun x => f132 ((17/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-331597803137267/100000000000000),(-12225245147/195312500000),(19683890333/100000000000000),(-21194797/25000000000000)⟩
def e133 : ℝ := (555819/2500000000000)
theorem h133 : Model (fun x => f133 ((17/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(47058823529411/100000000000000),(-276816608997/50000000000000),(814166497/12500000000000),(-19156859/25000000000000)⟩
def e134 : ℝ := (182447/20000000000000)
theorem h134 : Model (fun x => f134 ((17/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (21/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-156046025005771/100000000000000),(-554864680027/50000000000000),(11159323373/50000000000000),(-756171/250000000000)⟩
def e135 : ℝ := (20237737/100000000000000)
theorem h135 : Model (fun x => f135 ((17/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(417605/2048),(4913/512),(867/5120),(17/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((17/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((17/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(44217/256),(7803/1280),(459/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((17/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(771341/2048),(40171/2560),(6171/25600),(103/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((17/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-289/64),(-17/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((17/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(762093/2048),(39899/2560),(1231/5120),(103/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((17/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((17/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(51/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((17/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-51/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((17/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(735981/2048),(7903/512),(1231/5120),(103/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((17/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(742125/2048),(7903/512),(1231/5120),(103/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((17/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((17/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(742125/32),(7903/8),(1231/80),(103/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((17/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((17/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(78927345/4096),(928557/1024),(163863/10240),(3213/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((17/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(51895829/1000000000000),(-122107833/50000000000000),(7182813/100000000000000),(-10563/6250000000000)⟩
def e151 : ℝ := (3971/100000000000000)
theorem h151 : Model (fun x => f151 ((17/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (4696691013/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(120353725301953/100000000000000),(-537045515483/100000000000000),(1294922531/25000000000000),(-47153317/100000000000000)⟩
def e152 : ℝ := (90451687/50000000000000)
theorem h152 : Model (fun x => f152 ((17/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(41/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((17/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1353/64),(37/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((17/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(75/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((17/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(5333333333333/100000000000000),(-42666666667/100000000000000),(341333333/100000000000000),(-2730667/100000000000000)⟩
def e156 : ℝ := (22023/100000000000000)
theorem h156 : Model (fun x => f156 ((17/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (93/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(14093749999999/12500000000000),(165666666663/50000000000000),(682666659/100000000000000),(-5461341/100000000000000)⟩
def e157 : ℝ := (890529/100000000000000)
theorem h157 : Model (fun x => f157 ((17/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(26593749999999/12500000000000),(165666666663/50000000000000),(682666659/100000000000000),(-5461341/100000000000000)⟩
def e158 : ℝ := (890529/100000000000000)
theorem h158 : Model (fun x => f158 ((17/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(26593749999999/25000000000000),(165666666663/100000000000000),(341333329/100000000000000),(-2730671/100000000000000)⟩
def e159 : ℝ := (222633/50000000000000)
theorem h159 : Model (fun x => f159 ((17/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(1593749999999/25000000000000),(165666666663/100000000000000),(341333329/100000000000000),(-2730671/100000000000000)⟩
def e160 : ℝ := (222633/50000000000000)
theorem h160 : Model (fun x => f160 ((17/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((17/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((17/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(39257440476189/10000000000000),(4891111111/800000000000),(1259682523/100000000000000),(-10077477/100000000000000)⟩
def e163 : ℝ := (821623/50000000000000)
theorem h163 : Model (fun x => f163 ((17/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(109931547619047/4000000000000),(4891111111/800000000000),(1259682523/100000000000000),(-10077477/100000000000000)⟩
def e164 : ℝ := (1643247/100000000000000)
theorem h164 : Model (fun x => f164 ((17/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((17/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2923492094493921/100000000000000),(650420399291/12500000000000),(5866840077/50000000000000),(-81592891/100000000000000)⟩
def e166 : ℝ := (14019817/100000000000000)
theorem h166 : Model (fun x => f166 ((17/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8205873046874873/100000000000000),(650420399291/12500000000000),(5866840077/50000000000000),(-81592891/100000000000000)⟩
def e167 : ℝ := (7009909/50000000000000)
theorem h167 : Model (fun x => f167 ((17/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((17/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8728997453612817/100000000000000),(19129473945321/100000000000000),(24555660133/50000000000000),(-17104389/6250000000000)⟩
def e169 : ℝ := (12933963/25000000000000)
theorem h169 : Model (fun x => f169 ((17/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3499511268165109/25000000000000),(19129473945321/100000000000000),(24555660133/50000000000000),(-17104389/6250000000000)⟩
def e170 : ℝ := (51735853/100000000000000)
theorem h170 : Model (fun x => f170 ((17/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((17/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(7445210223020989/50000000000000),(8707814515839/20000000000000),(131713322009/100000000000000),(-526700901/100000000000000)⟩
def e172 : ℝ := (118344229/100000000000000)
theorem h172 : Model (fun x => f172 ((17/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(17226134731756263/100000000000000),(8707814515839/20000000000000),(131713322009/100000000000000),(-526700901/100000000000000)⟩
def e173 : ℝ := (11834423/10000000000000)
theorem h173 : Model (fun x => f173 ((17/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((17/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(3664860164181007/20000000000000),(37426325830547/50000000000000),(135519157831/50000000000000),(-331924357/50000000000000)⟩
def e175 : ℝ := (102299511/50000000000000)
theorem h175 : Model (fun x => f175 ((17/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(18726681773285987/100000000000000),(37426325830547/50000000000000),(135519157831/50000000000000),(-331924357/50000000000000)⟩
def e176 : ℝ := (204599023/100000000000000)
theorem h176 : Model (fun x => f176 ((17/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((17/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(19920507736332219/100000000000000),(27662094418719/25000000000000),(476243307509/100000000000000),(-128253987/25000000000000)⟩
def e178 : ℝ := (303928217/100000000000000)
theorem h178 : Model (fun x => f178 ((17/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(19902888688713171/100000000000000),(27662094418719/25000000000000),(476243307509/100000000000000),(-128253987/25000000000000)⟩
def e179 : ℝ := (151964109/50000000000000)
theorem h179 : Model (fun x => f179 ((17/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((17/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(21171697842617839/100000000000000),(150674664011883/100000000000000),(757846489901/100000000000000),(77453079/100000000000000)⟩
def e181 : ℝ := (41518433/10000000000000)
theorem h181 : Model (fun x => f181 ((17/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(5293757793987793/25000000000000),(150674664011883/100000000000000),(757846489901/100000000000000),(77453079/100000000000000)⟩
def e182 : ℝ := (415184331/100000000000000)
theorem h182 : Model (fun x => f182 ((17/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(33747705936651/2500000000000),(55856847681/125000000000),(185103922967/50000000000000),(1196519063/100000000000000)⟩
def e183 : ℝ := (123536513/100000000000000)
theorem h183 : Model (fun x => f183 ((17/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(113156406249991/100000000000000),(14098233333/4000000000000),(1000641101/100000000000000),(-584819/12500000000000)⟩
def e184 : ℝ := (478343/50000000000000)
theorem h184 : Model (fun x => f184 ((17/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(51593749999999/25000000000000),(165666666663/100000000000000),(341333329/100000000000000),(-2730671/100000000000000)⟩
def e185 : ℝ := (222633/50000000000000)
theorem h185 : Model (fun x => f185 ((17/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(425906406249983/100000000000000),(683789166651/100000000000000),(1683307759/100000000000000),(-5069947/50000000000000)⟩
def e186 : ℝ := (923609/50000000000000)
theorem h186 : Model (fun x => f186 ((17/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(175792869179677/20000000000000),(1058377419507/50000000000000),(6060497621/100000000000000),(-27433629/100000000000000)⟩
def e187 : ℝ := (5744539/100000000000000)
theorem h187 : Model (fun x => f187 ((17/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(453490667211939/25000000000000),(5824603732021/100000000000000),(19014307411/100000000000000),(-63352363/100000000000000)⟩
def e188 : ℝ := (3967709/25000000000000)
theorem h188 : Model (fun x => f188 ((17/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(410522993356909/20000000000000),(12984329502149/100000000000000),(30098159291/50000000000000),(-3125403/10000000000000)⟩
def e189 : ℝ := (17865929/50000000000000)
theorem h189 : Model (fun x => f189 ((17/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((17/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(26593749999999/3125000000000),(165666666663/12500000000000),(341333329/12500000000000),(-2730671/12500000000000)⟩
def e191 : ℝ := (222633/6250000000000)
theorem h191 : Model (fun x => f191 ((17/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(964156406249959/100000000000000),(1677789166629/100000000000000),(3731307733/100000000000000),(-331549/1250000000000)⟩
def e192 : ℝ := (2259407/50000000000000)
theorem h192 : Model (fun x => f192 ((17/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1064156406249959/100000000000000),(1677789166629/100000000000000),(3731307733/100000000000000),(-331549/1250000000000)⟩
def e193 : ℝ := (2259407/50000000000000)
theorem h193 : Model (fun x => f193 ((17/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(21843033664683203/100000000000000),(86306062875519/50000000000000),(935022035247/100000000000000),(77178361/12500000000000)⟩
def e194 : ℝ := (475926381/100000000000000)
theorem h194 : Model (fun x => f194 ((17/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(114452966487/25000000000000),(-452225871/12500000000000),(8992027/100000000000000),(35433/50000000000000)⟩
def e195 : ℝ := (1099/10000000000000)
theorem h195 : Model (fun x => f195 ((17/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (21669485423543649/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(6180040090529/100000000000000),(6229533881/4000000000000),(99802609/50000000000000),(-2940843/100000000000000)⟩
def e196 : ℝ := (745393/100000000000000)
theorem h196 : Model (fun x => f196 ((17/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(14093749999999/6250000000000),(165666666663/25000000000000),(682666659/50000000000000),(-5461341/50000000000000)⟩
def e197 : ℝ := (890529/50000000000000)
theorem h197 : Model (fun x => f197 ((17/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(11750881316099/25000000000000),(-73202513297/100000000000000),(-4602413/12500000000000),(1498823/100000000000000)⟩
def e198 : ℝ := (201471/100000000000000)
theorem h198 : Model (fun x => f198 ((17/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (212417977648137/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(21198589894241/20000000000000),(146405026593/100000000000000),(14727721/20000000000000),(-187353/6250000000000)⟩
def e199 : ℝ := (1311573/100000000000000)
theorem h199 : Model (fun x => f199 ((17/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1198589894241/20000000000000),(146405026593/100000000000000),(14727721/20000000000000),(-187353/6250000000000)⟩
def e200 : ℝ := (1311573/100000000000000)
theorem h200 : Model (fun x => f200 ((17/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(391164456381827/100000000000000),(540304264807/100000000000000),(135880759/50000000000000),(-11062749/100000000000000)⟩
def e201 : ℝ := (1210083/25000000000000)
theorem h201 : Model (fun x => f201 ((17/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(171679921381007/6250000000000),(540304264807/100000000000000),(135880759/50000000000000),(-11062749/100000000000000)⟩
def e202 : ℝ := (4840333/100000000000000)
theorem h202 : Model (fun x => f202 ((17/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2911497797145203/100000000000000),(459425297923/10000000000000),(3101843837/100000000000000),(-18654349/20000000000000)⟩
def e203 : ℝ := (329633/800000000000)
theorem h203 : Model (fun x => f203 ((17/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1638775749905231/20000000000000),(459425297923/10000000000000),(3101843837/100000000000000),(-18654349/20000000000000)⟩
def e204 : ℝ := (20602063/50000000000000)
theorem h204 : Model (fun x => f204 ((17/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8684933762717061/100000000000000),(2108229325137/12500000000000),(16047811073/100000000000000),(-336560717/100000000000000)⟩
def e205 : ℝ := (75767491/50000000000000)
theorem h205 : Model (fun x => f205 ((17/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(348849534544117/2500000000000),(2108229325137/12500000000000),(16047811073/100000000000000),(-336560717/100000000000000)⟩
def e206 : ℝ := (151534983/100000000000000)
theorem h206 : Model (fun x => f206 ((17/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(1479023643519519/10000000000000),(38305925699391/100000000000000),(25988747573/50000000000000),(-184776827/25000000000000)⟩
def e207 : ℝ := (34506369/10000000000000)
theorem h207 : Model (fun x => f207 ((17/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(685038028836379/4000000000000),(38305925699391/100000000000000),(25988747573/50000000000000),(-184776827/25000000000000)⟩
def e208 : ℝ := (345063691/100000000000000)
theorem h208 : Model (fun x => f208 ((17/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(2269037536759631/12500000000000),(16418708294571/25000000000000),(123785592077/100000000000000),(-59623587/5000000000000)⟩
def e209 : ℝ := (148391327/25000000000000)
theorem h209 : Model (fun x => f209 ((17/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(9277340623229/50000000000),(16418708294571/25000000000000),(123785592077/100000000000000),(-59623587/5000000000000)⟩
def e210 : ℝ := (593565309/100000000000000)
theorem h210 : Model (fun x => f210 ((17/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(9833326959050689/50000000000000),(96775678759079/100000000000000),(120509332737/50000000000000),(-1590549641/100000000000000)⟩
def e211 : ℝ := (13716501/1562500000000)
theorem h211 : Model (fun x => f211 ((17/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(1964903487048233/10000000000000),(96775678759079/100000000000000),(120509332737/50000000000000),(-1590549641/100000000000000)⟩
def e212 : ℝ := (175571213/20000000000000)
theorem h212 : Model (fun x => f212 ((17/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(10413295800924893/50000000000000),(131342571014923/100000000000000),(411616525709/100000000000000),(-925375839/50000000000000)⟩
def e213 : ℝ := (23915919/2000000000000)
theorem h213 : Model (fun x => f213 ((17/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(20829924935183119/100000000000000),(131342571014923/100000000000000),(411616525709/100000000000000),(-925375839/50000000000000)⟩
def e214 : ℝ := (1195795951/100000000000000)
theorem h214 : Model (fun x => f214 ((17/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(249665375251091/20000000000000),(19183675527881/50000000000000),(29037370321/12500000000000),(-35976321/100000000000000)⟩
def e215 : ℝ := (70940053/20000000000000)
theorem h215 : Model (fun x => f215 ((17/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(56172526688027/50000000000000),(7758950293/2500000000000),(11576493/3125000000000),(-613897/10000000000000)⟩
def e216 : ℝ := (1396461/50000000000000)
theorem h216 : Model (fun x => f216 ((17/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(41198589894241/20000000000000),(146405026593/100000000000000),(14727721/20000000000000),(-187353/6250000000000)⟩
def e217 : ℝ := (1311573/100000000000000)
theorem h217 : Model (fun x => f217 ((17/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(828771391247/195312500000),(301584032453/50000000000000),(258862493/50000000000000),(-6067133/50000000000000)⟩
def e218 : ℝ := (1354017/25000000000000)
theorem h218 : Model (fun x => f218 ((17/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(109261480525007/12500000000000),(14560355709/781250000000),(282752091/12500000000000),(-36513541/100000000000000)⟩
def e219 : ℝ := (524171/3125000000000)
theorem h219 : Model (fun x => f219 ((17/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(360113514190989/20000000000000),(319928599237/6250000000000),(4015925937/50000000000000),(-9673339/10000000000000)⟩
def e220 : ℝ := (1846933/4000000000000)
theorem h220 : Model (fun x => f220 ((17/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2022848598661251/100000000000000),(11338989002139/100000000000000),(31580335429/100000000000000),(-43830323/25000000000000)⟩
def e221 : ℝ := (12879267/12500000000000)
theorem h221 : Model (fun x => f221 ((17/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(21198589894241/2500000000000),(146405026593/12500000000000),(14727721/2500000000000),(-187353/781250000000)⟩
def e222 : ℝ := (1311573/12500000000000)
theorem h222 : Model (fun x => f222 ((17/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(480144324572847/50000000000000),(92599889029/6250000000000),(119944577/12500000000000),(-15060077/50000000000000)⟩
def e223 : ℝ := (6642753/50000000000000)
theorem h223 : Model (fun x => f223 ((17/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(530144324572847/50000000000000),(92599889029/6250000000000),(119944577/12500000000000),(-15060077/50000000000000)⟩
def e224 : ℝ := (6642753/50000000000000)
theorem h224 : Model (fun x => f224 ((17/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(21448034081007979/100000000000000),(75098251119459/50000000000000),(522251349203/100000000000000),(-472874791/25000000000000)⟩
def e225 : ℝ := (171245533/12500000000000)
theorem h225 : Model (fun x => f225 ((17/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(93248639593/20000000000000),(-1632506207/50000000000000),(5755709/50000000000000),(40007/100000000000000)⟩
def e226 : ℝ := (31059/100000000000000)
theorem h226 : Model (fun x => f226 ((17/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (2129731206595643/10000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(582023914891/10000000000000),(138127137059/100000000000000),(-25920539/100000000000000),(-2836283/100000000000000)⟩
def e227 : ℝ := (2108451/100000000000000)
theorem h227 : Model (fun x => f227 ((17/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(12000279239439/100000000000000),(73466371021/25000000000000),(173684679/100000000000000),(-2888563/50000000000000)⟩
def e228 : ℝ := (713461/25000000000000)
theorem h228 : Model (fun x => f228 ((17/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(14442783111301/100000000000000),(28923109597/10000000000000),(-23361817/3125000000000),(1677039/100000000000000)⟩
def e229 : ℝ := (1611873/6250000000000)
theorem h229 : Model (fun x => f229 ((17/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3398301908541/50000000000000),(56148706137/100000000000000),(-1012374493/100000000000000),(6349741/50000000000000)⟩
def e230 : ℝ := (3173907/25000000000000)
theorem h230 : Model (fun x => f230 ((17/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-149249421188689/100000000000000),(-1053580653917/100000000000000),(21306272253/100000000000000),(-144884459/50000000000000)⟩
def e231 : ℝ := (6586673/20000000000000)
theorem h231 : Model (fun x => f231 ((17/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((17/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-1445/64),(-17/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((17/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(357/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((17/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1411/64),(-1/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((17/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((17/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3075/64),(-1/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((17/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((17/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(384375/32),(-25/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((17/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(527/64),(7/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((17/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(911/64),(7/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((17/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((17/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(172179/64),(1323/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((17/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(9292654737/25000000000000),(-114245591/100000000000000),(991609/50000000000000),(-1389/12500000000000)⟩
def e244 : ℝ := (1/800000000000)
theorem h244 : Model (fun x => f244 ((17/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (268191/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(111620755141699/25000000000000),(-715182499813/50000000000000),(-2519590241/50000000000000),(-47318629/100000000000000)⟩
def e245 : ℝ := (760617/25000000000000)
theorem h245 : Model (fun x => f245 ((17/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(153/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((17/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(2737/64),(89/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((17/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(4081/64),(89/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((17/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(1089/64),(33/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((17/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(4444209/4096),(115797/5120),(8459/51200),(61/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((17/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((17/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(28125/32),(225/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((17/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(113777777777/100000000000000),(-364088889/20000000000000),(21845333/100000000000000),(-233017/100000000000000)⟩
def e253 : ℝ := (1193/50000000000000)
theorem h253 : Model (fun x => f253 ((17/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (69183/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(30862562499789/25000000000000),(299031333023/50000000000000),(82997421/6250000000000),(-5301263/100000000000000)⟩
def e254 : ℝ := (5244997/100000000000000)
theorem h254 : Model (fun x => f254 ((17/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(55862562499789/25000000000000),(299031333023/50000000000000),(82997421/6250000000000),(-5301263/100000000000000)⟩
def e255 : ℝ := (5244997/100000000000000)
theorem h255 : Model (fun x => f255 ((17/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(55862562499789/50000000000000),(299031333023/100000000000000),(82997421/12500000000000),(-331329/12500000000000)⟩
def e256 : ℝ := (2622499/100000000000000)
theorem h256 : Model (fun x => f256 ((17/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(5862562499789/50000000000000),(299031333023/100000000000000),(82997421/12500000000000),(-331329/12500000000000)⟩
def e257 : ℝ := (2622499/100000000000000)
theorem h257 : Model (fun x => f257 ((17/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(206159456844459/50000000000000),(1103568014727/100000000000000),(153150003/6250000000000),(-1956419/20000000000000)⟩
def e258 : ℝ := (9678273/100000000000000)
theorem h258 : Model (fun x => f258 ((17/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2768033199403203/100000000000000),(1103568014727/100000000000000),(153150003/6250000000000),(-1956419/20000000000000)⟩
def e259 : ℝ := (4839137/50000000000000)
theorem h259 : Model (fun x => f259 ((17/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1546294276031523/50000000000000),(9510249318603/100000000000000),(4883379201/20000000000000),(-8705563/12500000000000)⟩
def e260 : ℝ := (20876271/25000000000000)
theorem h260 : Model (fun x => f260 ((17/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4187484752221999/50000000000000),(9510249318603/100000000000000),(4883379201/20000000000000),(-8705563/12500000000000)⟩
def e261 : ℝ := (16701017/20000000000000)
theorem h261 : Model (fun x => f261 ((17/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4678472573758297/50000000000000),(35669120888389/100000000000000),(111326502479/100000000000000),(-20454971/12500000000000)⟩
def e262 : ℝ := (313729297/100000000000000)
theorem h262 : Model (fun x => f262 ((17/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14625992766564213/100000000000000),(35669120888389/100000000000000),(111326502479/100000000000000),(-20454971/12500000000000)⟩
def e263 : ℝ := (156864649/50000000000000)
theorem h263 : Model (fun x => f263 ((17/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(16340908700873103/100000000000000),(83587671036507/100000000000000),(328155096057/100000000000000),(-771253/100000000000000)⟩
def e264 : ℝ := (73665921/10000000000000)
theorem h264 : Model (fun x => f264 ((17/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(4669155746646847/25000000000000),(83587671036507/100000000000000),(328155096057/100000000000000),(-771253/100000000000000)⟩
def e265 : ℝ := (736659211/100000000000000)
theorem h265 : Model (fun x => f265 ((17/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(20866480377464677/100000000000000),(29847476926049/20000000000000),(29623757659/4000000000000),(1040381219/100000000000000)⟩
def e266 : ℝ := (131728387/10000000000000)
theorem h266 : Model (fun x => f266 ((17/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(21268861329845629/100000000000000),(29847476926049/20000000000000),(29623757659/4000000000000),(1040381219/100000000000000)⟩
def e267 : ℝ := (1317283871/100000000000000)
theorem h267 : Model (fun x => f267 ((17/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(2970332738344617/12500000000000),(57584053519423/25000000000000),(1414916898519/100000000000000),(3804121351/100000000000000)⟩
def e268 : ℝ := (2041479309/100000000000000)
theorem h268 : Model (fun x => f268 ((17/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(742032589348059/3125000000000),(57584053519423/25000000000000),(1414916898519/100000000000000),(3804121351/100000000000000)⟩
def e269 : ℝ := (204147931/10000000000000)
theorem h269 : Model (fun x => f269 ((17/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(1061167152623007/4000000000000),(328348541286159/100000000000000),(2427257310409/100000000000000),(9381195431/100000000000000)⟩
def e270 : ℝ := (2930432173/100000000000000)
theorem h270 : Model (fun x => f270 ((17/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(6633128037227127/25000000000000),(328348541286159/100000000000000),(2427257310409/100000000000000),(9381195431/100000000000000)⟩
def e271 : ℝ := (1465216087/50000000000000)
theorem h271 : Model (fun x => f271 ((17/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(3110970214987741/100000000000000),(117839801663463/100000000000000),(1442634380157/100000000000000),(9835104093/100000000000000)⟩
def e272 : ℝ := (1092337251/100000000000000)
theorem h272 : Model (fun x => f272 ((17/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(124825035561713/100000000000000),(133637252243/20000000000000),(2377860939/100000000000000),(-243979/12500000000000)⟩
def e273 : ℝ := (5887181/100000000000000)
theorem h273 : Model (fun x => f273 ((17/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(105862562499789/50000000000000),(299031333023/100000000000000),(82997421/12500000000000),(-331329/12500000000000)⟩
def e274 : ℝ := (2622499/100000000000000)
theorem h274 : Model (fun x => f274 ((17/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(448275285560869/100000000000000),(1266248927261/100000000000000),(148232787/4000000000000),(-906637/12500000000000)⟩
def e275 : ℝ := (11132179/100000000000000)
theorem h275 : Model (fun x => f275 ((17/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(189822281739193/20000000000000),(2010725343037/50000000000000),(14609087793/100000000000000),(-3874781/50000000000000)⟩
def e276 : ℝ := (35423099/100000000000000)
theorem h276 : Model (fun x => f276 ((17/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(2009507316446787/100000000000000),(11352561989183/100000000000000),(49258410917/100000000000000),(7205533/25000000000000)⟩
def e277 : ℝ := (50067627/50000000000000)
theorem h277 : Model (fun x => f277 ((17/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1254184111184963/50000000000000),(2759809134677/10000000000000),(46281594499/25000000000000),(595841101/100000000000000)⟩
def e278 : ℝ := (245782503/100000000000000)
theorem h278 : Model (fun x => f278 ((17/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(55862562499789/6250000000000),(299031333023/12500000000000),(82997421/1562500000000),(-331329/1562500000000)⟩
def e279 : ℝ := (2622499/12500000000000)
theorem h279 : Model (fun x => f279 ((17/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1018626035558337/100000000000000),(3060436925399/100000000000000),(7689695883/100000000000000),(-2894611/12500000000000)⟩
def e280 : ℝ := (26867173/100000000000000)
theorem h280 : Model (fun x => f280 ((17/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1118626035558337/100000000000000),(3060436925399/100000000000000),(7689695883/100000000000000),(-2894611/12500000000000)⟩
def e281 : ℝ := (26867173/100000000000000)
theorem h281 : Model (fun x => f281 ((17/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(14029630001550917/50000000000000),(15419458496981/4000000000000),(3108379929157/100000000000000),(13872258991/100000000000000)⟩
def e282 : ℝ := (866100923/25000000000000)
theorem h282 : Model (fun x => f282 ((17/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(356388586117/100000000000000),(-4896172433/100000000000000),(13892331/50000000000000),(-3879/25000000000000)⟩
def e283 : ℝ := (45701/100000000000000)
theorem h283 : Model (fun x => f283 ((17/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (27670647824085469/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(2217428552743/20000000000000),(133824568483/50000000000000),(47223389/20000000000000),(-1661993/50000000000000)⟩
def e284 : ℝ := (5524523/100000000000000)
theorem h284 : Model (fun x => f284 ((17/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(30862562499789/12500000000000),(299031333023/25000000000000),(82997421/3125000000000),(-5301263/50000000000000)⟩
def e285 : ℝ := (5244997/50000000000000)
theorem h285 : Model (fun x => f285 ((17/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(44752691035421/100000000000000),(-119780191401/100000000000000),(54626627/100000000000000),(1627381/100000000000000)⟩
def e286 : ℝ := (1063669/100000000000000)
theorem h286 : Model (fun x => f286 ((17/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (111425424414057/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(55247308964577/50000000000000),(239560382799/100000000000000),(-109253257/100000000000000),(-813691/25000000000000)⟩
def e287 : ℝ := (922467/12500000000000)
theorem h287 : Model (fun x => f287 ((17/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(5247308964577/50000000000000),(239560382799/100000000000000),(-109253257/100000000000000),(-813691/25000000000000)⟩
def e288 : ℝ := (922467/12500000000000)
theorem h288 : Model (fun x => f288 ((17/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(203888878321653/50000000000000),(884091888901/100000000000000),(-3149973/781250000000),(-1201163/10000000000000)⟩
def e289 : ℝ := (13617371/50000000000000)
theorem h289 : Model (fun x => f289 ((17/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2763492042357591/100000000000000),(884091888901/100000000000000),(-3149973/781250000000),(-1201163/10000000000000)⟩
def e290 : ℝ := (27234743/100000000000000)
theorem h290 : Model (fun x => f290 ((17/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1526754986852797/50000000000000),(303884242803/4000000000000),(-1346781631/100000000000000),(-26287287/25000000000000)⟩
def e291 : ℝ := (29277379/12500000000000)
theorem h291 : Model (fun x => f291 ((17/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4167945463043273/50000000000000),(303884242803/4000000000000),(-1346781631/100000000000000),(-26287287/25000000000000)⟩
def e292 : ℝ := (234219033/100000000000000)
theorem h292 : Model (fun x => f292 ((17/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4605355414885173/50000000000000),(28363885538041/100000000000000),(1901075707/25000000000000),(-49878021/12500000000000)⟩
def e293 : ℝ := (875586157/100000000000000)
theorem h293 : Model (fun x => f293 ((17/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(2895951689763593/20000000000000),(28363885538041/100000000000000),(1901075707/25000000000000),(-49878021/12500000000000)⟩
def e294 : ℝ := (437793079/50000000000000)
theorem h294 : Model (fun x => f294 ((17/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(7999676887542903/50000000000000),(66028331723479/100000000000000),(3783210651/6250000000000),(-924953767/100000000000000)⟩
def e295 : ℝ := (1021061749/50000000000000)
theorem h295 : Model (fun x => f295 ((17/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(18335068060800091/100000000000000),(66028331723479/100000000000000),(3783210651/6250000000000),(-924953767/100000000000000)⟩
def e296 : ℝ := (2042123499/100000000000000)
theorem h296 : Model (fun x => f296 ((17/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(4051852680166281/20000000000000),(58440656047881/50000000000000),(205029971671/100000000000000),(-772958123/50000000000000)⟩
def e297 : ℝ := (3623720009/100000000000000)
theorem h297 : Model (fun x => f297 ((17/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(20661644353212357/100000000000000),(58440656047881/50000000000000),(205029971671/100000000000000),(-772958123/50000000000000)⟩
def e298 : ℝ := (362372001/10000000000000)
theorem h298 : Model (fun x => f298 ((17/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(2853750623245327/12500000000000),(178644673535917/100000000000000),(483974883109/100000000000000),(-504292017/25000000000000)⟩
def e299 : ℝ := (2776926579/50000000000000)
theorem h299 : Model (fun x => f299 ((17/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(1425774121146473/6250000000000),(178644673535917/100000000000000),(483974883109/100000000000000),(-504292017/25000000000000)⟩
def e300 : ℝ := (5553853159/100000000000000)
theorem h300 : Model (fun x => f300 ((17/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(12603229341548389/50000000000000),(252042188553777/100000000000000),(937804787099/100000000000000),(-2007114517/100000000000000)⟩
def e301 : ℝ := (7857922719/100000000000000)
theorem h301 : Model (fun x => f301 ((17/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(25209792016430111/100000000000000),(252042188553777/100000000000000),(937804787099/100000000000000),(-2007114517/100000000000000)⟩
def e302 : ℝ := (49112017/625000000000)
theorem h302 : Model (fun x => f302 ((17/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(661417838214677/25000000000000),(21710884741597/25000000000000),(33733487109/5000000000000),(470043101/50000000000000)⟩
def e303 : ℝ := (342080371/12500000000000)
theorem h303 : Model (fun x => f303 ((17/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(122090605913097/100000000000000),(264701329683/50000000000000),(41556729/12500000000000),(-3858067/50000000000000)⟩
def e304 : ℝ := (8179641/50000000000000)
theorem h304 : Model (fun x => f304 ((17/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(105247308964577/50000000000000),(239560382799/100000000000000),(-109253257/100000000000000),(-813691/25000000000000)⟩
def e305 : ℝ := (922467/12500000000000)
theorem h305 : Model (fun x => f305 ((17/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(88615968354281/20000000000000),(252130856241/25000000000000),(56973659/50000000000000),(-7112831/50000000000000)⟩
def e306 : ℝ := (15559377/50000000000000)
theorem h306 : Model (fun x => f306 ((17/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(932659220057819/100000000000000),(796082823789/25000000000000),(217179639/10000000000000),(-45194329/100000000000000)⟩
def e307 : ℝ := (9841749/10000000000000)
theorem h307 : Model (fun x => f307 ((17/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1963197461841733/100000000000000),(8937127991117/100000000000000),(5590475089/50000000000000),(-123763709/100000000000000)⟩
def e308 : ℝ := (276676663/100000000000000)
theorem h308 : Model (fun x => f308 ((17/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2396879676433113/100000000000000),(21304613287179/100000000000000),(33745504133/50000000000000),(-213682737/100000000000000)⟩
def e309 : ℝ := (331599883/50000000000000)
theorem h309 : Model (fun x => f309 ((17/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(55247308964577/6250000000000),(239560382799/12500000000000),(-109253257/12500000000000),(-813691/3125000000000)⟩
def e310 : ℝ := (922467/1562500000000)
theorem h310 : Model (fun x => f310 ((17/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1006047549346329/100000000000000),(1222942860879/50000000000000),(-4231033/781250000000),(-16877123/50000000000000)⟩
def e311 : ℝ := (7539717/10000000000000)
theorem h311 : Model (fun x => f311 ((17/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1106047549346329/100000000000000),(1222942860879/50000000000000),(-4231033/781250000000),(-16877123/50000000000000)⟩
def e312 : ℝ := (7539717/10000000000000)
theorem h312 : Model (fun x => f312 ((17/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(13255314460984333/50000000000000),(36783011366769/12500000000000),(1254588302851/100000000000000),(-102319267/6250000000000)⟩
def e313 : ℝ := (9187628609/100000000000000)
theorem h313 : Model (fun x => f313 ((17/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(75441439201/20000000000000),(-2093472263/50000000000000),(14311763/50000000000000),(-96281/100000000000000)⟩
def e314 : ℝ := (134237/100000000000000)
theorem h314 : Model (fun x => f314 ((17/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (13107549708997391/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(15967460361/160000000000),(108403643181/50000000000000),(-333903557/100000000000000),(-2391571/100000000000000)⟩
def e315 : ℝ := (14177661/100000000000000)
theorem h315 : Model (fun x => f315 ((17/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1053340274467/5000000000000),(15139263229/3125000000000),(-24446653/25000000000000),(-5715557/100000000000000)⟩
def e316 : ℝ := (2462773/12500000000000)
theorem h316 : Model (fun x => f316 ((17/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(11757463685717/12500000000000),(372336691989/20000000000000),(-1053461261/12500000000000),(-14625361/25000000000000)⟩
def e317 : ℝ := (44524157/50000000000000)
theorem h317 : Model (fun x => f317 ((17/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(44263392699169/100000000000000),(35534053763/10000000000000),(-101830609/1250000000000),(853881/1250000000000)⟩
def e318 : ℝ := (561667/1250000000000)
theorem h318 : Model (fun x => f318 ((17/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-1312325356119/1250000000000),(-698240116287/100000000000000),(13159823533/100000000000000),(-110729219/50000000000000)⟩
def e319 : ℝ := (3114669/4000000000000)
theorem h319 : Model (fun x => f319 ((17/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((17/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-3179/64),(-187/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((17/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((17/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(1649/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((17/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(10013/64),(201/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((17/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((17/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(16925/64),(201/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((17/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2115625/32),(5025/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((17/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((17/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(208389499864581607/20000000000000),(1601236552197663/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (16867/12500000000000)
theorem h329 : Model (fun x => f329 ((17/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9597412543/100000000000000),(-5899617/20000000000000),(8001/1562500000000),(-287/10000000000000)⟩
def e330 : ℝ := (7/20000000000000)
theorem h330 : Model (fun x => f330 ((17/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (129837409575325087/12500000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(158629108681909/25000000000000),(265993046711/25000000000000),(8094436121/100000000000000),(680463/3125000000000)⟩
def e331 : ℝ := (2055711/50000000000000)
theorem h331 : Model (fun x => f331 ((17/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((17/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(89/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((17/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((17/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((17/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(675806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((17/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((17/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((17/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1499105313224107/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (53/5000000000000)
theorem h339 : Model (fun x => f339 ((17/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3774193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((17/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((17/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((17/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2126789373551527/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1059/100000000000000)
theorem h343 : Model (fun x => f343 ((17/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(940384612069/20000000000000),(-6229043717/100000000000000),(1031519/12500000000000),(-10933/100000000000000)⟩
def e344 : ℝ := (19/100000000000000)
theorem h344 : Model (fun x => f344 ((17/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2123971831915987/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(70486778421341/50000000000000),(85624227459/10000000000000),(-1134338131/100000000000000),(300547/20000000000000)⟩
def e345 : ℝ := (763/25000000000000)
theorem h345 : Model (fun x => f345 ((17/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(120486778421341/50000000000000),(85624227459/10000000000000),(-1134338131/100000000000000),(300547/20000000000000)⟩
def e346 : ℝ := (763/25000000000000)
theorem h346 : Model (fun x => f346 ((17/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(120486778421341/100000000000000),(85624227459/20000000000000),(-283584533/50000000000000),(751367/100000000000000)⟩
def e347 : ℝ := (1527/100000000000000)
theorem h347 : Model (fun x => f347 ((17/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(20486778421341/100000000000000),(85624227459/20000000000000),(-283584533/50000000000000),(751367/100000000000000)⟩
def e348 : ℝ := (1527/100000000000000)
theorem h348 : Model (fun x => f348 ((17/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(444653587031139/100000000000000),(789985431913/50000000000000),(-418624787/20000000000000),(1386451/50000000000000)⟩
def e349 : ℝ := (2819/50000000000000)
theorem h349 : Model (fun x => f349 ((17/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(175022992046589/6250000000000),(789985431913/50000000000000),(-418624787/20000000000000),(1386451/50000000000000)⟩
def e350 : ℝ := (5639/100000000000000)
theorem h350 : Model (fun x => f350 ((17/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3374073033817199/100000000000000),(13892622779061/100000000000000),(-465622747/4000000000000),(201869/3125000000000)⟩
def e351 : ℝ := (21313/25000000000000)
theorem h351 : Model (fun x => f351 ((17/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8656453986198151/100000000000000),(13892622779061/100000000000000),(-465622747/4000000000000),(201869/3125000000000)⟩
def e352 : ℝ := (85253/100000000000000)
theorem h352 : Model (fun x => f352 ((17/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5214941266747953/50000000000000),(53798882879849/100000000000000),(-3644820767/100000000000000),(-55805441/100000000000000)⟩
def e353 : ℝ := (433669/100000000000000)
theorem h353 : Model (fun x => f353 ((17/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(627957206101741/4000000000000),(53798882879849/100000000000000),(-3644820767/100000000000000),(-55805441/100000000000000)⟩
def e354 : ℝ := (43367/10000000000000)
theorem h354 : Model (fun x => f354 ((17/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(18915135187416207/100000000000000),(132030979120817/100000000000000),(136893386597/100000000000000),(-67504117/25000000000000)⟩
def e355 : ℝ := (190239/20000000000000)
theorem h355 : Model (fun x => f355 ((17/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(5312712368282623/25000000000000),(132030979120817/100000000000000),(136893386597/100000000000000),(-67504117/25000000000000)⟩
def e356 : ℝ := (237799/25000000000000)
theorem h356 : Model (fun x => f356 ((17/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(25604463917343447/100000000000000),(6251481292751/2500000000000),(304831358151/50000000000000),(-328431621/100000000000000)⟩
def e357 : ℝ := (2419603/100000000000000)
theorem h357 : Model (fun x => f357 ((17/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(26006844869724399/100000000000000),(6251481292751/2500000000000),(304831358151/50000000000000),(-328431621/100000000000000)⟩
def e358 : ℝ := (604901/25000000000000)
theorem h358 : Model (fun x => f358 ((17/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(15667404776283363/50000000000000),(412629136560749/100000000000000),(1657616699297/100000000000000),(495763201/50000000000000)⟩
def e359 : ℝ := (6318117/100000000000000)
theorem h359 : Model (fun x => f359 ((17/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(15658595252473839/50000000000000),(412629136560749/100000000000000),(1657616699297/100000000000000),(495763201/50000000000000)⟩
def e360 : ℝ := (3159059/50000000000000)
theorem h360 : Model (fun x => f360 ((17/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(37733073931485551/100000000000000),(126247813125693/20000000000000),(3586140094927/100000000000000),(3093133949/50000000000000)⟩
def e361 : ℝ := (10187159/100000000000000)
theorem h361 : Model (fun x => f361 ((17/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(9434101816204721/25000000000000),(126247813125693/20000000000000),(3586140094927/100000000000000),(3093133949/50000000000000)⟩
def e362 : ℝ := (254679/2500000000000)
theorem h362 : Model (fun x => f362 ((17/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(60398235472799/781250000000),(145439042320331/50000000000000),(3223123213319/100000000000000),(6661868477/50000000000000)⟩
def e363 : ℝ := (13612977/100000000000000)
theorem h363 : Model (fun x => f363 ((17/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(145170637743533/100000000000000),(206331746427/20000000000000),(46614961/10000000000000),(-1522873/50000000000000)⟩
def e364 : ℝ := (13353/100000000000000)
theorem h364 : Model (fun x => f364 ((17/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(220486778421341/100000000000000),(85624227459/20000000000000),(-283584533/50000000000000),(751367/100000000000000)⟩
def e365 : ℝ := (1527/100000000000000)
theorem h365 : Model (fun x => f365 ((17/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(97228838917243/20000000000000),(75516040269/4000000000000),(-334094261/50000000000000),(-385753/25000000000000)⟩
def e366 : ℝ := (16407/100000000000000)
theorem h366 : Model (fun x => f366 ((17/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(13398545914069/1250000000000),(1560964541067/25000000000000),(3851976427/100000000000000),(-6658829/50000000000000)⟩
def e367 : ℝ := (55073/100000000000000)
theorem h367 : Model (fun x => f367 ((17/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(590840444824699/25000000000000),(573620071483/3125000000000),(5828996539/20000000000000),(-20116001/50000000000000)⟩
def e368 : ℝ := (21273/12500000000000)
theorem h368 : Model (fun x => f368 ((17/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(3430907367194971/100000000000000),(25514560739987/50000000000000),(242696408781/100000000000000),(51171079/20000000000000)⟩
def e369 : ℝ := (351549/25000000000000)
theorem h369 : Model (fun x => f369 ((17/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(120486778421341/12500000000000),(85624227459/2500000000000),(-283584533/6250000000000),(751367/12500000000000)⟩
def e370 : ℝ := (1527/12500000000000)
theorem h370 : Model (fun x => f370 ((17/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1109064865114261/100000000000000),(891325566099/20000000000000),(-2035601459/50000000000000),(296519/10000000000000)⟩
def e371 : ℝ := (25569/100000000000000)
theorem h371 : Model (fun x => f371 ((17/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1209064865114261/100000000000000),(891325566099/20000000000000),(-2035601459/50000000000000),(296519/10000000000000)⟩
def e372 : ℝ := (25569/100000000000000)
theorem h372 : Model (fun x => f372 ((17/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(41481895531371119/100000000000000),(384938975677877/50000000000000),(5068855836151/100000000000000),(11933767223/100000000000000)⟩
def e373 : ℝ := (10496553/50000000000000)
theorem h373 : Model (fun x => f373 ((17/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(120534511163/50000000000000),(-894817957/20000000000000),(53579011/100000000000000),(-517037/100000000000000)⟩
def e374 : ℝ := (4597/100000000000000)
theorem h374 : Model (fun x => f374 ((17/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (8141387353883777/20000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(18636983776823/100000000000000),(355326230501/100000000000000),(-68875973/6250000000000),(189579/5000000000000)⟩
def e375 : ℝ := (785089/100000000000000)
theorem h375 : Model (fun x => f375 ((17/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(70486778421341/25000000000000),(85624227459/5000000000000),(-1134338131/50000000000000),(300547/10000000000000)⟩
def e376 : ℝ := (763/12500000000000)
theorem h376 : Model (fun x => f376 ((17/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(8299665848007/20000000000000),(-73727226103/50000000000000),(179822503/25000000000000),(-3508729/100000000000000)⟩
def e377 : ℝ := (17387/100000000000000)
theorem h377 : Model (fun x => f377 ((17/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (120058089362087/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(14625417689991/12500000000000),(36863613051/12500000000000),(-359645007/25000000000000),(3508727/50000000000000)⟩
def e378 : ℝ := (132801/100000000000000)
theorem h378 : Model (fun x => f378 ((17/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(2125417689991/12500000000000),(36863613051/12500000000000),(-359645007/25000000000000),(3508727/50000000000000)⟩
def e379 : ℝ := (132801/100000000000000)
theorem h379 : Model (fun x => f379 ((17/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(53974755760681/12500000000000),(1088354290077/100000000000000),(-2654522671/50000000000000),(12948873/50000000000000)⟩
def e380 : ℝ := (245051/50000000000000)
theorem h380 : Model (fun x => f380 ((17/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2787512331799733/100000000000000),(1088354290077/100000000000000),(-2654522671/50000000000000),(12948873/50000000000000)⟩
def e381 : ℝ := (490103/100000000000000)
theorem h381 : Model (fun x => f381 ((17/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(13045930293943/400000000000),(4747016482457/50000000000000),(-5387837803/12500000000000),(24324991/12500000000000)⟩
def e382 : ℝ := (225403/5000000000000)
theorem h382 : Model (fun x => f382 ((17/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4271931762933351/50000000000000),(4747016482457/50000000000000),(-5387837803/12500000000000),(24324991/12500000000000)⟩
def e383 : ℝ := (4508061/100000000000000)
theorem h383 : Model (fun x => f383 ((17/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(9996605820166379/100000000000000),(36304950132201/100000000000000),(-9083947989/6250000000000),(563557141/100000000000000)⟩
def e384 : ℝ := (18512983/100000000000000)
theorem h384 : Model (fun x => f384 ((17/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(7632826719606999/50000000000000),(36304950132201/100000000000000),(-9083947989/6250000000000),(563557141/100000000000000)⟩
def e385 : ℝ := (2314123/12500000000000)
theorem h385 : Model (fun x => f385 ((17/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(4465331157183047/25000000000000),(43748888050063/50000000000000),(-56519694773/20000000000000),(194933797/25000000000000)⟩
def e386 : ℝ := (6044489/12500000000000)
theorem h386 : Model (fun x => f386 ((17/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(20197038914446473/100000000000000),(43748888050063/50000000000000),(-56519694773/20000000000000),(194933797/25000000000000)⟩
def e387 : ℝ := (48355913/100000000000000)
theorem h387 : Model (fun x => f387 ((17/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4726242083596513/20000000000000),(161938187978223/100000000000000),(-363161492699/100000000000000),(47500109/20000000000000)⟩
def e388 : ℝ := (48097959/50000000000000)
theorem h388 : Model (fun x => f388 ((17/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(24033591370363517/100000000000000),(161938187978223/100000000000000),(-363161492699/100000000000000),(47500109/20000000000000)⟩
def e389 : ℝ := (96195919/100000000000000)
theorem h389 : Model (fun x => f389 ((17/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(28120104990570369/100000000000000),(260350292131577/100000000000000),(-73270847763/25000000000000),(-1436176217/100000000000000)⟩
def e390 : ℝ := (81143773/50000000000000)
theorem h390 : Model (fun x => f390 ((17/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(28102485942951321/100000000000000),(260350292131577/100000000000000),(-73270847763/25000000000000),(-1436176217/100000000000000)⟩
def e391 : ℝ := (162287547/100000000000000)
theorem h391 : Model (fun x => f391 ((17/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(8220211900855273/25000000000000),(387495274856609/100000000000000),(2060208303/10000000000000),(-539746433/12500000000000)⟩
def e392 : ℝ := (61570077/25000000000000)
theorem h392 : Model (fun x => f392 ((17/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(1315367237470177/4000000000000),(387495274856609/100000000000000),(2060208303/10000000000000),(-539746433/12500000000000)⟩
def e393 : ℝ := (246280309/100000000000000)
theorem h393 : Model (fun x => f393 ((17/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(5591409590707413/100000000000000),(162865522681579/100000000000000),(336597926461/50000000000000),(-3940239421/100000000000000)⟩
def e394 : ℝ := (101016609/100000000000000)
theorem h394 : Model (fun x => f394 ((17/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(136897819268289/100000000000000),(345053272597/50000000000000),(-624165197/25000000000000),(793631/10000000000000)⟩
def e395 : ℝ := (4673/1250000000000)
theorem h395 : Model (fun x => f395 ((17/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(27125417689991/12500000000000),(36863613051/12500000000000),(-359645007/25000000000000),(3508727/50000000000000)⟩
def e396 : ℝ := (132801/100000000000000)
theorem h396 : Model (fun x => f396 ((17/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(94180900461629/20000000000000),(127992435401/10000000000000),(-1343455211/25000000000000),(10985609/50000000000000)⟩
def e397 : ℝ := (319721/50000000000000)
theorem h397 : Model (fun x => f397 ((17/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1021878505376461/100000000000000),(4166217925693/100000000000000),(-14661098031/100000000000000),(46463171/100000000000000)⟩
def e398 : ℝ := (562299/25000000000000)
theorem h398 : Model (fun x => f398 ((17/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2217510502940817/100000000000000),(6027221409171/50000000000000),(-855726627/2500000000000),(2774609/4000000000000)⟩
def e399 : ℝ := (3446057/50000000000000)
theorem h399 : Model (fun x => f399 ((17/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1517861760285623/50000000000000),(7951363616103/25000000000000),(-4758514993/25000000000000),(-133113789/50000000000000)⟩
def e400 : ℝ := (4022487/20000000000000)
theorem h400 : Model (fun x => f400 ((17/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(14625417689991/1562500000000),(36863613051/1562500000000),(-359645007/3125000000000),(3508727/6250000000000)⟩
def e401 : ℝ := (132801/12500000000000)
theorem h401 : Model (fun x => f401 ((17/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1072924551427713/100000000000000),(1524688890229/50000000000000),(-3501325253/25000000000000),(32037971/50000000000000)⟩
def e402 : ℝ := (179531/12500000000000)
theorem h402 : Model (fun x => f402 ((17/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1172924551427713/100000000000000),(1524688890229/50000000000000),(-3501325253/25000000000000),(32037971/50000000000000)⟩
def e403 : ℝ := (179531/12500000000000)
theorem h403 : Model (fun x => f403 ((17/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(35606746486245863/100000000000000),(232812331309343/50000000000000),(160725540959/50000000000000),(-1242470043/20000000000000)⟩
def e404 : ℝ := (9235307/3125000000000)
theorem h404 : Model (fun x => f404 ((17/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(140422826947/50000000000000),(-3672581063/100000000000000),(45490429/100000000000000),(-256359/50000000000000)⟩
def e405 : ℝ := (8137/100000000000000)
theorem h405 : Model (fun x => f405 ((17/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (1757039693233261/5000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(7851615413457/50000000000000),(252051692359/100000000000000),(-38679271/2500000000000),(4815203/50000000000000)⟩
def e406 : ℝ := (572549/50000000000000)
theorem h406 : Model (fun x => f406 ((17/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(34340214603737/100000000000000),(30368896143/5000000000000),(-331148301/12500000000000),(6710993/50000000000000)⟩
def e407 : ℝ := (1930187/100000000000000)
theorem h407 : Model (fun x => f407 ((17/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(217894305381451/100000000000000),(210964153687/5000000000000),(-7567544243/100000000000000),(113619437/100000000000000)⟩
def e408 : ℝ := (13766139/100000000000000)
theorem h408 : Model (fun x => f408 ((17/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(25634624162523/25000000000000),(48700607573/6250000000000),(-6364185241/50000000000000),(203213503/100000000000000)⟩
def e409 : ℝ := (3237481/25000000000000)
theorem h409 : Model (fun x => f409 ((17/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-611882959857/25000000000000),(80969604881/100000000000000),(431453051/100000000000000),(-3648987/20000000000000)⟩
def e410 : ℝ := (90816649/100000000000000)
theorem h410 : Model (fun x => f410 ((17/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(24891197681427/390625000000),(87710723876953/25000000000000),(31501/409600),(1717/2048000)⟩
def e411 : ℝ := (227539063/50000000000000)
theorem h411 : Model (fun x => f411 ((17/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1681/64),(41/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((17/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(68921/512),(5043/2560),(123/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((17/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(857763117700815133/100000000000000),(11956011823654161/20000000000000),(446904314756393/25000000000000),(29906502151489/100000000000000)⟩
def e414 : ℝ := (153812604829/50000000000000)
theorem h414 : Model (fun x => f414 ((17/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(182159849/1562500000000),(-101562087/12500000000000),(16164513/50000000000000),(-966299/100000000000000)⟩
def e415 : ℝ := (4539/12500000000000)
theorem h415 : Model (fun x => f415 ((17/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (796165227196157609/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5720513619043/100000000000000),(206504703/50000000000000),(-727651403/100000000000000),(15891567/100000000000000)⟩
def e416 : ℝ := (34562847/100000000000000)
theorem h416 : Model (fun x => f416 ((17/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(654596355923/20000000000000),(81382614287/100000000000000),(-18512397/6250000000000),(-294171/12500000000000)⟩
def e417 : ℝ := (15672437/12500000000000)
theorem h417 : Model (fun x => f417 ((17/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((17/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((654551533467/400000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (21/10) (43/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (21/10) (43/20) ≤ (3273008426327/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(17/8)-(1/40)) (by norm_num : ((17/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel22


noncomputable section
namespace Hf4Quad.Panel23
open Hf4Quad.Dag

def p0 : Cubic := ⟨(87/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((87/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((87/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((87/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((87/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(381142857142857/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((87/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-381142857142857/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((87/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-144857142857143/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((87/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((87/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(7569/1600),(87/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((87/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(71585119047619/12500000000000),(13165079365079/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((87/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-71585119047619/12500000000000),(-13165079365079/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((87/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-431197619047619/50000000000000),(-17546031746031/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((87/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((87/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(658503/64000),(22707/64000),(261/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((87/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(128310529/1280000),(4424501/1280000),(1986575520833/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((87/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-128310529/1280000),(-4424501/1280000),(-1986575520833/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((87/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-5443327658110119/50000000000000),(-363210172371031/100000000000000),(-4048812417327/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((87/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((87/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(57289761/2560000),(658503/640000),(22707/1280000),(87/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((87/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(3125929419642857/50000000000000),(57488357142857/20000000000000),(2477946428571/50000000000000),(9494047619/25000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((87/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1158699119233631/25000000000000),(-37884193328373/50000000000000),(181416087963/20000000000000),(22753389551/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((87/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((87/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(4867391803710937/100000000000000),(69933790283203/25000000000000),(658503/10240000),(7569/10240000)⟩
def e22 : ℝ := (425781251/100000000000000)
theorem h22 : Model (fun x => f22 ((87/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(6342031246464843/20000000000000),(455605692993163/25000000000000),(41894776367187/100000000000000),(96309830729/20000000000000)⟩
def e23 : ℝ := (554777201/20000000000000)
theorem h23 : Model (fun x => f23 ((87/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(27075359755389691/100000000000000),(873327192657953/50000000000000),(21400928403501/50000000000000),(126075635799/25000000000000)⟩
def e24 : ℝ := (1441506499/50000000000000)
theorem h24 : Model (fun x => f24 ((87/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((87/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(10586577173071287/100000000000000),(730108770556639/100000000000000),(131125856781/625000000000),(5023979187/1562500000000)⟩
def e26 : ℝ := (1392309573/50000000000000)
theorem h26 : Model (fun x => f26 ((87/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(23772187048949493/100000000000000),(102466323486851/6250000000000),(9422190665457/20000000000000),(361003473771/50000000000000)⟩
def e27 : ℝ := (3126434831/50000000000000)
theorem h27 : Model (fun x => f27 ((87/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(3177971675271199/6250000000000),(1693057780552761/50000000000000),(89912810134287/100000000000000),(613154745369/50000000000000)⟩
def e28 : ℝ := (456794133/5000000000000)
theorem h28 : Model (fun x => f28 ((87/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((87/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(23025805351430049/100000000000000),(115790687830467/6250000000000),(63884517423703/100000000000000),(611920664977/50000000000000)⟩
def e30 : ℝ := (7082264411/50000000000000)
theorem h30 : Model (fun x => f30 ((87/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(5464060158791733/100000000000000),(219818512135299/50000000000000),(94749358679/625000000000),(290419490203/100000000000000)⟩
def e31 : ℝ := (420158147/12500000000000)
theorem h31 : Model (fun x => f31 ((87/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(56311606963130917/100000000000000),(95643814634403/2500000000000),(105072707522927/100000000000000),(1516728980941/100000000000000)⟩
def e32 : ℝ := (3124286959/25000000000000)
theorem h32 : Model (fun x => f32 ((87/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((87/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(3247101/320),(37323/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((87/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((87/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(192183/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((87/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(6322029/320),(10999/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((87/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((87/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(7051629/320),(10999/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((87/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-7051629/320),(-10999/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((87/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((87/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(127/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((87/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(16129/1600),(127/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((87/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((87/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(338709/160),(2667/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((87/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(23619094857/50000000000000),(-1487817/200000000000),(109829/1250000000000),(-18449/20000000000000)⟩
def e46 : ℝ := (931/100000000000000)
theorem h46 : Model (fun x => f46 ((87/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (166677/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-260239209761519/25000000000000),(156369579073/100000000000000),(-156467339/12500000000000),(5010823/50000000000000)⟩
def e47 : ℝ := (5110991/12500000000000)
theorem h47 : Model (fun x => f47 ((87/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((87/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(167/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((87/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((87/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((87/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(27833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((87/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(47833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((87/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((87/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(29895833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((87/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((87/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(627812499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((87/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((87/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(4895833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((87/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(245893229166647/50000000000000),(12177083333313/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (119/100000000000000)
theorem h60 : Model (fun x => f60 ((87/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(143001736111107/100000000000000),(62282986111/6250000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((87/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((87/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(29895833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((87/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1338835069444427/100000000000000),(1290798611109/25000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((87/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1438835069444427/100000000000000),(1290798611109/25000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((87/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(3537998014639069/50000000000000),(200600036530333/100000000000000),(232367947047/20000000000000),(2093822337/100000000000000)⟩
def e66 : ℝ := (126987/20000000000000)
theorem h66 : Model (fun x => f66 ((87/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(54895833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((87/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(482168402777771/100000000000000),(457465277777/25000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((87/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(211752290219903/20000000000000),(753388129339/12500000000000),(1429578993/12500000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (63/100000000000000)
theorem h69 : Model (fun x => f69 ((87/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(18729479559832319/25000000000000),(1275176785305677/50000000000000),(25200741763819/100000000000000),(115647635911/100000000000000)⟩
def e70 : ℝ := (140336119/50000000000000)
theorem h70 : Model (fun x => f70 ((87/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((87/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3003036458333247/12500000000000),(1307942708331/781250000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((87/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(4704757118055099/100000000000000),(66443489583221/50000000000000),(754687499993/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1341/100000000000000)
theorem h73 : Model (fun x => f73 ((87/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(3113259670864243/6250000000000),(1690516762078201/100000000000000),(826882194673/5000000000000),(4618176761/6250000000000)⟩
def e74 : ℝ := (16938067/10000000000000)
theorem h74 : Model (fun x => f74 ((87/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(31182518243289291/25000000000000),(848174066537911/20000000000000),(41738385657279/100000000000000),(189538464087/100000000000000)⟩
def e75 : ℝ := (112513227/25000000000000)
theorem h75 : Model (fun x => f75 ((87/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((87/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1001012152777749/12500000000000),(435980902777/781250000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((87/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(3835069444443/100000000000000),(40798611111/25000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((87/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(75103443287/10000000000000),(9587673611/20000000000000),(1019965277/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((87/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(60143567556593/100000000000000),(2129035029133/50000000000000),(109162255997/100000000000000),(298773363/25000000000000)⟩
def e80 : ℝ := (201431/4000000000000)
theorem h80 : Model (fun x => f80 ((87/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(132065250426351/100000000000000),(9600610367761/100000000000000),(64361019759/25000000000000),(3079068771/100000000000000)⟩
def e81 : ℝ := (3211653/20000000000000)
theorem h81 : Model (fun x => f81 ((87/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(24972427644716703/20000000000000),(1062617735764329/25000000000000),(8399165947263/20000000000000),(96308766429/50000000000000)⟩
def e82 : ℝ := (466111173/100000000000000)
theorem h82 : Model (fun x => f82 ((87/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(147077576437/100000000000000),(12517240547/100000000000000),(249679/62500000000),(5666473/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((87/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(7200673013/25000000000000),(122564647/4000000000000),(65193961/50000000000000),(277421/10000000000000)⟩
def e84 : ℝ := (14821/50000000000000)
theorem h84 : Model (fun x => f84 ((87/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(5640527193/100000000000000),(720067301/100000000000000),(9575363/25000000000000),(217313/20000000000000)⟩
def e85 : ℝ := (1749/10000000000000)
theorem h85 : Model (fun x => f85 ((87/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1104603241/100000000000000),(10282211/6250000000000),(10500981/100000000000000),(2979/800000000000)⟩
def e86 : ℝ := (2007/25000000000000)
theorem h86 : Model (fun x => f86 ((87/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(3313809723/100000000000000),(30846633/6250000000000),(31502943/100000000000000),(8937/800000000000)⟩
def e87 : ℝ := (6021/25000000000000)
theorem h87 : Model (fun x => f87 ((87/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-3313809723/100000000000000),(-30846633/6250000000000),(-31502943/100000000000000),(-8937/800000000000)⟩
def e88 : ℝ := (6021/25000000000000)
theorem h88 : Model (fun x => f88 ((87/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(3901941715930431/3125000000000),(1062617612377797/25000000000000),(10498949558343/25000000000000),(192616415733/100000000000000)⟩
def e89 : ℝ := (466135257/100000000000000)
theorem h89 : Model (fun x => f89 ((87/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3003036458333247/10000000000000),(1307942708331/625000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((87/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(232486368637267/10000000000000),(8823012092481/50000000000000),(6278234411/12500000000000),(63536843/100000000000000)⟩
def e91 : ℝ := (1213/4000000000000)
theorem h91 : Model (fun x => f91 ((87/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(698165041083215963/100000000000000),(1016442700753457/10000000000000),(60487060848853/100000000000000),(188522916531/100000000000000)⟩
def e92 : ℝ := (81383823/25000000000000)
theorem h92 : Model (fun x => f92 ((87/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(286465217/2000000000000),(-208529117/100000000000000),(1795001/100000000000000),(-2387/20000000000000)⟩
def e93 : ℝ := (17/20000000000000)
theorem h93 : Model (fun x => f93 ((87/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (687939938166380717/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(3576865857201/20000000000000),(8710801561/2500000000000),(-3035121/500000000000),(56367/4000000000000)⟩
def e94 : ℝ := (334239/100000000000000)
theorem h94 : Model (fun x => f94 ((87/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(27833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((87/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(8362369337979/20000000000000),(-145685876969/100000000000000),(63452037/12500000000000),(-884349/50000000000000)⟩
def e96 : ℝ := (6187/100000000000000)
theorem h96 : Model (fun x => f96 ((87/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (238333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(58188153310103/50000000000000),(145685876967/50000000000000),(-1015232593/100000000000000),(707479/20000000000000)⟩
def e97 : ℝ := (5851/12500000000000)
theorem h97 : Model (fun x => f97 ((87/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1221951219512163/50000000000000),(3059403416307/50000000000000),(-21319884453/100000000000000),(14857059/20000000000000)⟩
def e98 : ℝ := (122871/12500000000000)
theorem h98 : Model (fun x => f98 ((87/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(8188153310103/50000000000000),(145685876967/50000000000000),(-1015232593/100000000000000),(707479/20000000000000)⟩
def e99 : ℝ := (5851/12500000000000)
theorem h99 : Model (fun x => f99 ((87/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(100055239228329/25000000000000),(8122875969427/100000000000000),(-2618557241/25000000000000),(-25624573/100000000000000)⟩
def e100 : ℝ := (980759/50000000000000)
theorem h100 : Model (fun x => f100 ((87/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(67717223712801/50000000000000),(27127014861/4000000000000),(-1514005401/100000000000000),(2317177/100000000000000)⟩
def e101 : ℝ := (28043/20000000000000)
theorem h101 : Model (fun x => f101 ((87/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(58188153310103/5000000000000),(145685876967/5000000000000),(-1015232593/10000000000000),(707479/2000000000000)⟩
def e102 : ℝ := (5851/1250000000000)
theorem h102 : Model (fun x => f102 ((87/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(649598756813831/50000000000000),(718378582173/20000000000000),(-11666331331/100000000000000),(37691127/100000000000000)⟩
def e103 : ℝ := (121659/20000000000000)
theorem h103 : Model (fun x => f103 ((87/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(699598756813831/50000000000000),(718378582173/20000000000000),(-11666331331/100000000000000),(37691127/100000000000000)⟩
def e104 : ℝ := (121659/20000000000000)
theorem h104 : Model (fun x => f104 ((87/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(5599881678147953/100000000000000),(64015293389223/50000000000000),(49259375989/50000000000000),(-1531555311/100000000000000)⟩
def e105 : ℝ := (33364321/100000000000000)
theorem h105 : Model (fun x => f105 ((87/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(108188153310103/50000000000000),(145685876967/50000000000000),(-1015232593/100000000000000),(707479/20000000000000)⟩
def e106 : ℝ := (5851/12500000000000)
theorem h106 : Model (fun x => f106 ((87/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(234093530333007/50000000000000),(1260918879393/100000000000000),(-3544470587/100000000000000),(9391967/100000000000000)⟩
def e107 : ℝ := (233831/100000000000000)
theorem h107 : Model (fun x => f107 ((87/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(126630733742853/12500000000000),(2046247275531/50000000000000),(-8748620727/100000000000000),(13754771/100000000000000)⟩
def e108 : ℝ := (208639/25000000000000)
theorem h108 : Model (fun x => f108 ((87/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(28364685031081371/50000000000000),(763091712083367/50000000000000),(5747772526451/100000000000000),(-21914142819/100000000000000)⟩
def e109 : ℝ := (441002993/100000000000000)
theorem h109 : Model (fun x => f109 ((87/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1422061697968821/6250000000000),(569667312081/500000000000),(-31794113421/12500000000000),(48660717/12500000000000)⟩
def e110 : ℝ := (588903/2500000000000)
theorem h110 : Model (fun x => f110 ((87/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(372609894380611/10000000000000),(4247693546531/5000000000000),(29660287073/50000000000000),(-257297129/25000000000000)⟩
def e111 : ℝ := (22389949/100000000000000)
theorem h111 : Model (fun x => f111 ((87/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(37747091460210983/100000000000000),(1013112077061647/100000000000000),(3751694900657/100000000000000),(-596729443/4000000000000)⟩
def e112 : ℝ := (147633473/50000000000000)
theorem h112 : Model (fun x => f112 ((87/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(3779058460894949/4000000000000),(2539295501228381/100000000000000),(2374866856777/25000000000000),(-18416189447/50000000000000)⟩
def e113 : ℝ := (736269939/100000000000000)
theorem h113 : Model (fun x => f113 ((87/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(474020565989607/6250000000000),(189889104027/500000000000),(-10598037807/12500000000000),(16220239/12500000000000)⟩
def e114 : ℝ := (196301/2500000000000)
theorem h114 : Model (fun x => f114 ((87/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(268183418519/10000000000000),(95431863657/100000000000000),(103291957/20000000000000),(-4757613/100000000000000)⟩
def e115 : ℝ := (46599/100000000000000)
theorem h115 : Model (fun x => f115 ((87/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(109796347303/25000000000000),(5860580477/25000000000000),(167705839/50000000000000),(-37073/25000000000000)⟩
def e116 : ℝ := (12433/50000000000000)
theorem h116 : Model (fun x => f116 ((87/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(16654632541491/50000000000000),(486183967987/25000000000000),(33969248089/100000000000000),(96829579/100000000000000)⟩
def e117 : ℝ := (1121287/50000000000000)
theorem h117 : Model (fun x => f117 ((87/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(7207335754889/10000000000000),(2152500721567/50000000000000),(15765929781/20000000000000),(72481937/25000000000000)⟩
def e118 : ℝ := (2440879/50000000000000)
theorem h118 : Model (fun x => f118 ((87/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(18909706975984523/20000000000000),(508720100534303/20000000000000),(9578297076013/100000000000000),(-18271225573/50000000000000)⟩
def e119 : ℝ := (741151697/100000000000000)
theorem h119 : Model (fun x => f119 ((87/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(4495146623/6250000000000),(2559324343/50000000000000),(29693399/25000000000000),(730551/100000000000000)⟩
def e120 : ℝ := (1477/20000000000000)
theorem h120 : Model (fun x => f120 ((87/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(368069497/3125000000000),(261951751/25000000000000),(6726969/20000000000000),(416287/100000000000000)⟩
def e121 : ℝ := (2377/100000000000000)
theorem h121 : Model (fun x => f121 ((87/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(96441903/5000000000000),(41182101/20000000000000),(4220791/50000000000000),(155953/100000000000000)⟩
def e122 : ℝ := (1317/100000000000000)
theorem h122 : Model (fun x => f122 ((87/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(157936217/50000000000000),(2458789/6250000000000),(981401/50000000000000),(48113/100000000000000)⟩
def e123 : ℝ := (601/100000000000000)
theorem h123 : Model (fun x => f123 ((87/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(473808651/50000000000000),(7376367/6250000000000),(2944203/50000000000000),(144339/100000000000000)⟩
def e124 : ℝ := (1803/100000000000000)
theorem h124 : Model (fun x => f124 ((87/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-473808651/50000000000000),(-7376367/6250000000000),(-2944203/50000000000000),(-144339/100000000000000)⟩
def e125 : ℝ := (1803/100000000000000)
theorem h125 : Model (fun x => f125 ((87/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(94548533932305313/100000000000000),(2543600384649643/100000000000000),(9578291187607/100000000000000),(-7308519097/20000000000000)⟩
def e126 : ℝ := (1482307/200000000000)
theorem h126 : Model (fun x => f126 ((87/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1422061697968821/5000000000000),(569667312081/400000000000),(-31794113421/10000000000000),(48660717/10000000000000)⟩
def e127 : ℝ := (588903/2000000000000)
theorem h127 : Model (fun x => f127 ((87/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1095995618875409/50000000000000),(11806918077629/100000000000000),(-1729034111/10000000000000),(-1441849/100000000000000)⟩
def e128 : ℝ := (2558443/100000000000000)
theorem h128 : Model (fun x => f128 ((87/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(62342935629774117/10000000000000),(809974698142113/12500000000000),(98564200851/2000000000000),(-51907097733/100000000000000)⟩
def e129 : ℝ := (745336933/50000000000000)
theorem h129 : Model (fun x => f129 ((87/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(8020154889/50000000000000),(-166719709/100000000000000),(1606051/100000000000000),(-351/2500000000000)⟩
def e130 : ℝ := (163/100000000000000)
theorem h130 : Model (fun x => f130 ((87/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (616944577104790117/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(15165877733299/100000000000000),(7824073143/3125000000000),(-1185797907/100000000000000),(287323/5000000000000)⟩
def e131 : ℝ := (422711/100000000000000)
theorem h131 : Model (fun x => f131 ((87/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(4131275877413/12500000000000),(74850300377/12500000000000),(-1792822107/100000000000000),(1431127/20000000000000)⟩
def e132 : ℝ := (15139/2000000000000)
theorem h132 : Model (fun x => f132 ((87/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-86009597571583/25000000000000),(-6181594096969/100000000000000),(1199071681/6250000000000),(-10184221/12500000000000)⟩
def e133 : ℝ := (5433437/25000000000000)
theorem h133 : Model (fun x => f133 ((87/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(11494252873563/25000000000000),(-264235698243/50000000000000),(6074383867/100000000000000),(-13964101/20000000000000)⟩
def e134 : ℝ := (81187/10000000000000)
theorem h134 : Model (fun x => f134 ((87/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (43/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-158178570246587/100000000000000),(-511983871449/50000000000000),(20590501367/100000000000000),(-274131631/100000000000000)⟩
def e135 : ℝ := (1180161/6250000000000)
theorem h135 : Model (fun x => f135 ((87/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(57289761/256000),(658503/64000),(22707/128000),(87/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((87/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((87/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(5926527/32000),(204363/32000),(2349/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((87/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(104701977/256000),(1067229/64000),(32103/128000),(21/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((87/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-7569/1600),(-87/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((87/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(103490937/256000),(1060269/64000),(32023/128000),(21/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((87/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((87/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(261/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((87/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-261/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((87/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(100150137/256000),(1050669/64000),(32023/128000),(21/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((87/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(100918137/256000),(1050669/64000),(32023/128000),(21/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((87/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((87/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(100918137/4000),(1050669/1000),(32023/2000),(21/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((87/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((87/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(10827764829/512000),(124457067/128000),(4291623/256000),(16443/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((87/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(4728584413/100000000000000),(-10870309/5000000000000),(780913/12500000000000),(-143617/100000000000000)⟩
def e151 : ℝ := (329/10000000000000)
theorem h151 : Model (fun x => f151 ((87/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (5160643677/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(119299982401799/100000000000000),(-10337592157/2000000000000),(613295729/12500000000000),(-22019531/50000000000000)⟩
def e152 : ℝ := (81552249/50000000000000)
theorem h152 : Model (fun x => f152 ((87/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(207/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((87/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(34569/1600),(187/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((87/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(381/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((87/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(262467191601/5000000000000),(-41333416001/100000000000000),(39729/12207031250),(-2562677/100000000000000)⟩
def e156 : ℝ := (10171/50000000000000)
theorem h156 : Model (fun x => f156 ((87/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (189/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(113415354330687/100000000000000),(41749979331/12500000000000),(26036797/4000000000000),(-1281339/25000000000000)⟩
def e157 : ℝ := (420743/50000000000000)
theorem h157 : Model (fun x => f157 ((87/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(213415354330687/100000000000000),(41749979331/12500000000000),(26036797/4000000000000),(-1281339/25000000000000)⟩
def e158 : ℝ := (420743/50000000000000)
theorem h158 : Model (fun x => f158 ((87/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(106707677165343/100000000000000),(41749979331/25000000000000),(162729981/50000000000000),(-1281339/50000000000000)⟩
def e159 : ℝ := (52593/12500000000000)
theorem h159 : Model (fun x => f159 ((87/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(6707677165343/100000000000000),(41749979331/25000000000000),(162729981/50000000000000),(-1281339/50000000000000)⟩
def e160 : ℝ := (52593/12500000000000)
theorem h160 : Model (fun x => f160 ((87/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((87/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((87/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(196901070959859/50000000000000),(123261843739/20000000000000),(7506889/625000000000),(-9457503/100000000000000)⟩
def e163 : ℝ := (1552749/100000000000000)
theorem h163 : Model (fun x => f163 ((87/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2749516427634003/100000000000000),(123261843739/20000000000000),(7506889/625000000000),(-9457503/100000000000000)⟩
def e164 : ℝ := (6211/400000000000)
theorem h164 : Model (fun x => f164 ((87/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((87/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2933945113207763/100000000000000),(5249339412383/100000000000000),(5629739653/50000000000000),(-15308291/20000000000000)⟩
def e166 : ℝ := (13258269/100000000000000)
theorem h166 : Model (fun x => f166 ((87/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1643265213117743/20000000000000),(5249339412383/100000000000000),(5629739653/50000000000000),(-15308291/20000000000000)⟩
def e167 : ℝ := (1325827/10000000000000)
theorem h167 : Model (fun x => f167 ((87/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((87/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4383725346460167/50000000000000),(9661352945041/50000000000000),(47521972997/100000000000000),(-256345771/100000000000000)⟩
def e169 : ℝ := (9797571/20000000000000)
theorem h169 : Model (fun x => f169 ((87/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14036498311967953/100000000000000),(9661352945041/50000000000000),(47521972997/100000000000000),(-256345771/100000000000000)⟩
def e170 : ℝ := (3061741/6250000000000)
theorem h170 : Model (fun x => f170 ((87/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((87/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(14978021304053583/100000000000000),(5507468899621/12500000000000),(128661678461/100000000000000),(-245500773/50000000000000)⟩
def e172 : ℝ := (112265671/100000000000000)
theorem h172 : Model (fun x => f172 ((87/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(4328433897441967/25000000000000),(5507468899621/12500000000000),(128661678461/100000000000000),(-245500773/50000000000000)⟩
def e173 : ℝ := (14033209/12500000000000)
theorem h173 : Model (fun x => f173 ((87/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((87/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(18475085078390591/100000000000000),(37964530593861/50000000000000),(267220913831/100000000000000),(-152342473/25000000000000)⟩
def e175 : ℝ := (97275809/50000000000000)
theorem h175 : Model (fun x => f175 ((87/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(18877466030771543/100000000000000),(37964530593861/50000000000000),(267220913831/100000000000000),(-152342473/25000000000000)⟩
def e176 : ℝ := (194551619/100000000000000)
theorem h176 : Model (fun x => f176 ((87/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((87/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(20143705509112987/100000000000000),(28136872537781/25000000000000),(473385293227/100000000000000),(-27539733/6250000000000)⟩
def e178 : ℝ := (289776071/100000000000000)
theorem h178 : Model (fun x => f178 ((87/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(20126086461493939/100000000000000),(28136872537781/25000000000000),(473385293227/100000000000000),(-27539733/6250000000000)⟩
def e179 : ℝ := (36222009/12500000000000)
theorem h179 : Model (fun x => f179 ((87/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((87/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(5369019841837189/25000000000000),(153707360199409/100000000000000),(758595019297/100000000000000),(85445563/50000000000000)⟩
def e181 : ℝ := (12404563/3125000000000)
theorem h181 : Model (fun x => f181 ((87/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(21479412700682089/100000000000000),(153707360199409/100000000000000),(758595019297/100000000000000),(85445563/50000000000000)⟩
def e182 : ℝ := (396946017/100000000000000)
theorem h182 : Model (fun x => f182 ((87/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(360192415243359/25000000000000),(46180794953367/100000000000000),(188741078877/50000000000000),(307030903/25000000000000)⟩
def e183 : ℝ := (7469807/6250000000000)
theorem h183 : Model (fun x => f183 ((87/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(11386528366023/10000000000000),(44550433161/12500000000000),(486735627/50000000000000),(-4382113/100000000000000)⟩
def e184 : ℝ := (906861/100000000000000)
theorem h184 : Model (fun x => f184 ((87/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(206707677165343/100000000000000),(41749979331/25000000000000),(162729981/50000000000000),(-1281339/50000000000000)⟩
def e185 : ℝ := (52593/12500000000000)
theorem h185 : Model (fun x => f185 ((87/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(106820159497729/25000000000000),(21575103123/3125000000000),(812195589/50000000000000),(-9507469/100000000000000)⟩
def e186 : ℝ := (1748349/100000000000000)
theorem h186 : Model (fun x => f186 ((87/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(22080547044207/2500000000000),(535168734139/25000000000000),(2950670807/50000000000000),(-25642777/100000000000000)⟩
def e187 : ℝ := (217837/4000000000000)
theorem h187 : Model (fun x => f187 ((87/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1825687436019243/100000000000000),(1474979812339/25000000000000),(9323992573/50000000000000),(-58817447/100000000000000)⟩
def e188 : ℝ := (7535053/50000000000000)
theorem h188 : Model (fun x => f188 ((87/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2078824177772491/100000000000000),(13224773076303/100000000000000),(30016820107/50000000000000),(-23080257/100000000000000)⟩
def e189 : ℝ := (34111629/100000000000000)
theorem h189 : Model (fun x => f189 ((87/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((87/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(106707677165343/12500000000000),(41749979331/3125000000000),(162729981/6250000000000),(-1281339/6250000000000)⟩
def e191 : ℝ := (52593/1562500000000)
theorem h191 : Model (fun x => f191 ((87/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(483763350491487/50000000000000),(42310070097/2500000000000),(71543019/2000000000000),(-24883537/100000000000000)⟩
def e192 : ℝ := (4272813/100000000000000)
theorem h192 : Model (fun x => f192 ((87/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(533763350491487/50000000000000),(42310070097/2500000000000),(71543019/2000000000000),(-24883537/100000000000000)⟩
def e193 : ℝ := (4272813/100000000000000)
theorem h193 : Model (fun x => f193 ((87/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(22192003164211107/100000000000000),(88180031203149/50000000000000),(93905424803/10000000000000),(90676027/12500000000000)⟩
def e194 : ℝ := (455670871/100000000000000)
theorem h194 : Model (fun x => f194 ((87/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(450612769203/100000000000000),(-447628001/12500000000000),(234769/2500000000000),(15543/25000000000000)⟩
def e195 : ℝ := (2547/25000000000000)
theorem h195 : Model (fun x => f195 ((87/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (5503675716619423/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(6492292067149/100000000000000),(156502251519/100000000000000),(18253667/10000000000000),(-1375581/50000000000000)⟩
def e196 : ℝ := (714913/100000000000000)
theorem h196 : Model (fun x => f196 ((87/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(113415354330687/50000000000000),(41749979331/6250000000000),(26036797/2000000000000),(-1281339/12500000000000)⟩
def e197 : ℝ := (420743/25000000000000)
theorem h197 : Model (fun x => f197 ((87/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(46856984734589/100000000000000),(-73332236111/100000000000000),(-28147883/100000000000000),(1393027/100000000000000)⟩
def e198 : ℝ := (47301/25000000000000)
theorem h198 : Model (fun x => f198 ((87/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (26635087201159/12500000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(5314301526541/5000000000000),(146664472221/100000000000000),(28147881/50000000000000),(-1393029/50000000000000)⟩
def e199 : ℝ := (1236743/100000000000000)
theorem h199 : Model (fun x => f199 ((87/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(314301526541/5000000000000),(146664472221/100000000000000),(28147881/50000000000000),(-1393029/50000000000000)⟩
def e200 : ℝ := (1236743/100000000000000)
theorem h200 : Model (fun x => f200 ((87/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(49030758131777/12500000000000),(845721473/156250000000),(207758169/100000000000000),(-10281881/100000000000000)⟩
def e201 : ℝ := (4564173/100000000000000)
theorem h201 : Model (fun x => f201 ((87/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2747960350768501/100000000000000),(845721473/156250000000),(207758169/100000000000000),(-10281881/100000000000000)⟩
def e202 : ℝ := (2282087/50000000000000)
theorem h202 : Model (fun x => f202 ((87/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2920697977392637/100000000000000),(921113433283/20000000000000),(160102613/6250000000000),(-43439279/50000000000000)⟩
def e203 : ℝ := (38879737/100000000000000)
theorem h203 : Model (fun x => f203 ((87/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8203078929773589/100000000000000),(921113433283/20000000000000),(160102613/6250000000000),(-43439279/50000000000000)⟩
def e204 : ℝ := (19439869/50000000000000)
theorem h204 : Model (fun x => f204 ((87/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8718726975766419/100000000000000),(16926076942837/100000000000000),(7047691981/50000000000000),(-6290651/2000000000000)⟩
def e205 : ℝ := (143143189/100000000000000)
theorem h205 : Model (fun x => f205 ((87/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6993887297407019/50000000000000),(16926076942837/100000000000000),(7047691981/50000000000000),(-6290651/2000000000000)⟩
def e206 : ℝ := (14314319/10000000000000)
theorem h206 : Model (fun x => f206 ((87/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(14867050376426331/100000000000000),(481314388651/1250000000000),(11920122453/25000000000000),(-693810091/100000000000000)⟩
def e207 : ℝ := (326479099/100000000000000)
theorem h207 : Model (fun x => f207 ((87/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(2150345582767577/12500000000000),(481314388651/1250000000000),(11920122453/25000000000000),(-693810091/100000000000000)⟩
def e208 : ℝ := (3264791/1000000000000)
theorem h208 : Model (fun x => f208 ((87/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(18284135700947889/100000000000000),(13231188128963/20000000000000),(116835504037/100000000000000),(-11250951/1000000000000)⟩
def e209 : ℝ := (112555349/20000000000000)
theorem h209 : Model (fun x => f209 ((87/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(18686516653328841/100000000000000),(13231188128963/20000000000000),(116835504037/100000000000000),(-11250951/1000000000000)⟩
def e210 : ℝ := (281388373/50000000000000)
theorem h210 : Model (fun x => f210 ((87/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(3972231359060771/20000000000000),(97721004297793/100000000000000),(115863398811/50000000000000),(-376959237/25000000000000)⟩
def e211 : ℝ := (208583507/25000000000000)
theorem h211 : Model (fun x => f211 ((87/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(19843537747684807/100000000000000),(97721004297793/100000000000000),(115863398811/50000000000000),(-376959237/25000000000000)⟩
def e212 : ℝ := (834334029/100000000000000)
theorem h212 : Model (fun x => f212 ((87/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(4218181717779813/20000000000000),(132967196370593/100000000000000),(400786280853/100000000000000),(-880299421/50000000000000)⟩
def e213 : ℝ := (71215039/6250000000000)
theorem h213 : Model (fun x => f213 ((87/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(10547120961116199/50000000000000),(132967196370593/100000000000000),(400786280853/100000000000000),(-880299421/50000000000000)⟩
def e214 : ℝ := (364621/32000000000)
theorem h214 : Model (fun x => f214 ((87/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(16574881093457/1250000000000),(39296117144093/100000000000000),(232084348989/100000000000000),(-557869/1562500000000)⟩
def e215 : ℝ := (341901729/100000000000000)
theorem h215 : Model (fun x => f215 ((87/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(7060450178749/6250000000000),(62353538289/20000000000000),(66954747/20000000000000),(-23029/400000000000)⟩
def e216 : ℝ := (1320373/50000000000000)
theorem h216 : Model (fun x => f216 ((87/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(10314301526541/5000000000000),(146664472221/100000000000000),(28147881/50000000000000),(-1393029/50000000000000)⟩
def e217 : ℝ := (1236743/100000000000000)
theorem h217 : Model (fun x => f217 ((87/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(53192407990203/12500000000000),(605096635887/100000000000000),(447365259/100000000000000),(-5664683/50000000000000)⟩
def e218 : ℝ := (639279/12500000000000)
theorem h218 : Model (fun x => f218 ((87/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(877828055893987/100000000000000),(187234474657/10000000000000),(2049874393/100000000000000),(-34229901/100000000000000)⟩
def e219 : ℝ := (15861011/100000000000000)
theorem h219 : Model (fun x => f219 ((87/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1810836651389573/100000000000000),(5029147989/97656250000),(149376981/2000000000000),(-18201563/20000000000000)⟩
def e220 : ℝ := (21861637/50000000000000)
theorem h220 : Model (fun x => f220 ((87/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(10228257567191/500000000000),(57316211711/500000000000),(1527755807/5000000000000),(-166537581/100000000000000)⟩
def e221 : ℝ := (12255147/12500000000000)
theorem h221 : Model (fun x => f221 ((87/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(5314301526541/625000000000),(146664472221/12500000000000),(28147881/6250000000000),(-1393029/6250000000000)⟩
def e222 : ℝ := (1236743/12500000000000)
theorem h222 : Model (fun x => f222 ((87/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(60203465444159/6250000000000),(1485083469213/100000000000000),(785139831/100000000000000),(-14022857/50000000000000)⟩
def e223 : ℝ := (1253469/10000000000000)
theorem h223 : Model (fun x => f223 ((87/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(66453465444159/6250000000000),(1485083469213/100000000000000),(785139831/100000000000000),(-14022857/50000000000000)⟩
def e224 : ℝ := (1253469/10000000000000)
theorem h224 : Model (fun x => f224 ((87/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(21750501145449117/100000000000000),(152263181082241/100000000000000),(511178878623/100000000000000),(-360133203/20000000000000)⟩
def e225 : ℝ := (81699997/6250000000000)
theorem h225 : Model (fun x => f225 ((87/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(91951904309/20000000000000),(-3218521119/100000000000000),(146573/1250000000000),(31617/100000000000000)⟩
def e226 : ℝ := (28793/100000000000000)
theorem h226 : Model (fun x => f226 ((87/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (10798861838811143/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(3048183760477/50000000000000),(34497589073/25000000000000),(-21120207/50000000000000),(-2606797/100000000000000)⟩
def e227 : ℝ := (1008501/50000000000000)
theorem h227 : Model (fun x => f227 ((87/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(12588659588103/100000000000000),(294492607811/100000000000000),(2192129/1562500000000),(-5357959/100000000000000)⟩
def e228 : ℝ := (546383/20000000000000)
theorem h228 : Model (fun x => f228 ((87/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(15018268673229/100000000000000),(14313070749/5000000000000),(-147430627/20000000000000),(7151/400000000000)⟩
def e229 : ℝ := (6095529/25000000000000)
theorem h229 : Model (fun x => f229 ((87/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(431559444633/6250000000000),(52247189483/100000000000000),(-93946339/10000000000000),(11620383/100000000000000)⟩
def e230 : ℝ := (11719499/100000000000000)
theorem h230 : Model (fun x => f230 ((87/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-151273619132459/100000000000000),(-194344110683/20000000000000),(19651037977/100000000000000),(-16406953/6250000000000)⟩
def e231 : ℝ := (1224083/4000000000000)
theorem h231 : Model (fun x => f231 ((87/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((87/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-7569/320),(-87/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((87/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1827/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((87/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7047/320),(-3/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((87/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((87/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15367/320),(-3/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((87/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((87/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(384175/32),(-75/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((87/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13311/1600),(33/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((87/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(22911/1600),(33/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((87/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((87/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4330179/1600),(6237/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((87/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(36949973661/100000000000000),(-21288449/20000000000000),(191939/10000000000000),(-159/1562500000000)⟩
def e244 : ℝ := (117/100000000000000)
theorem h244 : Model (fun x => f244 ((87/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1079379/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(221800877050229/50000000000000),(-362773011891/25000000000000),(-1331260559/25000000000000),(-48006787/100000000000000)⟩
def e245 : ℝ := (89533/3125000000000)
theorem h245 : Model (fun x => f245 ((87/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(783/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((87/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(70209/1600),(447/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((87/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(103809/1600),(447/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((87/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(27889/1600),(167/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((87/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2895129201/2560000),(14901243/640000),(215147/1280000),(307/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((87/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((87/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(145161/160),(1143/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((87/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(110222442667/100000000000000),(-1735786499/100000000000000),(4100283/20000000000000),(-107619/50000000000000)⟩
def e253 : ℝ := (2167/100000000000000)
theorem h253 : Model (fun x => f253 ((87/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (71433/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(24930329091467/20000000000000),(120662455389/20000000000000),(259437133/20000000000000),(-4961293/100000000000000)⟩
def e254 : ℝ := (993961/20000000000000)
theorem h254 : Model (fun x => f254 ((87/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(44930329091467/20000000000000),(120662455389/20000000000000),(259437133/20000000000000),(-4961293/100000000000000)⟩
def e255 : ℝ := (993961/20000000000000)
theorem h255 : Model (fun x => f255 ((87/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(112325822728667/100000000000000),(37707017309/12500000000000),(10134263/1562500000000),(-2480647/100000000000000)⟩
def e256 : ℝ := (496981/20000000000000)
theorem h256 : Model (fun x => f256 ((87/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(12325822728667/100000000000000),(37707017309/12500000000000),(10134263/1562500000000),(-2480647/100000000000000)⟩
def e257 : ℝ := (496981/20000000000000)
theorem h257 : Model (fun x => f257 ((87/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(207267887177897/50000000000000),(1113254796741/100000000000000),(2393616403/100000000000000),(-9154769/100000000000000)⟩
def e258 : ℝ := (4585243/50000000000000)
theorem h258 : Model (fun x => f258 ((87/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2770250060070079/100000000000000),(1113254796741/100000000000000),(2393616403/100000000000000),(-9154769/100000000000000)⟩
def e259 : ℝ := (9170487/100000000000000)
theorem h259 : Model (fun x => f259 ((87/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(777926542903777/25000000000000),(9607101966731/100000000000000),(12007247033/50000000000000),(-64562313/100000000000000)⟩
def e260 : ℝ := (79234181/100000000000000)
theorem h260 : Model (fun x => f260 ((87/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(419704356199803/5000000000000),(9607101966731/100000000000000),(12007247033/50000000000000),(-64562313/100000000000000)⟩
def e261 : ℝ := (39617091/50000000000000)
theorem h261 : Model (fun x => f261 ((87/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2357181855647419/25000000000000),(18056267701367/50000000000000),(110398338243/100000000000000),(-2919913/2000000000000)⟩
def e262 : ℝ := (298342733/100000000000000)
theorem h262 : Model (fun x => f262 ((87/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(2939555008327459/20000000000000),(18056267701367/50000000000000),(110398338243/100000000000000),(-2919913/2000000000000)⟩
def e263 : ℝ := (149171367/50000000000000)
theorem h263 : Model (fun x => f263 ((87/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(1650939673832777/10000000000000),(42450221565603/50000000000000),(328270236893/100000000000000),(38655949/100000000000000)⟩
def e264 : ℝ := (702767591/100000000000000)
theorem h264 : Model (fun x => f264 ((87/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(3769022204808411/20000000000000),(42450221565603/50000000000000),(328270236893/100000000000000),(38655949/100000000000000)⟩
def e265 : ℝ := (87845949/12500000000000)
theorem h265 : Model (fun x => f265 ((87/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(21167926001885961/100000000000000),(152212555453297/100000000000000),(373533840971/50000000000000),(1745071/156250000000)⟩
def e266 : ℝ := (252412507/20000000000000)
theorem h266 : Model (fun x => f266 ((87/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(21570306954266913/100000000000000),(152212555453297/100000000000000),(373533840971/50000000000000),(1745071/156250000000)⟩
def e267 : ℝ := (157757817/12500000000000)
theorem h267 : Model (fun x => f267 ((87/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(12114512375739591/50000000000000),(236042160224043/100000000000000),(1438211901877/100000000000000),(3960237901/100000000000000)⟩
def e268 : ℝ := (61427811/3125000000000)
theorem h268 : Model (fun x => f268 ((87/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(12105702851930067/50000000000000),(236042160224043/100000000000000),(1438211901877/100000000000000),(3960237901/100000000000000)⟩
def e269 : ℝ := (1965689953/100000000000000)
theorem h269 : Model (fun x => f269 ((87/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(1699728790689769/6250000000000),(84542872493557/25000000000000),(310569057373/12500000000000),(9717177313/100000000000000)⟩
def e270 : ℝ := (2836880733/100000000000000)
theorem h270 : Model (fun x => f270 ((87/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(27198993984369637/100000000000000),(84542872493557/25000000000000),(310569057373/12500000000000),(9717177313/100000000000000)⟩
def e271 : ℝ := (1418440367/50000000000000)
theorem h271 : Model (fun x => f271 ((87/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1676249891247101/50000000000000),(30932463332399/25000000000000),(1502767315123/100000000000000),(10211172071/100000000000000)⟩
def e272 : ℝ := (1079619323/100000000000000)
theorem h272 : Model (fun x => f272 ((87/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(126170904516719/100000000000000),(6776754787/1000000000000),(295879841/12500000000000),(-66391/4000000000000)⟩
def e273 : ℝ := (2804099/50000000000000)
theorem h273 : Model (fun x => f273 ((87/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(212325822728667/100000000000000),(37707017309/12500000000000),(10134263/1562500000000),(-2480647/100000000000000)⟩
def e274 : ℝ := (496981/20000000000000)
theorem h274 : Model (fun x => f274 ((87/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(450822549974053/100000000000000),(320246938911/25000000000000),(458028049/12500000000000),(-6621069/100000000000000)⟩
def e275 : ℝ := (1322251/12500000000000)
theorem h275 : Model (fun x => f275 ((87/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(957212688278763/100000000000000),(4079801686837/100000000000000),(14568275529/100000000000000),(-5879803/100000000000000)⟩
def e276 : ℝ := (54007/160000000000)
theorem h276 : Model (fun x => f276 ((87/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1016204857825537/50000000000000),(115499633297/1000000000000),(49447595983/100000000000000),(3417799/10000000000000)⟩
def e277 : ℝ := (2392093/2500000000000)
theorem h277 : Model (fun x => f277 ((87/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(641077430430659/25000000000000),(5669167094823/20000000000000),(94383836739/50000000000000),(154468897/25000000000000)⟩
def e278 : ℝ := (47443633/20000000000000)
theorem h278 : Model (fun x => f278 ((87/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(112325822728667/12500000000000),(37707017309/1562500000000),(10134263/195312500000),(-2480647/12500000000000)⟩
def e279 : ℝ := (496981/2500000000000)
theorem h279 : Model (fun x => f279 ((87/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(204955497269211/20000000000000),(772731146619/25000000000000),(944472673/12500000000000),(-21504951/100000000000000)⟩
def e280 : ℝ := (12743719/50000000000000)
theorem h280 : Model (fun x => f280 ((87/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(224955497269211/20000000000000),(772731146619/25000000000000),(944472673/12500000000000),(-21504951/100000000000000)⟩
def e281 : ℝ := (12743719/50000000000000)
theorem h281 : Model (fun x => f281 ((87/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(28842778430119383/100000000000000),(199044227695829/50000000000000),(3193118327273/100000000000000),(14374687749/100000000000000)⟩
def e282 : ℝ := (3363647939/100000000000000)
theorem h282 : Model (fun x => f282 ((87/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(346707236413/100000000000000),(-299078651/6250000000000),(13831519/50000000000000),(-24833/100000000000000)⟩
def e283 : ℝ := (20963/50000000000000)
theorem h283 : Model (fun x => f283 ((87/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (7110369779516191/25000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(11623359346637/100000000000000),(67138644277/25000000000000),(216813097/100000000000000),(-3113517/100000000000000)⟩
def e284 : ℝ := (267963/5000000000000)
theorem h284 : Model (fun x => f284 ((87/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(24930329091467/10000000000000),(120662455389/10000000000000),(259437133/10000000000000),(-4961293/50000000000000)⟩
def e285 : ℝ := (993961/10000000000000)
theorem h285 : Model (fun x => f285 ((87/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(44513361919261/100000000000000),(-119542670963/100000000000000),(64007837/100000000000000),(750709/50000000000000)⟩
def e286 : ℝ := (997119/100000000000000)
theorem h286 : Model (fun x => f286 ((87/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (224047026063627/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(4438931046459/4000000000000),(239085341921/100000000000000),(-128015677/100000000000000),(-3002839/100000000000000)⟩
def e287 : ℝ := (278637/4000000000000)
theorem h287 : Model (fun x => f287 ((87/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(438931046459/4000000000000),(239085341921/100000000000000),(-128015677/100000000000000),(-3002839/100000000000000)⟩
def e288 : ℝ := (278637/4000000000000)
theorem h288 : Model (fun x => f288 ((87/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(204772116726531/50000000000000),(882338761851/100000000000000),(-59054851/12500000000000),(-5540953/50000000000000)⟩
def e289 : ℝ := (12853791/50000000000000)
theorem h289 : Model (fun x => f289 ((87/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2765258519167347/100000000000000),(882338761851/100000000000000),(-59054851/12500000000000),(-5540953/50000000000000)⟩
def e290 : ℝ := (25707583/100000000000000)
theorem h290 : Model (fun x => f290 ((87/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1534348986527147/50000000000000),(7590488016419/100000000000000),(-7635557/390625000000),(-304979/312500000000)⟩
def e291 : ℝ := (221329793/100000000000000)
theorem h291 : Model (fun x => f291 ((87/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4175539462717623/50000000000000),(7590488016419/100000000000000),(-7635557/390625000000),(-304979/312500000000)⟩
def e292 : ℝ := (110664897/50000000000000)
theorem h292 : Model (fun x => f292 ((87/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4633732939192997/50000000000000),(28389618831433/100000000000000),(2643928249/50000000000000),(-186731169/50000000000000)⟩
def e293 : ℝ := (82886413/10000000000000)
theorem h293 : Model (fun x => f293 ((87/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14536513497433613/100000000000000),(28389618831433/100000000000000),(2643928249/50000000000000),(-186731169/50000000000000)⟩
def e294 : ℝ := (828864131/100000000000000)
theorem h294 : Model (fun x => f294 ((87/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(16131645267757091/100000000000000),(66259563105727/100000000000000),(55134508681/100000000000000),(-437326081/50000000000000)⟩
def e295 : ℝ := (1938133631/100000000000000)
theorem h295 : Model (fun x => f295 ((87/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(1154209972091961/6250000000000),(66259563105727/100000000000000),(55134508681/100000000000000),(-437326081/50000000000000)⟩
def e296 : ℝ := (15141669/781250000000)
theorem h296 : Model (fun x => f296 ((87/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(10246916958503163/50000000000000),(58841578840451/50000000000000),(195960358229/100000000000000),(-739089667/50000000000000)⟩
def e297 : ℝ := (3450640743/100000000000000)
theorem h297 : Model (fun x => f297 ((87/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(10448107434693639/50000000000000),(58841578840451/50000000000000),(195960358229/100000000000000),(-739089667/50000000000000)⟩
def e298 : ℝ := (431330093/12500000000000)
theorem h298 : Model (fun x => f298 ((87/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(11594607117150173/50000000000000),(176324846033/97656250000),(3688096707/781250000000),(-1950004123/100000000000000)⟩
def e299 : ℝ := (1061738559/20000000000000)
theorem h299 : Model (fun x => f299 ((87/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(11585797593340649/50000000000000),(176324846033/97656250000),(3688096707/781250000000),(-1950004123/100000000000000)⟩
def e300 : ℝ := (1327173199/25000000000000)
theorem h300 : Model (fun x => f300 ((87/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(5142855663506977/20000000000000),(255769508910031/100000000000000),(185179962889/20000000000000),(-1962264543/100000000000000)⟩
def e301 : ℝ := (7541356423/100000000000000)
theorem h301 : Model (fun x => f301 ((87/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(12858805825434109/50000000000000),(255769508910031/100000000000000),(185179962889/20000000000000),(-1962264543/100000000000000)⟩
def e302 : ℝ := (942669553/12500000000000)
theorem h302 : Model (fun x => f302 ((87/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(2822064548585439/100000000000000),(89553334298939/100000000000000),(680186373861/100000000000000),(112335311/12500000000000)⟩
def e303 : ℝ := (33356349/1250000000000)
theorem h303 : Model (fun x => f303 ((87/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(123150680220109/100000000000000),(530641673503/100000000000000),(2299933/800000000000),(-227401/3125000000000)⟩
def e304 : ℝ := (3877041/25000000000000)
theorem h304 : Model (fun x => f304 ((87/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(8438931046459/4000000000000),(239085341921/100000000000000),(-128015677/100000000000000),(-3002839/100000000000000)⟩
def e305 : ℝ := (278637/4000000000000)
theorem h305 : Model (fun x => f305 ((87/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(445097232543059/100000000000000),(201762471469/20000000000000),(31460271/100000000000000),(-1328251/10000000000000)⟩
def e306 : ℝ := (14720007/50000000000000)
theorem h306 : Model (fun x => f306 ((87/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(18780724272003/2000000000000),(3192486720919/100000000000000),(954250501/50000000000000),(-42604321/100000000000000)⟩
def e307 : ℝ := (93318513/100000000000000)
theorem h307 : Model (fun x => f307 ((87/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(990557732087451/50000000000000),(898039176819/10000000000000),(2091416263/20000000000000),(-23521083/20000000000000)⟩
def e308 : ℝ := (262935621/100000000000000)
theorem h308 : Model (fun x => f308 ((87/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2439757170077161/100000000000000),(21572037802081/100000000000000),(66227208977/100000000000000),(-25960851/12500000000000)⟩
def e309 : ℝ := (127016127/20000000000000)
theorem h309 : Model (fun x => f309 ((87/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(4438931046459/500000000000),(239085341921/12500000000000),(-128015677/12500000000000),(-3002839/12500000000000)⟩
def e310 : ℝ := (278637/500000000000)
theorem h310 : Model (fun x => f310 ((87/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1010936889511909/100000000000000),(2443324408871/100000000000000),(-736633791/100000000000000),(-3912443/12500000000000)⟩
def e311 : ℝ := (17808891/25000000000000)
theorem h311 : Model (fun x => f311 ((87/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1110936889511909/100000000000000),(2443324408871/100000000000000),(-736633791/100000000000000),(-3912443/12500000000000)⟩
def e312 : ℝ := (17808891/25000000000000)
theorem h312 : Model (fun x => f312 ((87/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(27104162416898987/100000000000000),(299262908216447/100000000000000),(248969056959/20000000000000),(-201457949/12500000000000)⟩
def e313 : ℝ := (8836590061/100000000000000)
theorem h313 : Model (fun x => f313 ((87/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(184473510861/50000000000000),(-127300741/3125000000000),(28032687/100000000000000),(-100483/100000000000000)⟩
def e314 : ℝ := (6171/5000000000000)
theorem h314 : Model (fun x => f314 ((87/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (6700911053786023/25000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(5205961551539/50000000000000),(215444069129/100000000000000),(-347437971/100000000000000),(-2124061/100000000000000)⟩
def e315 : ℝ := (6806857/50000000000000)
theorem h315 : Model (fun x => f315 ((87/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(4407056489943/20000000000000),(483998646237/100000000000000),(-65312437/50000000000000),(-2618789/50000000000000)⟩
def e316 : ℝ := (9486487/50000000000000)
theorem h316 : Model (fun x => f316 ((87/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(48874449733963/50000000000000),(1827274253243/100000000000000),(-2194027049/25000000000000),(-11538013/20000000000000)⟩
def e317 : ℝ := (21308929/25000000000000)
theorem h317 : Model (fun x => f317 ((87/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(44942022743873/100000000000000),(323551119377/100000000000000),(-7753970659/100000000000000),(6260193/10000000000000)⟩
def e318 : ℝ := (41959717/100000000000000)
theorem h318 : Model (fun x => f318 ((87/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-53165798194293/50000000000000),(-324084717019/50000000000000),(5948533659/50000000000000),(-99954659/50000000000000)⟩
def e319 : ℝ := (566889/781250000000)
theorem h319 : Model (fun x => f319 ((87/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((87/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-83259/1600),(-957/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((87/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((87/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(8439/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((87/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(254301/1600),(983/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((87/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((87/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(427101/1600),(983/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((87/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2135505/32),(4915/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((87/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((87/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1048169447068590383/100000000000000),(1509737320643511/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (33929/25000000000000)
theorem h329 : Model (fun x => f329 ((87/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(381617687/4000000000000),(-2748327/10000000000000),(15487/3125000000000),(-657/25000000000000)⟩
def e330 : ℝ := (33/100000000000000)
theorem h330 : Model (fun x => f330 ((87/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (130638027851423821/12500000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(127335387293271/20000000000000),(219324287993/20000000000000),(8232413943/100000000000000),(6023933/25000000000000)⟩
def e331 : ℝ := (1938013/50000000000000)
theorem h331 : Model (fun x => f331 ((87/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((87/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(447/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((87/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((87/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((87/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(685806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((87/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((87/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((87/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(760643885794813/25000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (531/50000000000000)
theorem h339 : Model (fun x => f339 ((87/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3784193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((87/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((87/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((87/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2132424456820489/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (531/50000000000000)
theorem h343 : Model (fun x => f343 ((87/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4689497894293/100000000000000),(-3098082917/50000000000000),(1023363/12500000000000),(-5409/50000000000000)⟩
def e344 : ℝ := (19/100000000000000)
theorem h344 : Model (fun x => f344 ((87/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1064803457592473/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(4458797375927/3125000000000),(851722891673/100000000000000),(-70335573/6250000000000),(148691/10000000000000)⟩
def e345 : ℝ := (607/20000000000000)
theorem h345 : Model (fun x => f345 ((87/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(7583797375927/3125000000000),(851722891673/100000000000000),(-70335573/6250000000000),(148691/10000000000000)⟩
def e346 : ℝ := (607/20000000000000)
theorem h346 : Model (fun x => f346 ((87/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(7583797375927/6250000000000),(106465361459/25000000000000),(-70335573/12500000000000),(148691/20000000000000)⟩
def e347 : ℝ := (759/50000000000000)
theorem h347 : Model (fun x => f347 ((87/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(1333797375927/6250000000000),(106465361459/25000000000000),(-70335573/12500000000000),(148691/20000000000000)⟩
def e348 : ℝ := (759/50000000000000)
theorem h348 : Model (fun x => f348 ((87/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(44780517838807/10000000000000),(1571631526299/100000000000000),(-103828703/5000000000000),(1371851/50000000000000)⟩
def e349 : ℝ := (1121/20000000000000)
theorem h349 : Model (fun x => f349 ((87/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(560703892820471/20000000000000),(1571631526299/100000000000000),(-103828703/5000000000000),(1371851/50000000000000)⟩
def e350 : ℝ := (2803/50000000000000)
theorem h350 : Model (fun x => f350 ((87/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3401811768835153/100000000000000),(13846138131331/100000000000000),(-5800864899/50000000000000),(6485477/100000000000000)⟩
def e351 : ℝ := (42247/50000000000000)
theorem h351 : Model (fun x => f351 ((87/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(1736838544243221/20000000000000),(13846138131331/100000000000000),(-5800864899/50000000000000),(6485477/100000000000000)⟩
def e352 : ℝ := (16899/20000000000000)
theorem h352 : Model (fun x => f352 ((87/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1317183159424061/12500000000000),(53783637646093/100000000000000),(-3976876529/100000000000000),(-13721197/25000000000000)⟩
def e353 : ℝ := (430889/100000000000000)
theorem h353 : Model (fun x => f353 ((87/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(15806512894440107/100000000000000),(53783637646093/100000000000000),(-3976876529/100000000000000),(-13721197/25000000000000)⟩
def e354 : ℝ := (43089/10000000000000)
theorem h354 : Model (fun x => f354 ((87/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(19179742561825787/100000000000000),(33143829489059/25000000000000),(33819348363/25000000000000),(-268651529/100000000000000)⟩
def e355 : ℝ := (38169/4000000000000)
theorem h355 : Model (fun x => f355 ((87/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(2689432105942509/12500000000000),(33143829489059/25000000000000),(33819348363/25000000000000),(-268651529/100000000000000)⟩
def e356 : ℝ := (477113/50000000000000)
theorem h356 : Model (fun x => f356 ((87/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(32633773036449/125000000000),(10099757254313/4000000000000),(607669621649/100000000000000),(-13436507/4000000000000)⟩
def e357 : ℝ := (482541/20000000000000)
theorem h357 : Model (fun x => f357 ((87/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(3313674922692519/12500000000000),(10099757254313/4000000000000),(607669621649/100000000000000),(-13436507/4000000000000)⟩
def e358 : ℝ := (1206353/50000000000000)
theorem h358 : Model (fun x => f358 ((87/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(16083353077370003/50000000000000),(4192713617397/1000000000000),(207932616029/12500000000000),(478286339/50000000000000)⟩
def e359 : ℝ := (6323159/100000000000000)
theorem h359 : Model (fun x => f359 ((87/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(16074543553560479/50000000000000),(4192713617397/1000000000000),(207932616029/12500000000000),(478286339/50000000000000)⟩
def e360 : ℝ := (158079/2500000000000)
theorem h360 : Model (fun x => f360 ((87/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(7801989198125839/20000000000000),(2017680048911/312500000000),(3623073225629/100000000000000),(765573747/12500000000000)⟩
def e361 : ℝ := (10370211/100000000000000)
theorem h361 : Model (fun x => f361 ((87/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(1219164978873829/3125000000000),(2017680048911/312500000000),(3623073225629/100000000000000),(765573747/12500000000000)⟩
def e362 : ℝ := (2592553/25000000000000)
theorem h362 : Model (fun x => f362 ((87/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(520358095886083/6250000000000),(303930744757589/100000000000000),(825819109619/25000000000000),(2678667251/20000000000000)⟩
def e363 : ℝ := (6681461/50000000000000)
theorem h363 : Model (fun x => f363 ((87/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(7361789777807/5000000000000),(51674350647/5000000000000),(448048231/100000000000000),(-1494143/50000000000000)⟩
def e364 : ℝ := (6603/50000000000000)
theorem h364 : Model (fun x => f364 ((87/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(13833797375927/6250000000000),(106465361459/25000000000000),(-70335573/12500000000000),(148691/20000000000000)⟩
def e365 : ℝ := (759/50000000000000)
theorem h365 : Model (fun x => f365 ((87/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(122479327896451/25000000000000),(471302476153/25000000000000),(-677320937/100000000000000),(-23459/1562500000000)⟩
def e366 : ℝ := (8121/50000000000000)
theorem h366 : Model (fun x => f366 ((87/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(67774168194369/6250000000000),(6259106839559/100000000000000),(1886252837/50000000000000),(-13173077/100000000000000)⟩
def e367 : ℝ := (13731/25000000000000)
theorem h367 : Model (fun x => f367 ((87/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(300023715239327/12500000000000),(18471939364851/100000000000000),(7225884699/25000000000000),(-10062211/25000000000000)⟩
def e368 : ℝ := (169257/100000000000000)
theorem h368 : Model (fun x => f368 ((87/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(3533938431917689/100000000000000),(26001477970197/50000000000000),(244215457253/100000000000000),(125246139/50000000000000)⟩
def e369 : ℝ := (352469/25000000000000)
theorem h369 : Model (fun x => f369 ((87/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(7583797375927/781250000000),(106465361459/3125000000000),(-70335573/1562500000000),(148691/2500000000000)⟩
def e370 : ℝ := (759/6250000000000)
theorem h370 : Model (fun x => f370 ((87/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(279490464918699/25000000000000),(1110094644907/25000000000000),(-4053428441/100000000000000),(1479677/50000000000000)⟩
def e371 : ℝ := (507/2000000000000)
theorem h371 : Model (fun x => f371 ((87/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(304490464918699/25000000000000),(1110094644907/25000000000000),(-4053428441/100000000000000),(1479677/50000000000000)⟩
def e372 : ℝ := (507/2000000000000)
theorem h372 : Model (fun x => f372 ((87/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(43042022245147009/100000000000000),(395148207202801/50000000000000),(1028066715127/20000000000000),(11891670401/100000000000000)⟩
def e373 : ℝ := (10454553/50000000000000)
theorem h373 : Model (fun x => f373 ((87/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(2323310913/1000000000000),(-4265841121/100000000000000),(25289467/50000000000000),(-483419/100000000000000)⟩
def e374 : ℝ := (2127/50000000000000)
theorem h374 : Model (fun x => f374 ((87/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (8449314716917253/20000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(30223841071/156250000000),(350963221999/100000000000000),(-215919849/20000000000000),(3681131/100000000000000)⟩
def e375 : ℝ := (777967/100000000000000)
theorem h375 : Model (fun x => f375 ((87/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(4458797375927/1562500000000),(851722891673/50000000000000),(-70335573/3125000000000),(148691/5000000000000)⟩
def e376 : ℝ := (607/10000000000000)
theorem h376 : Model (fun x => f376 ((87/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(41206269697019/100000000000000),(-144618855839/100000000000000),(698641817/100000000000000),(-1687539/50000000000000)⟩
def e377 : ℝ := (1657/10000000000000)
theorem h377 : Model (fun x => f377 ((87/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (120914333139439/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(117587460605957/100000000000000),(72309427919/25000000000000),(-1397283639/100000000000000),(6750151/100000000000000)⟩
def e378 : ℝ := (25539/20000000000000)
theorem h378 : Model (fun x => f378 ((87/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(17587460605957/100000000000000),(72309427919/25000000000000),(-1397283639/100000000000000),(6750151/100000000000000)⟩
def e379 : ℝ := (25539/20000000000000)
theorem h379 : Model (fun x => f379 ((87/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(433953723664841/100000000000000),(133428111041/12500000000000),(-2578321001/50000000000000),(24911271/100000000000000)⟩
def e380 : ℝ := (235629/50000000000000)
theorem h380 : Model (fun x => f380 ((87/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1394834004689563/50000000000000),(133428111041/12500000000000),(-2578321001/50000000000000),(24911271/100000000000000)⟩
def e381 : ℝ := (471259/100000000000000)
theorem h381 : Model (fun x => f381 ((87/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(102509367861427/3125000000000),(4661964866873/50000000000000),(-2097787187/5000000000000),(187769427/100000000000000)⟩
def e382 : ℝ := (2168003/50000000000000)
theorem h382 : Model (fun x => f382 ((87/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(1070335090493327/12500000000000),(4661964866873/50000000000000),(-2097787187/5000000000000),(187769427/100000000000000)⟩
def e383 : ℝ := (4336007/100000000000000)
theorem h383 : Model (fun x => f383 ((87/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(50343194115423/500000000000),(1786513699333/5000000000000),(-71005654729/50000000000000),(547153601/100000000000000)⟩
def e384 : ℝ := (1782147/10000000000000)
theorem h384 : Model (fun x => f384 ((87/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(15337686442132219/100000000000000),(1786513699333/5000000000000),(-71005654729/50000000000000),(547153601/100000000000000)⟩
def e385 : ℝ := (17821471/100000000000000)
theorem h385 : Model (fun x => f385 ((87/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1803519600300743/10000000000000),(86376695137727/100000000000000),(-34744131121/12500000000000),(153739497/20000000000000)⟩
def e386 : ℝ := (5829359/12500000000000)
theorem h386 : Model (fun x => f386 ((87/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(4074182057744343/20000000000000),(86376695137727/100000000000000),(-34744131121/12500000000000),(153739497/20000000000000)⟩
def e387 : ℝ := (46634873/100000000000000)
theorem h387 : Model (fun x => f387 ((87/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(23953636110825487/100000000000000),(160488517134471/100000000000000),(-361643352101/100000000000000),(268086589/100000000000000)⟩
def e388 : ℝ := (93062863/100000000000000)
theorem h388 : Model (fun x => f388 ((87/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(24356017063206439/100000000000000),(160488517134471/100000000000000),(-361643352101/100000000000000),(268086589/100000000000000)⟩
def e389 : ℝ := (5816429/6250000000000)
theorem h389 : Model (fun x => f389 ((87/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(7159905492344509/25000000000000),(51832231654323/20000000000000),(-15068828063/5000000000000),(-1329184607/100000000000000)⟩
def e390 : ℝ := (157697537/100000000000000)
theorem h390 : Model (fun x => f390 ((87/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(7155500730439747/25000000000000),(51832231654323/20000000000000),(-15068828063/5000000000000),(-1329184607/100000000000000)⟩
def e391 : ℝ := (78848769/50000000000000)
theorem h391 : Model (fun x => f391 ((87/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(33655886410259211/100000000000000),(38752665117531/10000000000000),(-471980549/10000000000000),(-4123837143/100000000000000)⟩
def e392 : ℝ := (24063327/10000000000000)
theorem h392 : Model (fun x => f392 ((87/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(1051850616987267/3125000000000),(38752665117531/10000000000000),(-471980549/10000000000000),(-4123837143/100000000000000)⟩
def e393 : ℝ := (240633271/100000000000000)
theorem h393 : Model (fun x => f393 ((87/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(5919802012676839/100000000000000),(33102250813481/20000000000000),(64972835357/10000000000000),(-1940864013/50000000000000)⟩
def e394 : ℝ := (100851141/100000000000000)
theorem h394 : Model (fun x => f394 ((87/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(69134054458787/50000000000000),(680214560549/100000000000000),(-2449476159/100000000000000),(7791719/100000000000000)⟩
def e395 : ℝ := (359813/100000000000000)
theorem h395 : Model (fun x => f395 ((87/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(217587460605957/100000000000000),(72309427919/25000000000000),(-1397283639/100000000000000),(6750151/100000000000000)⟩
def e396 : ℝ := (25539/20000000000000)
theorem h396 : Model (fun x => f396 ((87/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(29590189383093/6250000000000),(1258689983901/100000000000000),(-5244043437/100000000000000),(21292021/100000000000000)⟩
def e397 : ℝ := (615203/100000000000000)
theorem h397 : Model (fun x => f397 ((87/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(128769083334331/12500000000000),(4108127359307/100000000000000),(-7192558421/50000000000000),(22765833/50000000000000)⟩
def e398 : ℝ := (2167049/100000000000000)
theorem h398 : Model (fun x => f398 ((87/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(448296605556383/20000000000000),(11918359999433/100000000000000),(-4226513943/12500000000000),(34799341/50000000000000)⟩
def e399 : ℝ := (207933/3125000000000)
theorem h399 : Model (fun x => f399 ((87/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3099256194222433/100000000000000),(31726184912411/100000000000000),(-2573192437/12500000000000),(-251049453/100000000000000)⟩
def e400 : ℝ := (19588371/100000000000000)
theorem h400 : Model (fun x => f400 ((87/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(117587460605957/12500000000000),(72309427919/3125000000000),(-1397283639/12500000000000),(6750151/12500000000000)⟩
def e401 : ℝ := (25539/2500000000000)
theorem h401 : Model (fun x => f401 ((87/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(107896779376523/10000000000000),(2994116253957/100000000000000),(-13627745271/100000000000000),(61792927/100000000000000)⟩
def e402 : ℝ := (1381373/100000000000000)
theorem h402 : Model (fun x => f402 ((87/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(117896779376523/10000000000000),(2994116253957/100000000000000),(-13627745271/100000000000000),(61792927/100000000000000)⟩
def e403 : ℝ := (1381373/100000000000000)
theorem h403 : Model (fun x => f403 ((87/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(730784647523129/2000000000000),(58354604471339/12500000000000),(284863238947/100000000000000),(-187018429/3125000000000)⟩
def e404 : ℝ := (289695419/100000000000000)
theorem h404 : Model (fun x => f404 ((87/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(136839218419/50000000000000),(-699320523/20000000000000),(21270041/50000000000000),(-235711/50000000000000)⟩
def e405 : ℝ := (297/4000000000000)
theorem h405 : Model (fun x => f405 ((87/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (9018026100715411/25000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(8100610806099/50000000000000),(15373541309/6250000000000),(-745407903/50000000000000),(4579751/50000000000000)⟩
def e406 : ℝ := (1104329/100000000000000)
theorem h406 : Model (fun x => f406 ((87/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(17772239948819/50000000000000),(596939882943/100000000000000),(-2570415051/100000000000000),(12840633/100000000000000)⟩
def e407 : ℝ := (235287/12500000000000)
theorem h407 : Model (fun x => f407 ((87/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(226303505695181/100000000000000),(1047591736637/25000000000000),(-6892900343/100000000000000),(111272891/100000000000000)⟩
def e408 : ℝ := (13479379/100000000000000)
theorem h408 : Model (fun x => f408 ((87/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(13005948603171/12500000000000),(730656195821/100000000000000),(-11567496663/100000000000000),(184119679/100000000000000)⟩
def e409 : ℝ := (604249/5000000000000)
theorem h409 : Model (fun x => f409 ((87/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1142003781609/50000000000000),(82486761783/100000000000000),(65914131/20000000000000),(-15789639/100000000000000)⟩
def e410 : ℝ := (21161693/25000000000000)
theorem h410 : Model (fun x => f410 ((87/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(7105273092773437/100000000000000),(95656563720703/25000000000000),(840159/10240000),(8961/10240000)⟩
def e411 : ℝ := (464843751/100000000000000)
theorem h411 : Model (fun x => f411 ((87/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(42849/1600),(207/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((87/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(8869743/64000),(128547/64000),(621/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((87/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(196943582117861073/20000000000000),(67299345095621633/100000000000000),(39491004587113/2000000000000),(2026945329277/6250000000000)⟩
def e414 : ℝ := (8192411223/2500000000000)
theorem h414 : Model (fun x => f414 ((87/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(126939907/1250000000000),(-21688883/3125000000000),(27070479/100000000000000),(-396431/50000000000000)⟩
def e415 : ℝ := (7291/25000000000000)
theorem h415 : Model (fun x => f415 ((87/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (91541125644261073/10000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(178704753773/3125000000000),(-92597267/4000000000000),(-319129277/50000000000000),(6975937/50000000000000)⟩
def e416 : ℝ := (993107/3125000000000)
theorem h416 : Model (fun x => f416 ((87/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1717272278759/50000000000000),(20042957527/25000000000000),(-308687899/100000000000000),(-367553/20000000000000)⟩
def e417 : ℝ := (29106549/25000000000000)
theorem h417 : Model (fun x => f417 ((87/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((87/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((10302975706067/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (43/20) (11/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (43/20) (11/5) ≤ (10303674263243/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(87/40)-(1/40)) (by norm_num : ((87/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel23


noncomputable section
namespace Hf4Quad.Panel24
open Hf4Quad.Dag

def p0 : Cubic := ⟨(89/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((89/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((89/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((89/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((89/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(389904761904761/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((89/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-389904761904761/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((89/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-29847619047619/10000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((89/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((89/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(7921/1600),(89/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((89/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(149828439153439/25000000000000),(3366931216931/25000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((89/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-149828439153439/25000000000000),(-3366931216931/25000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((89/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-448894973544973/50000000000000),(-4462169312169/25000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((89/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((89/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(704969/64000),(23763/64000),(267/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((89/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(5365801372974537/50000000000000),(361739418402777/100000000000000),(2032243923611/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((89/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-5365801372974537/50000000000000),(-361739418402777/100000000000000),(-2032243923611/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((89/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-581469634651951/5000000000000),(-379588095651453/100000000000000),(-4140149222883/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((89/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((89/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(62742241/2560000),(704969/640000),(23763/1280000),(89/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((89/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(1711717884424603/25000000000000),(307724563492063/100000000000000),(5186369047619/100000000000000),(38849206349/100000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((89/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-74726893052197/1562500000000),(-7186353215939/10000000000000),(32694369523/3125000000000),(1476650339/6250000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((89/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((89/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(2726591527832031/50000000000000),(76589649658203/25000000000000),(704969/10240000),(7921/10240000)⟩
def e22 : ℝ := (108886719/25000000000000)
theorem h22 : Model (fun x => f22 ((89/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(4440809719867169/12500000000000),(1995869537018949/100000000000000),(22425500415943/50000000000000),(503943829571/100000000000000)⟩
def e23 : ℝ := (1418753621/50000000000000)
theorem h23 : Model (fun x => f23 ((89/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(3842994575449593/12500000000000),(1924006004859559/100000000000000),(22948610328311/50000000000000),(105514046999/20000000000000)⟩
def e24 : ℝ := (589326847/20000000000000)
theorem h24 : Model (fun x => f24 ((89/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((89/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(12133332298852537/100000000000000),(102247182293701/12500000000000),(1148844744873/5000000000000),(344223144531/100000000000000)⟩
def e26 : ℝ := (728454591/25000000000000)
theorem h26 : Model (fun x => f26 ((89/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(27245429775836067/100000000000000),(918385273342787/50000000000000),(25797339138841/50000000000000),(772953981687/100000000000000)⟩
def e27 : ℝ := (204468339/3125000000000)
theorem h27 : Model (fun x => f27 ((89/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(57989386379432811/100000000000000),(3760776551545133/100000000000000),(3046621841697/3125000000000),(650262108341/50000000000000)⟩
def e28 : ℝ := (9489621083/100000000000000)
theorem h28 : Model (fun x => f28 ((89/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((89/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(13498332182473447/50000000000000),(2123333152299191/100000000000000),(17893256901397/25000000000000),(1340318869017/100000000000000)⟩
def e30 : ℝ := (3032333987/20000000000000)
theorem h30 : Model (fun x => f30 ((89/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(400396956603131/6250000000000),(503870327410681/100000000000000),(8492196529393/50000000000000),(79514948777/25000000000000)⟩
def e31 : ℝ := (3597888343/100000000000000)
theorem h31 : Model (fun x => f31 ((89/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(64395737685082907/100000000000000),(2132323439477907/50000000000000),(11447629199309/10000000000000),(161858401179/10000000000000)⟩
def e32 : ℝ := (6543754713/50000000000000)
theorem h32 : Model (fun x => f32 ((89/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((89/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(3398109/320),(38181/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((89/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((89/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(196601/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((89/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1308745/64),(55853/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((89/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((89/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1454665/64),(55853/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((89/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1454665/64),(-55853/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((89/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((89/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(129/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((89/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(16641/1600),(129/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((89/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((89/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(349461/160),(2709/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((89/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(45784794297/100000000000000),(-709841773/100000000000000),(4126987/50000000000000),(-85313/100000000000000)⟩
def e46 : ℝ := (53/6250000000000)
theorem h46 : Model (fun x => f46 ((89/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (172011/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-260162257015803/25000000000000),(75740127913/50000000000000),(-238704439/20000000000000),(9415239/100000000000000)⟩
def e47 : ℝ := (3840153/10000000000000)
theorem h47 : Model (fun x => f47 ((89/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((89/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(169/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((89/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((89/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((89/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(140833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((89/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(240833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((89/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((89/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(24083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((89/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((89/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(505749999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((89/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((89/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(4083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((89/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(129071614583321/25000000000000),(6161458333323/50000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (3/2500000000000)
theorem h60 : Model (fun x => f60 ((89/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(145001736111107/100000000000000),(50173611111/5000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((89/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((89/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(24083333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((89/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1349168402777757/100000000000000),(64626736111/1250000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((89/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1449168402777757/100000000000000),(64626736111/1250000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((89/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(7481860221986301/100000000000000),(102636270796989/50000000000000),(234883572047/20000000000000),(419777199/20000000000000)⟩
def e66 : ℝ := (317487/50000000000000)
theorem h66 : Model (fun x => f66 ((89/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(44083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((89/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(485835069444437/100000000000000),(57400173611/3125000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((89/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(214172293113421/20000000000000),(1518234592011/25000000000000),(11480034721/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (1/1562500000000)
theorem h69 : Model (fun x => f69 ((89/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(40060179012422379/50000000000000),(1326276653692273/50000000000000),(12950691699387/50000000000000),(23580883143/20000000000000)⟩
def e70 : ℝ := (17769121/6250000000000)
theorem h70 : Model (fun x => f70 ((89/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((89/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3045036458333247/12500000000000),(1053645833331/625000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((89/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1243389887152641/25000000000000),(27184062499951/20000000000000),(38098958333/5000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (171/12500000000000)
theorem h73 : Model (fun x => f73 ((89/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(53259932673103777/100000000000000),(219694932065419/12500000000000),(1061566527639/6250000000000),(75251942801/100000000000000)⟩
def e74 : ℝ := (171323469/100000000000000)
theorem h74 : Model (fun x => f74 ((89/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(26676058139589707/20000000000000),(2205056381953949/50000000000000),(21443223920499/50000000000000),(48289089629/25000000000000)⟩
def e75 : ℝ := (91125881/20000000000000)
theorem h75 : Model (fun x => f75 ((89/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((89/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1015012152777749/12500000000000),(351215277777/625000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((89/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(4168402777777/100000000000000),(21267361111/12500000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((89/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(425524450231/50000000000000),(26052517361/50000000000000),(212673611/20000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((89/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(13821199625233/20000000000000),(4709221678663/100000000000000),(58227031669/50000000000000),(1235602711/100000000000000)⟩
def e80 : ℝ := (1276527/25000000000000)
theorem h80 : Model (fun x => f80 ((89/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(7616056876821/5000000000000),(10667851108911/100000000000000),(276305921601/100000000000000),(802174893/25000000000000)⟩
def e81 : ℝ := (821217/5000000000000)
theorem h81 : Model (fun x => f81 ((89/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(26706522367096991/20000000000000),(4420780615016809/100000000000000),(43162753762599/100000000000000),(24545632261/12500000000000)⟩
def e82 : ℝ := (94410749/20000000000000)
theorem h82 : Model (fun x => f82 ((89/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(173755817177/100000000000000),(709207417/5000000000000),(217104311/50000000000000),(14769/250000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((89/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(17737573003/50000000000000),(3619912857/100000000000000),(29550309/20000000000000),(3015337/100000000000000)⟩
def e84 : ℝ := (15449/50000000000000)
theorem h84 : Model (fun x => f84 ((89/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(7242842309/100000000000000),(886878649/100000000000000),(4524891/10000000000000),(615631/50000000000000)⟩
def e85 : ℝ := (4751/25000000000000)
theorem h85 : Model (fun x => f85 ((89/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1478746971/100000000000000),(211249567/100000000000000),(6466823/50000000000000),(439919/100000000000000)⟩
def e86 : ℝ := (2273/25000000000000)
theorem h86 : Model (fun x => f86 ((89/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(4436240913/100000000000000),(633748701/100000000000000),(19400469/50000000000000),(1319757/100000000000000)⟩
def e87 : ℝ := (6819/25000000000000)
theorem h87 : Model (fun x => f87 ((89/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-4436240913/100000000000000),(-633748701/100000000000000),(-19400469/50000000000000),(-1319757/100000000000000)⟩
def e88 : ℝ := (6819/25000000000000)
theorem h88 : Model (fun x => f88 ((89/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(66766303699622021/50000000000000),(1105194995317027/25000000000000),(43162714961661/100000000000000),(196363738331/100000000000000)⟩
def e89 : ℝ := (472081021/100000000000000)
theorem h89 : Model (fun x => f89 ((89/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3045036458333247/10000000000000),(1053645833331/500000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((89/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2360357147020809/100000000000000),(1115480693297/6250000000000),(50607819731/100000000000000),(6377797/10000000000000)⟩
def e91 : ℝ := (30327/100000000000000)
theorem h91 : Model (fun x => f91 ((89/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(359368678368290571/50000000000000),(5204323976856491/50000000000000),(15406506272327/25000000000000),(4778394207/2500000000000)⟩
def e92 : ℝ := (164246313/50000000000000)
theorem h92 : Model (fun x => f92 ((89/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(13913288221/100000000000000),(-10074509/5000000000000),(431249/25000000000000),(-2281/20000000000000)⟩
def e93 : ℝ := (41/50000000000000)
theorem h93 : Model (fun x => f93 ((89/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (354133445646758973/50000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(18578776536473/100000000000000),(173010384701/50000000000000),(-598652469/100000000000000),(172613/12500000000000)⟩
def e94 : ℝ := (336647/100000000000000)
theorem h94 : Model (fun x => f94 ((89/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(140833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((89/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(41522491349481/100000000000000),(-8979777541/6250000000000),(497150313/100000000000000),(-430061/25000000000000)⟩
def e96 : ℝ := (5977/100000000000000)
theorem h96 : Model (fun x => f96 ((89/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (29999999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(29238754325259/25000000000000),(28735288131/10000000000000),(-99430063/10000000000000),(860121/25000000000000)⟩
def e97 : ℝ := (45613/100000000000000)
theorem h97 : Model (fun x => f97 ((89/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(614013840830439/25000000000000),(603441050751/10000000000000),(-2088031323/10000000000000),(18062541/25000000000000)⟩
def e98 : ℝ := (957873/100000000000000)
theorem h98 : Model (fun x => f98 ((89/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(4238754325259/25000000000000),(28735288131/10000000000000),(-99430063/10000000000000),(860121/25000000000000)⟩
def e99 : ℝ := (45613/100000000000000)
theorem h99 : Model (fun x => f99 ((89/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(208212305887113/50000000000000),(8080681198637/100000000000000),(-82974861/781250000000),(-726567/3125000000000)⟩
def e100 : ℝ := (478123/25000000000000)
theorem h100 : Model (fun x => f100 ((89/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(17098095089857/12500000000000),(336073612051/50000000000000),(-375013041/25000000000000),(1166667/50000000000000)⟩
def e101 : ℝ := (68343/50000000000000)
theorem h101 : Model (fun x => f101 ((89/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(29238754325259/2500000000000),(28735288131/1000000000000),(-99430063/1000000000000),(860121/2500000000000)⟩
def e102 : ℝ := (45613/10000000000000)
theorem h102 : Model (fun x => f102 ((89/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(20411483339519/1562500000000),(1772838018601/50000000000000),(-357595577/3125000000000),(18369087/50000000000000)⟩
def e103 : ℝ := (37051/6250000000000)
theorem h103 : Model (fun x => f103 ((89/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(21973983339519/1562500000000),(1772838018601/50000000000000),(-357595577/3125000000000),(18369087/50000000000000)⟩
def e104 : ℝ := (37051/6250000000000)
theorem h104 : Model (fun x => f104 ((89/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(2928162394013603/50000000000000),(128406510252411/100000000000000),(22374823673/25000000000000),(-1475243703/100000000000000)⟩
def e105 : ℝ := (16420793/50000000000000)
theorem h105 : Model (fun x => f105 ((89/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(54238754325259/25000000000000),(28735288131/10000000000000),(-99430063/10000000000000),(860121/25000000000000)⟩
def e106 : ℝ := (45613/100000000000000)
theorem h106 : Model (fun x => f106 ((89/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(14709212353779/3125000000000),(623426493361/50000000000000),(-218040839/6250000000000),(4607151/50000000000000)⟩
def e107 : ℝ := (28489/12500000000000)
theorem h107 : Model (fun x => f107 ((89/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(204239194924719/20000000000000),(507208146199/12500000000000),(-2166515493/25000000000000),(1720357/12500000000000)⟩
def e108 : ℝ := (814669/100000000000000)
theorem h108 : Model (fun x => f108 ((89/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(5980455299621761/10000000000000),(1548912164994217/100000000000000),(5616756701299/100000000000000),(-21755337811/100000000000000)⟩
def e109 : ℝ := (435553379/100000000000000)
theorem h109 : Model (fun x => f109 ((89/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(359059996886997/1562500000000),(7057545853071/6250000000000),(-7875273861/3125000000000),(24500007/6250000000000)⟩
def e110 : ℝ := (1435203/6250000000000)
theorem h110 : Model (fun x => f110 ((89/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1948117906985269/50000000000000),(21294740428649/25000000000000),(13316040091/25000000000000),(-989844611/100000000000000)⟩
def e111 : ℝ := (4404561/20000000000000)
theorem h111 : Model (fun x => f111 ((89/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(7957640658821999/20000000000000),(1027940331804279/100000000000000),(3662558312653/100000000000000),(-591696013/4000000000000)⟩
def e112 : ℝ := (291377993/100000000000000)
theorem h112 : Model (fun x => f112 ((89/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(19918551258065521/20000000000000),(80526640524953/3125000000000),(144989297093/1562500000000),(-4568467267/12500000000000)⟩
def e113 : ℝ := (181732843/25000000000000)
theorem h113 : Model (fun x => f113 ((89/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(119686665628999/1562500000000),(2352515284357/6250000000000),(-2625091287/3125000000000),(8166669/6250000000000)⟩
def e114 : ℝ := (478401/6250000000000)
theorem h114 : Model (fun x => f114 ((89/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(179670382299/6250000000000),(48720730741/50000000000000),(61068637/12500000000000),(-2273817/50000000000000)⟩
def e115 : ℝ := (2273/5000000000000)
theorem h115 : Model (fun x => f115 ((89/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(243705155229/50000000000000),(24781824979/100000000000000),(334251011/100000000000000),(-237149/100000000000000)⟩
def e116 : ℝ := (23831/100000000000000)
theorem h116 : Model (fun x => f116 ((89/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(4666921188153/12500000000000),(2081736992777/100000000000000),(1726097479/5000000000000),(87466837/100000000000000)⟩
def e117 : ℝ := (552991/25000000000000)
theorem h117 : Model (fun x => f117 ((89/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(10125119671183/12500000000000),(2311858556431/50000000000000),(80507807099/100000000000000),(269549301/100000000000000)⟩
def e118 : ℝ := (1210989/25000000000000)
theorem h118 : Model (fun x => f118 ((89/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(99673757247697069/100000000000000),(1290738106955679/50000000000000),(9359822821051/100000000000000),(-7255637767/20000000000000)⟩
def e119 : ℝ := (22867979/3125000000000)
theorem h119 : Model (fun x => f119 ((89/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(16528100493/20000000000000),(5602350283/100000000000000),(123037281/100000000000000),(345317/50000000000000)⟩
def e120 : ℝ := (7511/100000000000000)
theorem h120 : Model (fun x => f120 ((89/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(1401171149/10000000000000),(296837331/25000000000000),(9034453/25000000000000),(417787/100000000000000)⟩
def e121 : ℝ := (1147/50000000000000)
theorem h121 : Model (fun x => f121 ((89/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2375688107/100000000000000),(241578339/100000000000000),(1174967/12500000000000),(32671/20000000000000)⟩
def e122 : ℝ := (129/10000000000000)
theorem h122 : Model (fun x => f122 ((89/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(402798329/100000000000000),(47786257/100000000000000),(2264287/100000000000000),(52387/100000000000000)⟩
def e123 : ℝ := (611/100000000000000)
theorem h123 : Model (fun x => f123 ((89/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(1208394987/100000000000000),(143358771/100000000000000),(6792861/100000000000000),(157161/100000000000000)⟩
def e124 : ℝ := (1833/100000000000000)
theorem h124 : Model (fun x => f124 ((89/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-1208394987/100000000000000),(-143358771/100000000000000),(-6792861/100000000000000),(-157161/100000000000000)⟩
def e125 : ℝ := (1833/100000000000000)
theorem h125 : Model (fun x => f125 ((89/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(49836878019651041/50000000000000),(2581476070552587/100000000000000),(935981602819/10000000000000),(-9069586499/25000000000000)⟩
def e126 : ℝ := (731777161/100000000000000)
theorem h126 : Model (fun x => f126 ((89/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(359059996886997/1250000000000),(7057545853071/5000000000000),(-7875273861/2500000000000),(24500007/5000000000000)⟩
def e127 : ℝ := (1435203/5000000000000)
theorem h127 : Model (fun x => f127 ((89/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2215535903422103/100000000000000),(11737744227609/100000000000000),(-8647698241/50000000000000),(-254279/100000000000000)⟩
def e128 : ℝ := (312903/12500000000000)
theorem h128 : Model (fun x => f128 ((89/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(636408251668616311/100000000000000),(3249446385082919/50000000000000),(2310342409337/50000000000000),(-5060470297/10000000000000)⟩
def e129 : ℝ := (1473632621/100000000000000)
theorem h129 : Model (fun x => f129 ((89/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(7856592033/50000000000000),(-80230181/50000000000000),(1524507/100000000000000),(-6577/50000000000000)⟩
def e130 : ℝ := (151/100000000000000)
theorem h130 : Model (fun x => f130 ((89/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (39369042883456013/6250000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(15661920751951/100000000000000),(122847608413/50000000000000),(-57599367/5000000000000),(5524419/100000000000000)⟩
def e131 : ℝ := (205523/50000000000000)
theorem h131 : Model (fun x => f131 ((89/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(4280087161053/12500000000000),(147928996557/25000000000000),(-1750639809/100000000000000),(6905323/100000000000000)⟩
def e132 : ℝ := (747693/100000000000000)
theorem h132 : Model (fun x => f132 ((89/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-356325483534051/100000000000000),(-381613672733/6250000000000),(748227149/4000000000000),(-78350469/100000000000000)⟩
def e133 : ℝ := (5311543/25000000000000)
theorem h133 : Model (fun x => f133 ((89/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(44943820224719/100000000000000),(-252493372049/50000000000000),(141850209/2500000000000),(-63752903/100000000000000)⟩
def e134 : ℝ := (362233/50000000000000)
theorem h134 : Model (fun x => f134 ((89/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (11/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-32029256946881/20000000000000),(-118098968841/12500000000000),(4755671067/25000000000000),(-6223793/2500000000000)⟩
def e135 : ℝ := (17649261/100000000000000)
theorem h135 : Model (fun x => f135 ((89/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(62742241/256000),(704969/64000),(23763/128000),(89/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((89/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((89/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(6344721/32000),(213867/32000),(2403/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((89/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(113500009/256000),(1132703/64000),(267/1024),(107/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((89/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-7921/1600),(-89/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((89/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(112232649/256000),(1125583/64000),(6659/25600),(107/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((89/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((89/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(267/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((89/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-267/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((89/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(108815049/256000),(1115983/64000),(6659/25600),(107/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((89/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(109583049/256000),(1115983/64000),(6659/25600),(107/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((89/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((89/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(109583049/4000),(1115983/1000),(6659/400),(107/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((89/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((89/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(11858283549/512000),(133239141/128000),(4491207/256000),(16821/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((89/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(4317656917/100000000000000),(-194051997/100000000000000),(2725449/50000000000000),(-122493/100000000000000)⟩
def e151 : ℝ := (2741/100000000000000)
theorem h151 : Model (fun x => f151 ((89/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (5658138549/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(118285502375199/100000000000000),(-248885327373/50000000000000),(2325484707/50000000000000),(-41170933/100000000000000)⟩
def e152 : ℝ := (2950297/2000000000000)
theorem h152 : Model (fun x => f152 ((89/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(209/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((89/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(35321/1600),(189/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((89/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(387/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((89/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(516795865633/10000000000000),(-40061695011/100000000000000),(12422231/4000000000000),(-240741/10000000000000)⟩
def e156 : ℝ := (18811/100000000000000)
theorem h156 : Model (fun x => f156 ((89/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (96/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(28521479328161/25000000000000),(33654327663/10000000000000),(77638943/12500000000000),(-2407419/50000000000000)⟩
def e157 : ℝ := (795881/100000000000000)
theorem h157 : Model (fun x => f157 ((89/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(53521479328161/25000000000000),(33654327663/10000000000000),(77638943/12500000000000),(-2407419/50000000000000)⟩
def e158 : ℝ := (795881/100000000000000)
theorem h158 : Model (fun x => f158 ((89/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(53521479328161/50000000000000),(33654327663/20000000000000),(77638943/25000000000000),(-2407419/100000000000000)⟩
def e159 : ℝ := (397941/100000000000000)
theorem h159 : Model (fun x => f159 ((89/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(3521479328161/50000000000000),(33654327663/20000000000000),(77638943/25000000000000),(-2407419/100000000000000)⟩
def e160 : ℝ := (397941/100000000000000)
theorem h160 : Model (fun x => f160 ((89/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((89/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((89/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(395039490279283/100000000000000),(621002474733/100000000000000),(573049341/50000000000000),(-8884523/100000000000000)⟩
def e163 : ℝ := (293719/20000000000000)
theorem h163 : Model (fun x => f163 ((89/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(85961055499799/3125000000000),(621002474733/100000000000000),(573049341/50000000000000),(-8884523/100000000000000)⟩
def e164 : ℝ := (367149/25000000000000)
theorem h164 : Model (fun x => f164 ((89/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((89/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2944488227174011/100000000000000),(5293477867159/100000000000000),(10814413601/100000000000000),(-17968827/25000000000000)⟩
def e166 : ℝ := (3137439/25000000000000)
theorem h166 : Model (fun x => f166 ((89/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8226869179554963/100000000000000),(5293477867159/100000000000000),(10814413601/100000000000000),(-17968827/25000000000000)⟩
def e167 : ℝ := (12549757/100000000000000)
theorem h167 : Model (fun x => f167 ((89/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((89/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1761256834916143/20000000000000),(19509782875293/100000000000000),(23016253651/50000000000000),(-60088969/25000000000000)⟩
def e169 : ℝ := (46429267/100000000000000)
theorem h169 : Model (fun x => f169 ((89/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(7037665896814167/50000000000000),(19509782875293/100000000000000),(23016253651/50000000000000),(-60088969/25000000000000)⟩
def e170 : ℝ := (11607317/25000000000000)
theorem h170 : Model (fun x => f170 ((89/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((89/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15066651592593723/100000000000000),(11142160056137/25000000000000),(31453936087/25000000000000),(-229043921/50000000000000)⟩
def e172 : ℝ := (13324989/12500000000000)
theorem h172 : Model (fun x => f172 ((89/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(2175295734788501/12500000000000),(11142160056137/25000000000000),(31453936087/25000000000000),(-229043921/50000000000000)⟩
def e173 : ℝ := (106599913/100000000000000)
theorem h173 : Model (fun x => f173 ((89/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((89/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(18628007312339127/100000000000000),(76990837298247/100000000000000),(52743465597/20000000000000),(-559175943/100000000000000)⟩
def e175 : ℝ := (185173943/100000000000000)
theorem h175 : Model (fun x => f175 ((89/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(19030388264720079/100000000000000),(76990837298247/100000000000000),(52743465597/20000000000000),(-559175943/100000000000000)⟩
def e176 : ℝ := (23146743/12500000000000)
theorem h176 : Model (fun x => f176 ((89/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((89/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(20370690642341867/100000000000000),(28609004062267/25000000000000),(117736135707/25000000000000),(-373838699/100000000000000)⟩
def e178 : ℝ := (27654853/10000000000000)
theorem h178 : Model (fun x => f178 ((89/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(20353071594722819/100000000000000),(28609004062267/25000000000000),(117736135707/25000000000000),(-373838699/100000000000000)⟩
def e179 : ℝ := (276548531/100000000000000)
theorem h179 : Model (fun x => f179 ((89/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((89/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(21786530012430763/100000000000000),(9796509036331/6250000000000),(151976794051/20000000000000),(128851017/50000000000000)⟩
def e181 : ℝ := (379876413/100000000000000)
theorem h181 : Model (fun x => f181 ((89/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(85116653694391/390625000000),(9796509036331/6250000000000),(151976794051/20000000000000),(128851017/50000000000000)⟩
def e182 : ℝ := (189938207/50000000000000)
theorem h182 : Model (fun x => f182 ((89/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(767325533355613/50000000000000),(47705585337583/100000000000000),(192471966121/50000000000000),(1259023731/100000000000000)⟩
def e183 : ℝ := (23146003/20000000000000)
theorem h183 : Model (fun x => f183 ((89/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(11458194997899/10000000000000),(360245880463/100000000000000),(189601923/20000000000000),(-4108791/100000000000000)⟩
def e184 : ℝ := (860433/100000000000000)
theorem h184 : Model (fun x => f184 ((89/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(103521479328161/50000000000000),(33654327663/20000000000000),(77638943/25000000000000),(-2407419/100000000000000)⟩
def e185 : ℝ := (397941/100000000000000)
theorem h185 : Model (fun x => f185 ((89/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(214333933645817/50000000000000),(696789157093/100000000000000),(1569121159/100000000000000),(-8923629/100000000000000)⟩
def e186 : ℝ := (331263/20000000000000)
theorem h186 : Model (fun x => f186 ((89/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(177505327049911/20000000000000),(2163979329663/100000000000000),(5752506207/100000000000000),(-23991273/100000000000000)⟩
def e187 : ℝ := (1033537/20000000000000)
theorem h187 : Model (fun x => f187 ((89/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1837561404483581/100000000000000),(5973822438461/100000000000000),(286059183/1562500000000),(-853727/1562500000000)⟩
def e188 : ℝ := (7161663/50000000000000)
theorem h188 : Model (fun x => f188 ((89/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1052756844659301/50000000000000),(13464661498901/100000000000000),(11983625639/20000000000000),(-15521987/100000000000000)⟩
def e189 : ℝ := (16298113/50000000000000)
theorem h189 : Model (fun x => f189 ((89/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((89/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(53521479328161/6250000000000),(33654327663/2500000000000),(77638943/3125000000000),(-2407419/12500000000000)⟩
def e191 : ℝ := (397941/12500000000000)
theorem h191 : Model (fun x => f191 ((89/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(485462809614783/50000000000000),(1706418986983/100000000000000),(3432455791/100000000000000),(-23368143/100000000000000)⟩
def e192 : ℝ := (4043961/100000000000000)
theorem h192 : Model (fun x => f192 ((89/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(535462809614783/50000000000000),(1706418986983/100000000000000),(3432455791/100000000000000),(-23368143/100000000000000)⟩
def e193 : ℝ := (4043961/100000000000000)
theorem h193 : Model (fun x => f193 ((89/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(11274242757649259/50000000000000),(180125394902329/100000000000000),(117964119039/12500000000000),(206593621/25000000000000)⟩
def e194 : ℝ := (218350481/50000000000000)
theorem h194 : Model (fun x => f194 ((89/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(221744382637/50000000000000),(-141709897/4000000000000),(389583/4000000000000),(6777/12500000000000)⟩
def e195 : ℝ := (9451/100000000000000)
theorem h195 : Model (fun x => f195 ((89/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (22367415144368431/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(6806005067021/100000000000000),(157200100231/100000000000000),(166563187/100000000000000),(-515123/20000000000000)⟩
def e196 : ℝ := (686033/100000000000000)
theorem h196 : Model (fun x => f196 ((89/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(28521479328161/12500000000000),(33654327663/5000000000000),(77638943/6250000000000),(-2407419/25000000000000)⟩
def e197 : ℝ := (795881/50000000000000)
theorem h197 : Model (fun x => f197 ((89/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(46710218614689/100000000000000),(-9178563811/12500000000000),(-2008719/10000000000000),(323783/25000000000000)⟩
def e198 : ℝ := (177837/100000000000000)
theorem h198 : Model (fun x => f198 ((89/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (213748747313751/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(53289781385309/50000000000000),(5874280839/4000000000000),(40174379/100000000000000),(-2590267/100000000000000)⟩
def e199 : ℝ := (583609/50000000000000)
theorem h199 : Model (fun x => f199 ((89/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(3289781385309/50000000000000),(5874280839/4000000000000),(40174379/100000000000000),(-2590267/100000000000000)⟩
def e200 : ℝ := (583609/50000000000000)
theorem h200 : Model (fun x => f200 ((89/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(49166167349541/12500000000000),(33873271207/6250000000000),(148262589/100000000000000),(-9559319/100000000000000)⟩
def e201 : ℝ := (538449/12500000000000)
theorem h201 : Model (fun x => f201 ((89/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2749043624510613/100000000000000),(33873271207/6250000000000),(148262589/100000000000000),(-9559319/100000000000000)⟩
def e202 : ℝ := (4307593/100000000000000)
theorem h202 : Model (fun x => f202 ((89/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(9155995860553/312500000000),(922959064367/20000000000000),(411670651/20000000000000),(-80960383/100000000000000)⟩
def e203 : ℝ := (36719031/100000000000000)
theorem h203 : Model (fun x => f203 ((89/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1026537453469739/12500000000000),(922959064367/20000000000000),(411670651/20000000000000),(-80960383/100000000000000)⟩
def e204 : ℝ := (4589879/12500000000000)
theorem h204 : Model (fun x => f204 ((89/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(273519782396171/3125000000000),(4244691815909/25000000000000),(1227017521/10000000000000),(-73532727/25000000000000)⟩
def e205 : ℝ := (33833987/25000000000000)
theorem h205 : Model (fun x => f205 ((89/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14021680655725091/100000000000000),(4244691815909/25000000000000),(1227017521/10000000000000),(-73532727/25000000000000)⟩
def e206 : ℝ := (135335949/100000000000000)
theorem h206 : Model (fun x => f206 ((89/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3736061483991031/25000000000000),(38687718415049/100000000000000),(2182256701/5000000000000),(-26073667/4000000000000)⟩
def e207 : ℝ := (77292111/25000000000000)
theorem h207 : Model (fun x => f207 ((89/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(17279960221678409/100000000000000),(38687718415049/100000000000000),(2182256701/5000000000000),(-26073667/4000000000000)⟩
def e208 : ℝ := (61833689/20000000000000)
theorem h208 : Model (fun x => f208 ((89/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(18416906051201561/100000000000000),(66610035939909/100000000000000),(110274540467/100000000000000),(-1062688621/100000000000000)⟩
def e209 : ℝ := (534054709/100000000000000)
theorem h209 : Model (fun x => f209 ((89/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(18819287003582513/100000000000000),(66610035939909/100000000000000),(110274540467/100000000000000),(-1062688621/100000000000000)⟩
def e210 : ℝ := (53405471/10000000000000)
theorem h210 : Model (fun x => f210 ((89/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(20057513804965979/100000000000000),(98630129328303/100000000000000),(111456084607/50000000000000),(-715686297/50000000000000)⟩
def e211 : ℝ := (396831809/50000000000000)
theorem h211 : Model (fun x => f211 ((89/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(20039894757346931/100000000000000),(98630129328303/100000000000000),(111456084607/50000000000000),(-715686297/50000000000000)⟩
def e212 : ℝ := (793663619/100000000000000)
theorem h212 : Model (fun x => f212 ((89/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(10679216106036179/50000000000000),(26909910609073/20000000000000),(390474988297/100000000000000),(-83882561/5000000000000)⟩
def e213 : ℝ := (1086685909/100000000000000)
theorem h213 : Model (fun x => f213 ((89/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(21361765545405691/100000000000000),(26909910609073/20000000000000),(390474988297/100000000000000),(-83882561/5000000000000)⟩
def e214 : ℝ := (108668591/10000000000000)
theorem h214 : Model (fun x => f214 ((89/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(175688846621527/12500000000000),(10056006201963/25000000000000),(231868968947/100000000000000),(-1131703/3125000000000)⟩
def e215 : ℝ := (164905937/50000000000000)
theorem h215 : Model (fun x => f215 ((89/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(113592032003761/100000000000000),(156519570853/50000000000000),(301305201/100000000000000),(-5403393/100000000000000)⟩
def e216 : ℝ := (156191/6250000000000)
theorem h216 : Model (fun x => f216 ((89/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(103289781385309/50000000000000),(5874280839/4000000000000),(40174379/100000000000000),(-2590267/100000000000000)⟩
def e217 : ℝ := (583609/50000000000000)
theorem h217 : Model (fun x => f217 ((89/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(426751157544997/100000000000000),(75844147957/12500000000000),(381653959/100000000000000),(-10583927/100000000000000)⟩
def e218 : ℝ := (1208373/25000000000000)
theorem h218 : Model (fun x => f218 ((89/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(176316135075001/20000000000000),(47003552771/2500000000000),(1850923357/100000000000000),(-1605699/5000000000000)⟩
def e219 : ℝ := (7505717/50000000000000)
theorem h219 : Model (fun x => f219 ((89/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(910582752329973/50000000000000),(2589326234693/50000000000000),(6938919633/100000000000000),(-85702667/100000000000000)⟩
def e220 : ℝ := (20719863/50000000000000)
theorem h220 : Model (fun x => f220 ((89/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2068698902894781/100000000000000),(11583497435221/100000000000000),(7395133859/25000000000000),(-158431047/100000000000000)⟩
def e221 : ℝ := (18674291/20000000000000)
theorem h221 : Model (fun x => f221 ((89/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(53289781385309/6250000000000),(5874280839/500000000000),(40174379/12500000000000),(-2590267/12500000000000)⟩
def e222 : ℝ := (583609/6250000000000)
theorem h222 : Model (fun x => f222 ((89/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(193245706833741/20000000000000),(743947654753/50000000000000),(622700233/100000000000000),(-26125529/100000000000000)⟩
def e223 : ℝ := (3699/31250000000)
theorem h223 : Model (fun x => f223 ((89/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(213245706833741/20000000000000),(743947654753/50000000000000),(622700233/100000000000000),(-26125529/100000000000000)⟩
def e224 : ℝ := (3699/31250000000)
theorem h224 : Model (fun x => f224 ((89/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(4411411597739821/20000000000000),(154286628852999/100000000000000),(250314108641/50000000000000),(-858718849/50000000000000)⟩
def e225 : ℝ := (1248393469/100000000000000)
theorem h225 : Model (fun x => f225 ((89/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(453369620061/100000000000000),(-792817319/25000000000000),(11892557/100000000000000),(24091/100000000000000)⟩
def e226 : ℝ := (6679/25000000000000)
theorem h226 : Model (fun x => f226 ((89/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (21902267765797657/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(318607942567/5000000000000),(13779097713/10000000000000),(-57237507/100000000000000),(-2395109/100000000000000)⟩
def e227 : ℝ := (965269/50000000000000)
theorem h227 : Model (fun x => f227 ((89/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(13178163918361/100000000000000),(294991077361/100000000000000),(1366571/1250000000000),(-1242681/25000000000000)⟩
def e228 : ℝ := (2616571/100000000000000)
theorem h228 : Model (fun x => f228 ((89/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(779392869733/5000000000000),(141667322499/50000000000000),(-145230043/20000000000000),(935267/50000000000000)⟩
def e229 : ℝ := (23075153/100000000000000)
theorem h229 : Model (fun x => f229 ((89/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7005778604341/100000000000000),(972495999/2000000000000),(-174541143/20000000000000),(10646371/100000000000000)⟩
def e230 : ℝ := (2708887/25000000000000)
theorem h230 : Model (fun x => f230 ((89/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-9571281633129/6250000000000),(-448083475389/50000000000000),(18149978553/100000000000000),(-238305349/100000000000000)⟩
def e231 : ℝ := (28484809/100000000000000)
theorem h231 : Model (fun x => f231 ((89/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((89/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-7921/320),(-89/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((89/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1869/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((89/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7031/320),(-1/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((89/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((89/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15351/320),(-1/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((89/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((89/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(383775/32),(-125/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((89/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13439/1600),(31/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((89/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23039/1600),(31/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((89/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((89/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4354371/1600),(5859/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((89/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(459308589/1250000000000),(-3955329/4000000000000),(930497/50000000000000),(-9301/100000000000000)⟩
def e244 : ℝ := (109/100000000000000)
theorem h244 : Model (fun x => f244 ((89/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (67851/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(440677884358687/100000000000000),(-29459425909/2000000000000),(-1403854683/25000000000000),(-48833099/100000000000000)⟩
def e245 : ℝ := (2696677/100000000000000)
theorem h245 : Model (fun x => f245 ((89/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(801/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((89/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(72001/1600),(449/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((89/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(105601/1600),(449/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((89/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(28561/1600),(169/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((89/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3016070161/2560000),(15335229/640000),(218843/1280000),(309/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((89/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((89/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(149769/160),(1161/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((89/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(53415593347/50000000000000),(-1656297469/100000000000000),(2407409/12500000000000),(-199063/100000000000000)⟩
def e253 : ℝ := (79/4000000000000)
theorem h253 : Model (fun x => f253 ((89/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (73719/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(12586341970781/10000000000000),(19013836367/3125000000000),(79273107/6250000000000),(-4649007/100000000000000)⟩
def e254 : ℝ := (2359221/50000000000000)
theorem h254 : Model (fun x => f254 ((89/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(22586341970781/10000000000000),(19013836367/3125000000000),(79273107/6250000000000),(-4649007/100000000000000)⟩
def e255 : ℝ := (2359221/50000000000000)
theorem h255 : Model (fun x => f255 ((89/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(22586341970781/20000000000000),(19013836367/6250000000000),(79273107/12500000000000),(-290563/12500000000000)⟩
def e256 : ℝ := (1179611/50000000000000)
theorem h256 : Model (fun x => f256 ((89/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(2586341970781/20000000000000),(19013836367/6250000000000),(79273107/12500000000000),(-290563/12500000000000)⟩
def e257 : ℝ := (1179611/50000000000000)
theorem h257 : Model (fun x => f257 ((89/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(416771786365601/100000000000000),(35085055201/3125000000000),(2340444111/100000000000000),(-8578527/100000000000000)⟩
def e258 : ℝ := (1741331/20000000000000)
theorem h258 : Model (fun x => f258 ((89/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1386243036039943/50000000000000),(35085055201/3125000000000),(2340444111/100000000000000),(-8578527/100000000000000)⟩
def e259 : ℝ := (272083/3125000000000)
theorem h259 : Model (fun x => f259 ((89/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(48922123854081/1562500000000),(9702404328423/100000000000000),(5910337507/25000000000000),(-11978833/20000000000000)⟩
def e260 : ℝ := (18833057/25000000000000)
theorem h260 : Model (fun x => f260 ((89/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(1051674609880267/12500000000000),(9702404328423/100000000000000),(5910337507/25000000000000),(-11978833/20000000000000)⟩
def e261 : ℝ := (75332229/100000000000000)
theorem h261 : Model (fun x => f261 ((89/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(9501392952297363/100000000000000),(1462097734113/4000000000000),(109571858223/100000000000000),(-129756031/100000000000000)⟩
def e262 : ℝ := (5685651/2000000000000)
theorem h262 : Model (fun x => f262 ((89/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7385220285672491/50000000000000),(1462097734113/4000000000000),(109571858223/100000000000000),(-129756031/100000000000000)⟩
def e263 : ℝ := (284282551/100000000000000)
theorem h263 : Model (fun x => f263 ((89/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(16680511090174783/100000000000000),(86214137686453/100000000000000),(328613618553/100000000000000),(15055179/20000000000000)⟩
def e264 : ℝ := (67179713/10000000000000)
theorem h264 : Model (fun x => f264 ((89/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(4754056343972267/25000000000000),(86214137686453/100000000000000),(328613618553/100000000000000),(15055179/20000000000000)⟩
def e265 : ℝ := (671797131/100000000000000)
theorem h265 : Model (fun x => f265 ((89/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(21475348466663697/100000000000000),(77607261721767/50000000000000),(942486051/125000000000),(297361833/25000000000000)⟩
def e266 : ℝ := (1211712877/100000000000000)
theorem h266 : Model (fun x => f266 ((89/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(21877729419044649/100000000000000),(77607261721767/50000000000000),(942486051/125000000000),(297361833/25000000000000)⟩
def e267 : ℝ := (605856439/50000000000000)
theorem h267 : Model (fun x => f267 ((89/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(12353446955068959/50000000000000),(241843146027207/100000000000000),(1462433504921/100000000000000),(4112856787/100000000000000)⟩
def e268 : ℝ := (1896728261/100000000000000)
theorem h268 : Model (fun x => f268 ((89/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(2468927486251887/10000000000000),(241843146027207/100000000000000),(1462433504921/100000000000000),(4112856787/100000000000000)⟩
def e269 : ℝ := (948364131/50000000000000)
theorem h269 : Model (fun x => f269 ((89/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(1742626265798307/6250000000000),(87056913283483/25000000000000),(317983170703/12500000000000),(628349021/6250000000000)⟩
def e270 : ℝ := (1376089063/50000000000000)
theorem h270 : Model (fun x => f270 ((89/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(5577070717221249/20000000000000),(87056913283483/25000000000000),(317983170703/12500000000000),(628349021/6250000000000)⟩
def e271 : ℝ := (2752178127/100000000000000)
theorem h271 : Model (fun x => f271 ((89/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(56344578398293/1562500000000),(4058281179809/3125000000000),(782596478033/50000000000000),(2119858721/20000000000000)⟩
def e272 : ℝ := (534537679/50000000000000)
theorem h272 : Model (fun x => f272 ((89/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(25507142181053/20000000000000),(343562408289/50000000000000),(1178949047/50000000000000),(-1391553/100000000000000)⟩
def e273 : ℝ := (2676579/50000000000000)
theorem h273 : Model (fun x => f273 ((89/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(42586341970781/20000000000000),(19013836367/6250000000000),(79273107/12500000000000),(-290563/12500000000000)⟩
def e274 : ℝ := (1179611/50000000000000)
theorem h274 : Model (fun x => f274 ((89/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(18135965224523/4000000000000),(647783790161/50000000000000),(1813133903/50000000000000),(-6040561/100000000000000)⟩
def e275 : ℝ := (5035801/50000000000000)
theorem h275 : Model (fun x => f275 ((89/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(24135763031929/2500000000000),(4138011301639/100000000000000),(7269128131/50000000000000),(-129793/3125000000000)⟩
def e276 : ℝ := (16114651/50000000000000)
theorem h276 : Model (fun x => f276 ((89/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(513926929101731/25000000000000),(11748184291371/100000000000000),(24833943483/50000000000000),(39185799/100000000000000)⟩
def e277 : ℝ := (91616267/100000000000000)
theorem h277 : Model (fun x => f277 ((89/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2621761450253959/100000000000000),(29108408230201/100000000000000),(4813511889/2500000000000),(127932043/20000000000000)⟩
def e278 : ℝ := (229429111/100000000000000)
theorem h278 : Model (fun x => f278 ((89/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(22586341970781/2500000000000),(19013836367/781250000000),(79273107/1562500000000),(-290563/1562500000000)⟩
def e279 : ℝ := (1179611/6250000000000)
theorem h279 : Model (fun x => f279 ((89/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(206197877947301/20000000000000),(1560447935777/50000000000000),(3715688471/50000000000000),(-3997517/20000000000000)⟩
def e280 : ℝ := (12113467/50000000000000)
theorem h280 : Model (fun x => f280 ((89/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(226197877947301/20000000000000),(1560447935777/50000000000000),(3715688471/50000000000000),(-3997517/20000000000000)⟩
def e281 : ℝ := (12113467/50000000000000)
theorem h281 : Model (fun x => f281 ((89/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(14825921913287097/50000000000000),(41103545346773/10000000000000),(3280888436151/100000000000000),(14882605653/100000000000000)⟩
def e282 : ℝ := (1636365121/50000000000000)
theorem h282 : Model (fun x => f282 ((89/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(337247155977/100000000000000),(-467493821/10000000000000),(1718053/6250000000000),(-33053/100000000000000)⟩
def e283 : ℝ := (3853/10000000000000)
theorem h283 : Model (fun x => f283 ((89/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (14618754664667209/50000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1216131124451/10000000000000),(269385261147/100000000000000),(198722761/100000000000000),(-583901/20000000000000)⟩
def e284 : ℝ := (5206339/100000000000000)
theorem h284 : Model (fun x => f284 ((89/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(12586341970781/5000000000000),(19013836367/1562500000000),(79273107/3125000000000),(-4649007/50000000000000)⟩
def e285 : ℝ := (2359221/25000000000000)
theorem h285 : Model (fun x => f285 ((89/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(11068636095363/25000000000000),(-119269097147/100000000000000),(72663063/100000000000000),(10823/781250000000)⟩
def e286 : ℝ := (936551/100000000000000)
theorem h286 : Model (fun x => f286 ((89/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (45050739841381/20000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(22290182247419/20000000000000),(238538194291/100000000000000),(-9082883/6250000000000),(-2770691/100000000000000)⟩
def e287 : ℝ := (205881/3125000000000)
theorem h287 : Model (fun x => f287 ((89/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(2290182247419/20000000000000),(238538194291/100000000000000),(-9082883/6250000000000),(-2770691/100000000000000)⟩
def e288 : ℝ := (205881/3125000000000)
theorem h288 : Model (fun x => f288 ((89/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(205653467163687/50000000000000),(17606390531/2000000000000),(-67040327/12500000000000),(-1022517/10000000000000)⟩
def e289 : ℝ := (759799/3125000000000)
theorem h289 : Model (fun x => f289 ((89/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2767021220041659/100000000000000),(17606390531/2000000000000),(-67040327/12500000000000),(-1022517/10000000000000)⟩
def e290 : ℝ := (24313569/100000000000000)
theorem h290 : Model (fun x => f290 ((89/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(770967590965053/25000000000000),(3790763294037/50000000000000),(-2519042941/100000000000000),(-45310161/50000000000000)⟩
def e291 : ℝ := (52389617/25000000000000)
theorem h291 : Model (fun x => f291 ((89/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(2091562829060291/25000000000000),(3790763294037/50000000000000),(-2519042941/100000000000000),(-45310161/50000000000000)⟩
def e292 : ℝ := (209558469/100000000000000)
theorem h292 : Model (fun x => f292 ((89/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9324263328336231/100000000000000),(28406385287699/100000000000000),(1559495607/50000000000000),(-174913483/50000000000000)⟩
def e293 : ℝ := (98270269/12500000000000)
theorem h293 : Model (fun x => f293 ((89/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(291866218947677/2000000000000),(28406385287699/100000000000000),(1559495607/50000000000000),(-174913483/50000000000000)⟩
def e294 : ℝ := (786162153/100000000000000)
theorem h294 : Model (fun x => f294 ((89/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8132189015261021/50000000000000),(3323489783691/5000000000000),(50028328911/100000000000000),(-828062809/100000000000000)⟩
def e295 : ℝ := (1842994927/100000000000000)
theorem h295 : Model (fun x => f295 ((89/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(18600092316236327/100000000000000),(3323489783691/5000000000000),(50028328911/100000000000000),(-828062809/100000000000000)⟩
def e296 : ℝ := (115187183/6250000000000)
theorem h296 : Model (fun x => f296 ((89/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(5182493094346569/25000000000000),(29612379330879/25000000000000),(187282084829/100000000000000),(-707747969/50000000000000)⟩
def e297 : ℝ := (102878621/3125000000000)
theorem h297 : Model (fun x => f297 ((89/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(5283088332441807/25000000000000),(29612379330879/25000000000000),(187282084829/100000000000000),(-707747969/50000000000000)⟩
def e298 : ℝ := (3292115873/100000000000000)
theorem h298 : Model (fun x => f298 ((89/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(11776100175934081/50000000000000),(9121090022851/5000000000000),(230282049523/50000000000000),(-118030883/6250000000000)⟩
def e299 : ℝ := (5083941023/100000000000000)
theorem h299 : Model (fun x => f299 ((89/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(11767290652124557/50000000000000),(9121090022851/5000000000000),(230282049523/50000000000000),(-118030883/6250000000000)⟩
def e300 : ℝ := (158873157/3125000000000)
theorem h300 : Model (fun x => f300 ((89/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(13114752659710317/50000000000000),(259449724181567/100000000000000),(91424665827/10000000000000),(-384659939/20000000000000)⟩
def e301 : ℝ := (7251024287/100000000000000)
theorem h301 : Model (fun x => f301 ((89/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(26232838652753967/100000000000000),(259449724181567/100000000000000),(91424665827/10000000000000),(-384659939/20000000000000)⟩
def e302 : ℝ := (226594509/3125000000000)
theorem h302 : Model (fun x => f302 ((89/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(750974767274301/25000000000000),(92284697254469/100000000000000),(685453091803/100000000000000),(856712991/100000000000000)⟩
def e303 : ℝ := (1303083401/50000000000000)
theorem h303 : Model (fun x => f303 ((89/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(31053264038947/25000000000000),(531705982371/100000000000000),(245070113/100000000000000),(-3434619/50000000000000)⟩
def e304 : ℝ := (14729669/100000000000000)
theorem h304 : Model (fun x => f304 ((89/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(42290182247419/20000000000000),(238538194291/100000000000000),(-9082883/6250000000000),(-2770691/100000000000000)⟩
def e305 : ℝ := (205881/3125000000000)
theorem h305 : Model (fun x => f305 ((89/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(223557439314989/50000000000000),(1008782370953/100000000000000),(-45582143/100000000000000),(-620531/5000000000000)⟩
def e306 : ℝ := (27906053/100000000000000)
theorem h306 : Model (fun x => f306 ((89/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(945428485139719/100000000000000),(3199619273669/100000000000000),(830086327/50000000000000),(-2512831/6250000000000)⟩
def e307 : ℝ := (44327487/50000000000000)
theorem h307 : Model (fun x => f307 ((89/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1999117146922999/100000000000000),(1804166429411/20000000000000),(4884404817/50000000000000),(-3496847/3125000000000)⟩
def e308 : ℝ := (250357901/100000000000000)
theorem h308 : Model (fun x => f308 ((89/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2483164504327451/100000000000000),(10917238382667/50000000000000),(8124709979/12500000000000),(-202268703/100000000000000)⟩
def e309 : ℝ := (609294221/100000000000000)
theorem h309 : Model (fun x => f309 ((89/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(22290182247419/2500000000000),(238538194291/12500000000000),(-9082883/781250000000),(-2770691/12500000000000)⟩
def e310 : ℝ := (205881/390625000000)
theorem h310 : Model (fun x => f310 ((89/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(253955086513137/25000000000000),(2440011536699/100000000000000),(-917538911/100000000000000),(-14517383/50000000000000)⟩
def e311 : ℝ := (13487041/20000000000000)
theorem h311 : Model (fun x => f311 ((89/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(278955086513137/25000000000000),(2440011536699/100000000000000),(-917538911/100000000000000),(-14517383/50000000000000)⟩
def e312 : ℝ := (13487041/20000000000000)
theorem h312 : Model (fun x => f312 ((89/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(13853827382620301/50000000000000),(304223034582517/100000000000000),(154404635941/12500000000000),(-1592325279/100000000000000)⟩
def e313 : ℝ := (8514685503/100000000000000)
theorem h313 : Model (fun x => f313 ((89/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(180455547117/50000000000000),(-3962712443/100000000000000),(13709887/50000000000000),(-5183/5000000000000)⟩
def e314 : ℝ := (11371/10000000000000)
theorem h314 : Model (fun x => f314 ((89/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (1096087455462391/4000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(10841404999963/100000000000000),(42805965697/20000000000000),(-1404057/390625000000),(-37603/2000000000000)⟩
def e315 : ℝ := (13090209/100000000000000)
theorem h315 : Model (fun x => f315 ((89/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(23002716244473/100000000000000),(15106721551/3125000000000),(-160715831/100000000000000),(-959931/20000000000000)⟩
def e316 : ℝ := (4574137/25000000000000)
theorem h316 : Model (fun x => f316 ((89/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(4054715331647/4000000000000),(895739991103/50000000000000),(-9120503469/100000000000000),(-57162441/100000000000000)⟩
def e317 : ℝ := (40844713/50000000000000)
theorem h317 : Model (fun x => f317 ((89/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(11389649807997/25000000000000),(293265169171/100000000000000),(-462138559/6250000000000),(7173763/12500000000000)⟩
def e318 : ℝ := (613321/1562500000000)
theorem h318 : Model (fun x => f318 ((89/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-26895476724519/25000000000000),(-602901781607/100000000000000),(10755761609/100000000000000),(-36183049/20000000000000)⟩
def e319 : ℝ := (67737353/100000000000000)
theorem h319 : Model (fun x => f319 ((89/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((89/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-87131/1600),(-979/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((89/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((89/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(8633/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((89/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(258189/1600),(961/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((89/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((89/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(430989/1600),(961/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((89/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2154945/32),(4805/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((89/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((89/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1054025397888056123/100000000000000),(2836476178178717/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (136449/100000000000000)
theorem h329 : Model (fun x => f329 ((89/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4743718709/50000000000000),(-25531539/100000000000000),(240253/50000000000000),(-1201/50000000000000)⟩
def e330 : ℝ := (3/10000000000000)
theorem h330 : Model (fun x => f330 ((89/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (26278579302349097/2500000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(5111226456683/800000000000),(564925176197/50000000000000),(8384276699/100000000000000),(26428731/100000000000000)⟩
def e331 : ℝ := (3580673/100000000000000)
theorem h331 : Model (fun x => f331 ((89/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((89/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(449/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((89/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((89/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((89/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(695806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((89/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((89/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((89/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3086940459910289/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (213/20000000000000)
theorem h339 : Model (fun x => f339 ((89/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3794193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((89/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((89/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((89/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(534514885022363/25000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (133/12500000000000)
theorem h343 : Model (fun x => f343 ((89/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2338569111967/50000000000000),(-6163547567/100000000000000),(4061171/50000000000000),(-669/6250000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((89/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2135241998453907/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(36095118050137/25000000000000),(84723919561/10000000000000),(-69780907/6250000000000),(1471309/100000000000000)⟩
def e345 : ℝ := (1493/50000000000000)
theorem h345 : Model (fun x => f345 ((89/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(61095118050137/25000000000000),(84723919561/10000000000000),(-69780907/6250000000000),(1471309/100000000000000)⟩
def e346 : ℝ := (1493/50000000000000)
theorem h346 : Model (fun x => f346 ((89/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(61095118050137/50000000000000),(84723919561/20000000000000),(-69780907/12500000000000),(367827/50000000000000)⟩
def e347 : ℝ := (747/50000000000000)
theorem h347 : Model (fun x => f347 ((89/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(11095118050137/50000000000000),(84723919561/20000000000000),(-69780907/12500000000000),(367827/50000000000000)⟩
def e348 : ℝ := (747/50000000000000)
theorem h348 : Model (fun x => f348 ((89/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(18037606281469/4000000000000),(781679019759/50000000000000),(-2060198207/100000000000000),(2714913/100000000000000)⟩
def e349 : ℝ := (1379/25000000000000)
theorem h349 : Model (fun x => f349 ((89/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(280665444275101/10000000000000),(781679019759/50000000000000),(-2060198207/100000000000000),(2714913/100000000000000)⟩
def e350 : ℝ := (5517/100000000000000)
theorem h350 : Model (fun x => f350 ((89/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(53585276408067/1562500000000),(13799809141737/100000000000000),(-11562741427/100000000000000),(6509817/100000000000000)⟩
def e351 : ℝ := (10407/12500000000000)
theorem h351 : Model (fun x => f351 ((89/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(217795966062431/2500000000000),(13799809141737/100000000000000),(-11562741427/100000000000000),(6509817/100000000000000)⟩
def e352 : ℝ := (83257/100000000000000)
theorem h352 : Model (fun x => f352 ((89/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5322508102971141/50000000000000),(53767075190443/100000000000000),(-860689047/20000000000000),(-10795149/20000000000000)⟩
def e353 : ℝ := (85243/20000000000000)
theorem h353 : Model (fun x => f353 ((89/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(15914063824989901/100000000000000),(53767075190443/100000000000000),(-860689047/20000000000000),(-10795149/20000000000000)⟩
def e354 : ℝ := (53277/12500000000000)
theorem h354 : Model (fun x => f354 ((89/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(3889086432180691/20000000000000),(133113209289267/100000000000000),(133669653159/100000000000000),(-267264103/100000000000000)⟩
def e355 : ℝ := (190469/20000000000000)
theorem h355 : Model (fun x => f355 ((89/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(1089057322330887/5000000000000),(133113209289267/100000000000000),(133669653159/100000000000000),(-267264103/100000000000000)⟩
def e356 : ℝ := (476173/50000000000000)
theorem h356 : Model (fun x => f356 ((89/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(26614434268468657/100000000000000),(254920549685687/100000000000000),(302816127121/50000000000000),(-68637351/20000000000000)⟩
def e357 : ℝ := (2396731/100000000000000)
theorem h357 : Model (fun x => f357 ((89/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(27016815220849609/100000000000000),(254920549685687/100000000000000),(302816127121/50000000000000),(-68637351/20000000000000)⟩
def e358 : ℝ := (599183/25000000000000)
theorem h358 : Model (fun x => f358 ((89/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(33011910305130899/100000000000000),(21296827275367/5000000000000),(1669096259029/100000000000000),(921899521/100000000000000)⟩
def e359 : ℝ := (6311963/100000000000000)
theorem h359 : Model (fun x => f359 ((89/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(32994291257511851/100000000000000),(21296827275367/5000000000000),(1669096259029/100000000000000),(921899521/100000000000000)⟩
def e360 : ℝ := (1577991/25000000000000)
theorem h360 : Model (fun x => f360 ((89/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(20157901193582897/50000000000000),(660223154516451/100000000000000),(3659633615049/100000000000000),(3031017403/50000000000000)⟩
def e361 : ℝ := (263119/2500000000000)
theorem h361 : Model (fun x => f361 ((89/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(40319135720499127/100000000000000),(660223154516451/100000000000000),(3659633615049/100000000000000),(3031017403/50000000000000)⟩
def e362 : ℝ := (10524761/100000000000000)
theorem h362 : Model (fun x => f362 ((89/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(4473455704984333/50000000000000),(317304837353507/100000000000000),(3383835542559/100000000000000),(1682379591/12500000000000)⟩
def e363 : ℝ := (13106487/100000000000000)
theorem h363 : Model (fun x => f363 ((89/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(149304537982407/100000000000000),(1035243573449/100000000000000),(107572089/25000000000000),(-586379/20000000000000)⟩
def e364 : ℝ := (13023/100000000000000)
theorem h364 : Model (fun x => f364 ((89/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(111095118050137/50000000000000),(84723919561/20000000000000),(-69780907/12500000000000),(367827/50000000000000)⟩
def e365 : ℝ := (747/50000000000000)
theorem h365 : Model (fun x => f365 ((89/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(98737002036591/20000000000000),(1882482769059/100000000000000),(-171551539/25000000000000),(-1460587/100000000000000)⟩
def e366 : ℝ := (16011/100000000000000)
theorem h366 : Model (fun x => f366 ((89/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1096919889717169/100000000000000),(6274039363679/100000000000000),(1846949917/50000000000000),(-13029281/100000000000000)⟩
def e367 : ℝ := (3409/6250000000000)
theorem h367 : Model (fun x => f367 ((89/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1218624446396721/50000000000000),(3717414100049/20000000000000),(3582752487/12500000000000),(-1610273/4000000000000)⟩
def e368 : ℝ := (41917/25000000000000)
theorem h368 : Model (fun x => f368 ((89/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1819461599433289/50000000000000),(6622850283307/12500000000000),(12285117371/5000000000000),(122568437/50000000000000)⟩
def e369 : ℝ := (1411297/100000000000000)
theorem h369 : Model (fun x => f369 ((89/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(61095118050137/6250000000000),(84723919561/2500000000000),(-69780907/1562500000000),(367827/6250000000000)⟩
def e370 : ℝ := (747/6250000000000)
theorem h370 : Model (fun x => f370 ((89/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1126826426784599/100000000000000),(4424200355889/100000000000000),(-1008922423/25000000000000),(2953337/100000000000000)⟩
def e371 : ℝ := (999/4000000000000)
theorem h371 : Model (fun x => f371 ((89/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1226826426784599/100000000000000),(4424200355889/100000000000000),(-1008922423/25000000000000),(2953337/100000000000000)⟩
def e372 : ℝ := (999/4000000000000)
theorem h372 : Model (fun x => f372 ((89/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(22321635727045333/50000000000000),(405500136485347/50000000000000),(2605775503687/50000000000000),(185109629/1562500000000)⟩
def e373 : ℝ := (649867/3125000000000)
theorem h373 : Model (fun x => f373 ((89/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(223997921171/100000000000000),(-4069199441/100000000000000),(955461/2000000000000),(-452271/100000000000000)⟩
def e374 : ℝ := (197/5000000000000)
theorem h374 : Model (fun x => f374 ((89/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (21913523881150299/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(1002044778367/5000000000000),(69337714073/20000000000000),(-132229117/12500000000000),(1787429/50000000000000)⟩
def e375 : ℝ := (770171/100000000000000)
theorem h375 : Model (fun x => f375 ((89/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(36095118050137/12500000000000),(84723919561/5000000000000),(-69780907/3125000000000),(1471309/50000000000000)⟩
def e376 : ℝ := (1493/25000000000000)
theorem h376 : Model (fun x => f376 ((89/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(5114974976291/12500000000000),(-14186427403/10000000000000),(678776433/100000000000000),(-3247733/100000000000000)⟩
def e377 : ℝ := (15793/100000000000000)
theorem h377 : Model (fun x => f377 ((89/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (243532115036131/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(118160400379341/100000000000000),(283728548059/100000000000000),(-1357552869/100000000000000),(3247731/50000000000000)⟩
def e378 : ℝ := (122783/100000000000000)
theorem h378 : Model (fun x => f378 ((89/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(18160400379341/100000000000000),(283728548059/100000000000000),(-1357552869/100000000000000),(3247731/50000000000000)⟩
def e379 : ℝ := (122783/100000000000000)
theorem h379 : Model (fun x => f379 ((89/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(436068144257091/100000000000000),(104709345117/10000000000000),(-5010016541/100000000000000),(23971347/100000000000000)⟩
def e380 : ℝ := (453131/100000000000000)
theorem h380 : Model (fun x => f380 ((89/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(174486401873211/6250000000000),(104709345117/10000000000000),(-5010016541/100000000000000),(23971347/100000000000000)⟩
def e381 : ℝ := (113283/25000000000000)
theorem h381 : Model (fun x => f381 ((89/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3298781296974273/100000000000000),(2289583391943/25000000000000),(-40848875033/100000000000000),(2831783/1562500000000)⟩
def e382 : ℝ := (834107/20000000000000)
theorem h382 : Model (fun x => f382 ((89/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(343246489974209/4000000000000),(2289583391943/25000000000000),(-40848875033/100000000000000),(2831783/1562500000000)⟩
def e383 : ℝ := (521317/12500000000000)
theorem h383 : Model (fun x => f383 ((89/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(10139535671038997/100000000000000),(35168730668437/100000000000000),(-138776201741/100000000000000),(106260789/20000000000000)⟩
def e384 : ℝ := (8578039/50000000000000)
theorem h384 : Model (fun x => f384 ((89/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(1926072911260827/12500000000000),(35168730668437/100000000000000),(-138776201741/100000000000000),(106260789/20000000000000)⟩
def e385 : ℝ := (17156079/100000000000000)
theorem h385 : Model (fun x => f385 ((89/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(18206843708350579/100000000000000),(85274062611581/100000000000000),(-273374451239/100000000000000),(378733863/50000000000000)⟩
def e386 : ℝ := (11243783/25000000000000)
theorem h386 : Model (fun x => f386 ((89/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(641954937314527/3125000000000),(85274062611581/100000000000000),(-273374451239/100000000000000),(378733863/50000000000000)⟩
def e387 : ℝ := (44975133/100000000000000)
theorem h387 : Model (fun x => f387 ((89/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(6068292193486341/25000000000000),(19880659416539/12500000000000),(-71989914363/20000000000000),(296079101/100000000000000)⟩
def e388 : ℝ := (11253277/12500000000000)
theorem h388 : Model (fun x => f388 ((89/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(6168887431581579/25000000000000),(19880659416539/12500000000000),(-71989914363/20000000000000),(296079101/100000000000000)⟩
def e389 : ℝ := (90026217/100000000000000)
theorem h389 : Model (fun x => f389 ((89/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(29156728352430557/100000000000000),(257940113081167/100000000000000),(-61808927603/20000000000000),(-613882093/50000000000000)⟩
def e390 : ℝ := (153209813/100000000000000)
theorem h390 : Model (fun x => f390 ((89/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(29139109304811509/100000000000000),(257940113081167/100000000000000),(-61808927603/20000000000000),(-613882093/50000000000000)⟩
def e391 : ℝ := (76604907/50000000000000)
theorem h391 : Model (fun x => f391 ((89/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(17215444110769543/50000000000000),(193729521051749/50000000000000),(-28897458291/100000000000000),(-123016643/3125000000000)⟩
def e392 : ℝ := (235034897/100000000000000)
theorem h392 : Model (fun x => f392 ((89/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(34434221554872419/100000000000000),(193729521051749/50000000000000),(-28897458291/100000000000000),(-123016643/3125000000000)⟩
def e393 : ℝ := (117517449/50000000000000)
theorem h393 : Model (fun x => f393 ((89/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(6253392501874171/100000000000000),(168063830205013/100000000000000),(313310628861/50000000000000),(-1910089991/50000000000000)⟩
def e394 : ℝ := (50275399/50000000000000)
theorem h394 : Model (fun x => f394 ((89/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(139618802178061/100000000000000),(335254788377/50000000000000),(-2403160921/100000000000000),(7646597/100000000000000)⟩
def e395 : ℝ := (346329/100000000000000)
theorem h395 : Model (fun x => f395 ((89/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(218160400379341/100000000000000),(283728548059/100000000000000),(-1357552869/100000000000000),(3247731/50000000000000)⟩
def e396 : ℝ := (122783/100000000000000)
theorem h396 : Model (fun x => f396 ((89/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(475939602936743/100000000000000),(154745834109/12500000000000),(-5118266659/100000000000000),(20637521/100000000000000)⟩
def e397 : ℝ := (118379/20000000000000)
theorem h397 : Model (fun x => f397 ((89/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(259577935832661/25000000000000),(81022591503/2000000000000),(-882168619/6250000000000),(22304669/50000000000000)⟩
def e398 : ℝ := (2087933/100000000000000)
theorem h398 : Model (fun x => f398 ((89/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(283148132054481/12500000000000),(11783947334711/100000000000000),(-33394101197/100000000000000),(69719401/100000000000000)⟩
def e399 : ℝ := (1605927/25000000000000)
theorem h399 : Model (fun x => f399 ((89/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1581312121456083/50000000000000),(31640888852619/100000000000000),(-5511997689/25000000000000),(-236546899/100000000000000)⟩
def e400 : ℝ := (4768287/25000000000000)
theorem h400 : Model (fun x => f400 ((89/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(118160400379341/12500000000000),(283728548059/12500000000000),(-1357552869/12500000000000),(3247731/6250000000000)⟩
def e401 : ℝ := (122783/12500000000000)
theorem h401 : Model (fun x => f401 ((89/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1084902005212789/100000000000000),(1470168980613/50000000000000),(-13263583873/100000000000000),(59610293/100000000000000)⟩
def e402 : ℝ := (1328593/100000000000000)
theorem h402 : Model (fun x => f402 ((89/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1184902005212789/100000000000000),(1470168980613/50000000000000),(-13263583873/100000000000000),(59610293/100000000000000)⟩
def e403 : ℝ := (1328593/100000000000000)
theorem h403 : Model (fun x => f403 ((89/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(37473998071612041/100000000000000),(93581073533423/20000000000000),(249624662579/100000000000000),(-1152520129/20000000000000)⟩
def e404 : ℝ := (11353969/4000000000000)
theorem h404 : Model (fun x => f404 ((89/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(133425848783/50000000000000),(-3331946099/100000000000000),(39825553/100000000000000),(-434037/100000000000000)⟩
def e405 : ℝ := (53/781250000000)
theorem h405 : Model (fun x => f405 ((89/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (37005837032832477/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(4171821011679/25000000000000),(1920972131/800000000000),(-718599313/50000000000000),(4358707/50000000000000)⟩
def e406 : ℝ := (133033/12500000000000)
theorem h406 : Model (fun x => f406 ((89/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(4591022451757/12500000000000),(29340504337/5000000000000),(-1247515781/50000000000000),(768267/6250000000000)⟩
def e407 : ℝ := (366887/20000000000000)
theorem h407 : Model (fun x => f407 ((89/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(11732877709323/5000000000000),(4164122517289/100000000000000),(-49850969/800000000000),(54626091/50000000000000)⟩
def e408 : ℝ := (6581261/50000000000000)
theorem h408 : Model (fun x => f408 ((89/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(21092813859457/20000000000000),(686526195441/100000000000000),(-2102878743/20000000000000),(167241359/100000000000000)⟩
def e409 : ℝ := (5641731/50000000000000)
theorem h409 : Model (fun x => f409 ((89/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-2117837600791/100000000000000),(41812206917/50000000000000),(120683947/50000000000000),(-6836943/50000000000000)⟩
def e410 : ℝ := (15804163/20000000000000)
theorem h410 : Model (fun x => f410 ((89/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(3952025922363281/50000000000000),(104127501220703/25000000000000),(895073/10240000),(1869/2048000)⟩
def e411 : ℝ := (14831543/3125000000000)
theorem h411 : Model (fun x => f411 ((89/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(43681/1600),(209/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((89/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(9129329/64000),(131043/64000),(627/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((89/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(225495905386142811/20000000000000),(75597305191489063/100000000000000),(217711788181317/10000000000000),(17559657830383/50000000000000)⟩
def e414 : ℝ := (348710108103/100000000000000)
theorem h414 : Model (fun x => f414 ((89/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(8869340649/100000000000000),(-594687741/100000000000000),(11373683/50000000000000),(-163289/25000000000000)⟩
def e415 : ℝ := (2941/12500000000000)
theorem h415 : Model (fun x => f415 ((89/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (1049669635831642953/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2855738669363/50000000000000),(-4707498569/100000000000000),(-139926437/25000000000000),(1533933/12500000000000)⟩
def e416 : ℝ := (7313369/25000000000000)
theorem h416 : Model (fun x => f416 ((89/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(718727947587/20000000000000),(15783383053/20000000000000),(-159168927/50000000000000),(-701211/50000000000000)⟩
def e417 : ℝ := (108274291/100000000000000)
theorem h417 : Model (fun x => f417 ((89/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((89/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((1796712675513/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/5) (9/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/5) (9/4) ≤ (449205237451/250000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(89/40)-(1/40)) (by norm_num : ((89/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel24

