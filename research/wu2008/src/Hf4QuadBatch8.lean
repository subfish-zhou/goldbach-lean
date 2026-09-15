import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel25
open Hf4Quad.Dag

def p0 : Cubic := ⟨(91/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((91/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((91/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((91/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((91/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(199333333333333/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((91/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-199333333333333/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((91/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-61447619047619/20000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((91/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((91/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(8281/1600),(91/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((91/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(626551851851851/100000000000000),(1377037037037/10000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((91/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-626551851851851/100000000000000),(-1377037037037/10000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((91/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-466894973544973/50000000000000),(-9075661375661/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((91/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((91/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(753571/64000),(24843/64000),(273/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((91/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(458858452662037/4000000000000),(378180043402777/100000000000000),(4155824652777/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/25000000000000)
theorem h14 : Model (fun x => f14 ((91/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-458858452662037/4000000000000),(-378180043402777/100000000000000),(-4155824652777/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/25000000000000)
theorem h15 : Model (fun x => f15 ((91/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-12405251263640871/100000000000000),(-396331366154099/100000000000000),(-2115743014219/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (9/100000000000000)
theorem h16 : Model (fun x => f16 ((91/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((91/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(68574961/2560000),(753571/640000),(24843/1280000),(91/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((91/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(1496675736111111/20000000000000),(164469861111111/50000000000000),(5422083333333/100000000000000),(19861111111/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((91/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1230468145771329/25000000000000),(-67391643931877/100000000000000),(238119460979/20000000000000),(24499421297/100000000000000)⟩
def e20 : ℝ := (21825399/20000000000000)
theorem h20 : Model (fun x => f20 ((91/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((91/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(6094063916992187/100000000000000),(83709669189453/25000000000000),(753571/10240000),(8281/10240000)⟩
def e22 : ℝ := (445312501/100000000000000)
theorem h22 : Model (fun x => f22 ((91/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(39701697888849099/100000000000000),(1090705985957391/50000000000000),(47943120261863/100000000000000),(105369495081/20000000000000)⟩
def e23 : ℝ := (2901128481/100000000000000)
theorem h23 : Model (fun x => f23 ((91/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(34779825305763783/100000000000000),(422804065596581/20000000000000),(24566858783379/50000000000000),(275673448351/50000000000000)⟩
def e24 : ℝ := (752563869/25000000000000)
theorem h24 : Model (fun x => f24 ((91/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((91/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(554559816446289/4000000000000),(457054793774413/50000000000000),(5022580151367/20000000000000),(367954589843/100000000000000)⟩
def e26 : ℝ := (3045947271/100000000000000)
theorem h26 : Model (fun x => f26 ((91/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(15565819186495043/50000000000000),(102631774856011/5000000000000),(28195542542859/50000000000000),(826243004917/100000000000000)⟩
def e27 : ℝ := (6839682657/100000000000000)
theorem h27 : Model (fun x => f27 ((91/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(65911463678753869/100000000000000),(1333329864033/32000000000),(26381200663119/25000000000000),(1377589901619/100000000000000)⟩
def e28 : ℝ := (9849938133/100000000000000)
theorem h28 : Model (fun x => f28 ((91/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((91/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(15770294780191343/50000000000000),(2426199196952509/100000000000000),(1999614722763/2500000000000),(1464919210813/100000000000000)⟩
def e30 : ℝ := (1012783967/6250000000000)
theorem h30 : Model (fun x => f30 ((91/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1496926393421337/20000000000000),(287870460273333/50000000000000),(18980469908131/100000000000000),(173813826997/50000000000000)⟩
def e31 : ℝ := (384536389/10000000000000)
theorem h31 : Model (fun x => f31 ((91/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(36698047822930277/50000000000000),(4742396745649791/100000000000000),(124505272560607/100000000000000),(1725217555613/100000000000000)⟩
def e32 : ℝ := (13695302023/100000000000000)
theorem h32 : Model (fun x => f32 ((91/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((91/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(3552549/320),(39039/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((91/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((91/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(201019/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((91/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(6768853/320),(56711/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((91/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((91/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(7498453/320),(56711/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((91/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-7498453/320),(-56711/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((91/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((91/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(131/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((91/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(17161/1600),(131/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((91/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((91/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(360381/160),(2751/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((91/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(8879491427/20000000000000),(-338911887/50000000000000),(388067/5000000000000),(-19749/25000000000000)⟩
def e46 : ℝ := (773/100000000000000)
theorem h46 : Model (fun x => f46 ((91/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (177429/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-520175383822363/50000000000000),(146816651423/100000000000000),(-569412849/50000000000000),(1104487/12500000000000)⟩
def e47 : ℝ := (3608897/10000000000000)
theorem h47 : Model (fun x => f47 ((91/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((91/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(171/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((91/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((91/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((91/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(71249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((91/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(121249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((91/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((91/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(121249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((91/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((91/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2546249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((91/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((91/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(21249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((91/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(54107812499997/10000000000000),(12468749999979/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (61/50000000000000)
theorem h60 : Model (fun x => f60 ((91/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(147015624999997/100000000000000),(202083333333/20000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((91/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((91/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(121249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((91/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1359515624999987/100000000000000),(207083333333/4000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((91/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1459515624999987/100000000000000),(207083333333/4000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((91/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(7897119777831523/100000000000000),(2624942749019/1250000000000),(1187026367179/100000000000000),(525987413/25000000000000)⟩
def e66 : ℝ := (635029/100000000000000)
theorem h66 : Model (fun x => f66 ((91/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(221249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((91/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(97903124999999/20000000000000),(1843749999997/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((91/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(270763330078121/25000000000000),(611894531249/10000000000000),(11523437499/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (63/100000000000000)
theorem h69 : Model (fun x => f69 ((91/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(85530017962858169/100000000000000),(689395702107877/25000000000000),(26615653048267/100000000000000),(30047585829/25000000000000)⟩
def e70 : ℝ := (287966621/100000000000000)
theorem h70 : Model (fun x => f70 ((91/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((91/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3087328124999937/12500000000000),(4243749999993/2500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((91/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1049691562499929/20000000000000),(34745703124943/25000000000000),(769270833327/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1397/100000000000000)
theorem h73 : Model (fun x => f73 ((91/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(56843596603477371/100000000000000),(114150514296151/6250000000000),(17440698348849/100000000000000),(3065145127/4000000000000)⟩
def e74 : ℝ := (693107/400000000000)
theorem h74 : Model (fun x => f74 ((91/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(7118680728316777/5000000000000),(1145997759292481/25000000000000),(11014087849279/25000000000000),(196818971491/100000000000000)⟩
def e75 : ℝ := (461243371/100000000000000)
theorem h75 : Model (fun x => f75 ((91/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((91/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1029109374999979/12500000000000),(1414583333331/2500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((91/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(4515624999999/100000000000000),(177083333333/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((91/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(959570312499/100000000000000),(56445312499/100000000000000),(1106770833/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((91/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(1580004487303/2000000000000),(519002888989/10000000000000),(123990614121/100000000000000),(1276674599/100000000000000)⟩
def e80 : ℝ := (2588261/50000000000000)
theorem h80 : Model (fun x => f80 ((91/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(174787996407893/100000000000000),(5906053260201/50000000000000),(295954354117/100000000000000),(3341270109/100000000000000)⟩
def e81 : ℝ := (16794107/100000000000000)
theorem h81 : Model (fun x => f81 ((91/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(142548402562743433/100000000000000),(2297901571845163/50000000000000),(44352305751233/100000000000000),(125100151/62500000000)⟩
def e82 : ℝ := (239018739/50000000000000)
theorem h82 : Model (fun x => f82 ((91/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(101954345703/50000000000000),(15992838541/100000000000000),(117594401/25000000000000),(3074363/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((91/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(43330596923/100000000000000),(4248097737/100000000000000),(41648017/25000000000000),(326651/10000000000000)⟩
def e84 : ℝ := (16077/50000000000000)
theorem h84 : Model (fun x => f84 ((91/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(4603875923/50000000000000),(541632461/50000000000000),(53101221/100000000000000),(694133/50000000000000)⟩
def e85 : ℝ := (1029/5000000000000)
theorem h85 : Model (fun x => f85 ((91/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1956647267/100000000000000),(67139857/25000000000000),(15797613/100000000000000),(516261/100000000000000)⟩
def e86 : ℝ := (5123/50000000000000)
theorem h86 : Model (fun x => f86 ((91/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(5869941801/100000000000000),(201419571/25000000000000),(47392839/100000000000000),(1548783/100000000000000)⟩
def e87 : ℝ := (15369/50000000000000)
theorem h87 : Model (fun x => f87 ((91/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-5869941801/100000000000000),(-201419571/25000000000000),(-47392839/100000000000000),(-1548783/100000000000000)⟩
def e88 : ℝ := (15369/50000000000000)
theorem h88 : Model (fun x => f88 ((91/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(4454637396650051/3125000000000),(2297901169006021/50000000000000),(22176129179197/50000000000000),(200158692817/100000000000000)⟩
def e89 : ℝ := (59758527/12500000000000)
theorem h89 : Model (fun x => f89 ((91/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3087328124999937/10000000000000),(4243749999993/2000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((91/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(7488298347473/312500000000),(3610177734369/20000000000000),(10198242187/20000000000000),(8002387/12500000000000)⟩
def e91 : ℝ := (15163/50000000000000)
theorem h91 : Model (fun x => f91 ((91/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(369901345544703101/50000000000000),(5328728102854381/50000000000000),(62780737436743/100000000000000),(48443075719/25000000000000)⟩
def e92 : ℝ := (165731121/50000000000000)
theorem h92 : Model (fun x => f92 ((91/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(211204963/1562500000000),(-97362507/50000000000000),(207261/12500000000000),(-5451/50000000000000)⟩
def e93 : ℝ := (77/100000000000000)
theorem h93 : Model (fun x => f93 ((91/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (729082260042495579/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(3853686892699/20000000000000),(171821311373/50000000000000),(-36903247/6250000000000),(270513/20000000000000)⟩
def e94 : ℝ := (33583/10000000000000)
theorem h94 : Model (fun x => f94 ((91/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(71249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((91/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(20618556701031/50000000000000),(-70854146739/50000000000000),(3043563/625000000000),(-1673437/100000000000000)⟩
def e96 : ℝ := (5773/100000000000000)
theorem h96 : Model (fun x => f96 ((91/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (241666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(940206185567/800000000000),(56683317391/20000000000000),(-243485041/25000000000000),(418359/12500000000000)⟩
def e97 : ℝ := (44447/100000000000000)
theorem h97 : Model (fun x => f97 ((91/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(19744329896907/800000000000),(1190349665211/20000000000000),(-5113185861/25000000000000),(8785539/12500000000000)⟩
def e98 : ℝ := (933387/100000000000000)
theorem h98 : Model (fun x => f98 ((91/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(140206185567/800000000000),(56683317391/20000000000000),(-243485041/25000000000000),(418359/12500000000000)⟩
def e99 : ℝ := (44447/100000000000000)
theorem h99 : Model (fun x => f99 ((91/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(432543309597157/100000000000000),(4018964075841/50000000000000),(-10753504331/100000000000000),(-4202577/20000000000000)⟩
def e100 : ℝ := (466207/25000000000000)
theorem h100 : Model (fun x => f100 ((91/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(69061536826441/50000000000000),(20817970949/3125000000000),(-1486011799/100000000000000),(1173129/50000000000000)⟩
def e101 : ℝ := (533/400000000000)
theorem h101 : Model (fun x => f101 ((91/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(940206185567/80000000000),(56683317391/2000000000000),(-243485041/2500000000000),(418359/1250000000000)⟩
def e102 : ℝ := (44447/10000000000000)
theorem h102 : Model (fun x => f102 ((91/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(82086300350727/6250000000000),(1750170469959/50000000000000),(-11225413439/100000000000000),(17907489/50000000000000)⟩
def e103 : ℝ := (14443/2500000000000)
theorem h103 : Model (fun x => f103 ((91/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(88336300350727/6250000000000),(1750170469959/50000000000000),(-11225413439/100000000000000),(17907489/50000000000000)⟩
def e104 : ℝ := (14443/2500000000000)
theorem h104 : Model (fun x => f104 ((91/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(6113484113803513/100000000000000),(16093378026679/12500000000000),(631344913/781250000000),(-710388387/50000000000000)⟩
def e105 : ℝ := (16159941/50000000000000)
theorem h105 : Model (fun x => f105 ((91/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(1740206185567/800000000000),(56683317391/20000000000000),(-243485041/25000000000000),(418359/12500000000000)⟩
def e106 : ℝ := (44447/100000000000000)
theorem h106 : Model (fun x => f106 ((91/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(59146827505579/12500000000000),(616504122139/50000000000000),(-3433892127/100000000000000),(4520001/50000000000000)⟩
def e107 : ℝ := (3471/1562500000000)
theorem h107 : Model (fun x => f107 ((91/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(1029276750818729/100000000000000),(2011583037701/50000000000000),(-2145872047/25000000000000),(137599/1000000000000)⟩
def e108 : ℝ := (198813/25000000000000)
theorem h108 : Model (fun x => f108 ((91/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(62924670648375967/100000000000000),(196389850811431/12500000000000),(2743368537277/50000000000000),(-10791147187/50000000000000)⟩
def e109 : ℝ := (215060367/50000000000000)
theorem h109 : Model (fun x => f109 ((91/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1450292273355261/6250000000000),(437177389929/390625000000),(-31206247779/12500000000000),(24635709/6250000000000)⟩
def e110 : ℝ := (11193/50000000000)
theorem h110 : Model (fun x => f110 ((91/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(101669973802217/2500000000000),(17076058710967/20000000000000),(23719877997/50000000000000),(-237961423/25000000000000)⟩
def e111 : ℝ := (21657153/100000000000000)
theorem h111 : Model (fun x => f111 ((91/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(8371723223277697/20000000000000),(521206793567967/50000000000000),(714840835357/20000000000000),(-7328783093/50000000000000)⟩
def e112 : ℝ := (143756159/50000000000000)
theorem h112 : Model (fun x => f112 ((91/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(26195821691191113/25000000000000),(1306766196813691/50000000000000),(9060941251339/100000000000000),(-452998257/1250000000000)⟩
def e113 : ℝ := (179408263/25000000000000)
theorem h113 : Model (fun x => f113 ((91/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(483430757785087/6250000000000),(145725796643/390625000000),(-10402082593/12500000000000),(8211903/6250000000000)⟩
def e114 : ℝ := (3731/50000000000)
theorem h114 : Model (fun x => f114 ((91/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(767881815283/25000000000000),(49670948229/50000000000000),(461868529/100000000000000),(-2173743/50000000000000)⟩
def e115 : ℝ := (11089/25000000000000)
theorem h115 : Model (fun x => f115 ((91/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(107661780287/20000000000000),(3264456649/12500000000000),(66516521/20000000000000),(-6353/2000000000000)⟩
def e116 : ℝ := (4573/20000000000000)
theorem h116 : Model (fun x => f116 ((91/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(10409403205727/25000000000000),(2220838065389/100000000000000),(35019597407/100000000000000),(78477441/100000000000000)⟩
def e117 : ℝ := (545233/25000000000000)
theorem h117 : Model (fun x => f117 ((91/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(18114507846667/20000000000000),(4948903074317/100000000000000),(82065348041/100000000000000),(249723931/100000000000000)⟩
def e118 : ℝ := (2407269/50000000000000)
theorem h118 : Model (fun x => f118 ((91/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(104873859303997787/100000000000000),(2618481296701699/100000000000000),(457150329969/5000000000000),(-35990136629/100000000000000)⟩
def e119 : ℝ := (72244759/10000000000000)
theorem h119 : Model (fun x => f119 ((91/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(47171398579/50000000000000),(3051313431/50000000000000),(127060959/100000000000000),(650589/100000000000000)⟩
def e120 : ℝ := (3803/50000000000000)
theorem h120 : Model (fun x => f120 ((91/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(1033394041/6250000000000),(668457839/50000000000000),(38645429/100000000000000),(208927/50000000000000)⟩
def e121 : ℝ := (443/20000000000000)
theorem h121 : Model (fun x => f121 ((91/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2897764733/100000000000000),(281165771/100000000000000),(2600229/25000000000000),(42573/25000000000000)⟩
def e122 : ℝ := (63/5000000000000)
theorem h122 : Model (fun x => f122 ((91/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(253927837/50000000000000),(57489221/100000000000000),(10123/390625000000),(56681/100000000000000)⟩
def e123 : ℝ := (621/100000000000000)
theorem h123 : Model (fun x => f123 ((91/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(761783511/50000000000000),(172467663/100000000000000),(30369/390625000000),(170043/100000000000000)⟩
def e124 : ℝ := (1863/100000000000000)
theorem h124 : Model (fun x => f124 ((91/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-761783511/50000000000000),(-172467663/100000000000000),(-30369/390625000000),(-170043/100000000000000)⟩
def e125 : ℝ := (1863/100000000000000)
theorem h125 : Model (fun x => f125 ((91/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(20974771556086153/20000000000000),(654620281058509/25000000000000),(2285749706229/25000000000000),(-2249394167/6250000000000)⟩
def e126 : ℝ := (722449453/100000000000000)
theorem h126 : Model (fun x => f126 ((91/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1450292273355261/5000000000000),(437177389929/312500000000),(-31206247779/10000000000000),(24635709/5000000000000)⟩
def e127 : ℝ := (11193/40000000000)
theorem h127 : Model (fun x => f127 ((91/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2238942210543819/100000000000000),(2917141037491/25000000000000),(-3458703749/20000000000000),(217411/25000000000000)⟩
def e128 : ℝ := (489817/20000000000000)
theorem h128 : Model (fun x => f128 ((91/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(324712058844064867/50000000000000),(6516773403352317/100000000000000),(1080228470063/25000000000000),(-24661225151/50000000000000)⟩
def e129 : ℝ := (1456357441/100000000000000)
theorem h129 : Model (fun x => f129 ((91/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(7699128911/50000000000000),(-4828651/3125000000000),(1448077/100000000000000),(-6167/50000000000000)⟩
def e130 : ℝ := (141/100000000000000)
theorem h130 : Model (fun x => f130 ((91/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (321451486296044711/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(4037186752227/25000000000000),(241152711891/100000000000000),(-223895467/20000000000000),(664141/12500000000000)⟩
def e131 : ℝ := (400559/100000000000000)
theorem h131 : Model (fun x => f131 ((91/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(35417181472403/100000000000000),(584795334637/100000000000000),(-1709929287/100000000000000),(6665693/100000000000000)⟩
def e132 : ℝ := (736389/100000000000000)
theorem h132 : Model (fun x => f132 ((91/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-368462919326271/100000000000000),(-6031924433181/100000000000000),(18244499427/100000000000000),(-2355857/3125000000000)⟩
def e133 : ℝ := (10368321/50000000000000)
theorem h133 : Model (fun x => f133 ((91/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(43956043956043/100000000000000),(-483033450067/100000000000000),(530805989/10000000000000),(-58330329/100000000000000)⟩
def e134 : ℝ := (324059/50000000000000)
theorem h134 : Model (fun x => f134 ((91/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (9/4))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-6478468911231/4000000000000),(-435798101903/50000000000000),(4399385113/25000000000000),(-226516893/100000000000000)⟩
def e135 : ℝ := (16509279/100000000000000)
theorem h135 : Model (fun x => f135 ((91/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(68574961/256000),(753571/64000),(24843/128000),(91/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((91/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((91/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(6782139/32000),(223587/32000),(2457/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((91/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(122832073/256000),(240149/12800),(34671/128000),(109/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((91/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-8281/1600),(-91/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((91/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(121507113/256000),(238693/12800),(34591/128000),(109/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((91/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((91/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(273/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((91/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-273/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((91/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(118012713/256000),(236773/12800),(34591/128000),(109/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((91/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(118780713/256000),(236773/12800),(34591/128000),(109/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((91/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((91/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(118780713/4000),(236773/200),(34591/2000),(109/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((91/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((91/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(12960667629/512000),(142424919/128000),(4695327/256000),(17199/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((91/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(197520689/5000000000000),(-86822281/50000000000000),(2385227/50000000000000),(-52423/50000000000000)⟩
def e151 : ℝ := (229/10000000000000)
theorem h151 : Model (fun x => f151 ((91/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (6190754157/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(29327060339589/25000000000000),(-239824805537/50000000000000),(4412144003/100000000000000),(-7704311/20000000000000)⟩
def e152 : ℝ := (66816647/50000000000000)
theorem h152 : Model (fun x => f152 ((91/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(211/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((91/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(36081/1600),(191/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((91/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(393/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((91/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(5089058524173/100000000000000),(-19423887497/50000000000000),(2965479/1000000000000),(-90549/4000000000000)⟩
def e156 : ℝ := (3483/20000000000000)
theorem h156 : Model (fun x => f156 ((91/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (39/2))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(57380725190839/50000000000000),(2648211849/781250000000),(118619157/20000000000000),(-2263731/50000000000000)⟩
def e157 : ℝ := (376713/50000000000000)
theorem h157 : Model (fun x => f157 ((91/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(107380725190839/50000000000000),(2648211849/781250000000),(118619157/20000000000000),(-2263731/50000000000000)⟩
def e158 : ℝ := (376713/50000000000000)
theorem h158 : Model (fun x => f158 ((91/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(107380725190839/100000000000000),(2648211849/1562500000000),(74136973/25000000000000),(-2263731/100000000000000)⟩
def e159 : ℝ := (188357/50000000000000)
theorem h159 : Model (fun x => f159 ((91/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(7380725190839/100000000000000),(2648211849/1562500000000),(74136973/25000000000000),(-2263731/100000000000000)⟩
def e160 : ℝ := (188357/50000000000000)
theorem h160 : Model (fun x => f160 ((91/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((91/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((91/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(198143004816429/50000000000000),(156370604417/25000000000000),(547201467/50000000000000),(-4177123/50000000000000)⟩
def e163 : ℝ := (1390257/100000000000000)
theorem h163 : Model (fun x => f163 ((91/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2752000295347143/100000000000000),(156370604417/25000000000000),(547201467/50000000000000),(-4177123/50000000000000)⟩
def e164 : ℝ := (695129/50000000000000)
theorem h164 : Model (fun x => f164 ((91/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((91/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2955117874397793/100000000000000),(533589062201/10000000000000),(5198139519/50000000000000),(-4222439/6250000000000)⟩
def e166 : ℝ := (2377977/20000000000000)
theorem h166 : Model (fun x => f166 ((91/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1647499765355749/20000000000000),(533589062201/10000000000000),(5198139519/50000000000000),(-4222439/6250000000000)⟩
def e167 : ℝ := (5944943/50000000000000)
theorem h167 : Model (fun x => f167 ((91/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((91/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(884548597778187/10000000000000),(19691088924791/100000000000000),(44635292961/100000000000000),(-112788261/50000000000000)⟩
def e169 : ℝ := (5505561/12500000000000)
theorem h169 : Model (fun x => f169 ((91/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14114533596829489/100000000000000),(19691088924791/100000000000000),(44635292961/100000000000000),(-112788261/50000000000000)⟩
def e170 : ℝ := (44044489/100000000000000)
theorem h170 : Model (fun x => f170 ((91/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((91/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15156288533580117/100000000000000),(22533265079261/50000000000000),(61579802563/50000000000000),(-213848447/50000000000000)⟩
def e172 : ℝ := (101313239/100000000000000)
theorem h172 : Model (fun x => f172 ((91/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(8746001409647201/50000000000000),(22533265079261/50000000000000),(61579802563/50000000000000),(-213848447/50000000000000)⟩
def e173 : ℝ := (2532831/2500000000000)
theorem h173 : Model (fun x => f173 ((91/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((91/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(4695759869440083/25000000000000),(78039185544999/100000000000000),(260503103017/100000000000000),(-64106791/12500000000000)⟩
def e175 : ℝ := (176411877/100000000000000)
theorem h175 : Model (fun x => f175 ((91/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(4796355107535321/25000000000000),(78039185544999/100000000000000),(260503103017/100000000000000),(-64106791/12500000000000)⟩
def e176 : ℝ := (88205939/50000000000000)
theorem h176 : Model (fun x => f176 ((91/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((91/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(20601443588797093/100000000000000),(58157780153189/50000000000000),(468889230363/100000000000000),(-312074309/100000000000000)⟩
def e178 : ℝ := (132085867/50000000000000)
theorem h178 : Model (fun x => f178 ((91/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(4116764908235609/20000000000000),(58157780153189/50000000000000),(468889230363/100000000000000),(-312074309/100000000000000)⟩
def e179 : ℝ := (52834347/20000000000000)
theorem h179 : Model (fun x => f179 ((91/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((91/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(22103060064326873/100000000000000),(79893551058647/50000000000000),(190418907623/25000000000000),(169280399/50000000000000)⟩
def e181 : ℝ := (181941601/50000000000000)
theorem h181 : Model (fun x => f181 ((91/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(11053196698830103/50000000000000),(79893551058647/50000000000000),(190418907623/25000000000000),(169280399/50000000000000)⟩
def e182 : ℝ := (363883203/100000000000000)
theorem h182 : Model (fun x => f182 ((91/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(407903036571769/25000000000000),(49260591175659/100000000000000),(196294645461/50000000000000),(1289334439/100000000000000)⟩
def e183 : ℝ := (56079291/50000000000000)
theorem h183 : Model (fun x => f183 ((91/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(7206637589069/6250000000000),(363989643269/100000000000000),(462062049/50000000000000),(-385641/10000000000000)⟩
def e184 : ℝ := (408563/50000000000000)
theorem h184 : Model (fun x => f184 ((91/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(207380725190839/100000000000000),(2648211849/1562500000000),(74136973/25000000000000),(-2263731/100000000000000)⟩
def e185 : ℝ := (188357/50000000000000)
theorem h185 : Model (fun x => f185 ((91/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(215033825903391/50000000000000),(702960759941/100000000000000),(758609941/50000000000000),(-65499/781250000000)⟩
def e186 : ℝ := (785277/50000000000000)
theorem h186 : Model (fun x => f186 ((91/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(222969353782029/25000000000000),(2186707682659/100000000000000),(2806597559/50000000000000),(-11233013/50000000000000)⟩
def e187 : ℝ := (2454079/50000000000000)
theorem h187 : Model (fun x => f187 ((91/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(462395462826499/25000000000000),(1511603416701/25000000000000),(17991682141/100000000000000),(-50781723/100000000000000)⟩
def e188 : ℝ := (13626121/100000000000000)
theorem h188 : Model (fun x => f188 ((91/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2132682574989059/100000000000000),(856511019011/6250000000000),(11969255277/20000000000000),(-851771/10000000000000)⟩
def e189 : ℝ := (7794343/25000000000000)
theorem h189 : Model (fun x => f189 ((91/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((91/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(107380725190839/12500000000000),(2648211849/195312500000),(74136973/3125000000000),(-2263731/12500000000000)⟩
def e191 : ℝ := (188357/6250000000000)
theorem h191 : Model (fun x => f191 ((91/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(121794000368977/12500000000000),(1719874109957/100000000000000),(1648253617/50000000000000),(-10983129/50000000000000)⟩
def e192 : ℝ := (1915419/50000000000000)
theorem h192 : Model (fun x => f192 ((91/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(134294000368977/12500000000000),(1719874109957/100000000000000),(1648253617/50000000000000),(-10983129/50000000000000)⟩
def e193 : ℝ := (1915419/50000000000000)
theorem h193 : Model (fun x => f193 ((91/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(572812949024983/2500000000000),(45977637016691/25000000000000),(189791656927/20000000000000),(921059031/100000000000000)⟩
def e194 : ℝ := (418916243/100000000000000)
theorem h194 : Model (fun x => f194 ((91/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(436442647509/100000000000000),(-3503168297/100000000000000),(2510677/25000000000000),(9387/20000000000000)⟩
def e195 : ℝ := (8771/100000000000000)
theorem h195 : Model (fun x => f195 ((91/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (22727657114672647/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(7121051248333/100000000000000),(78918054433/50000000000000),(6064149/4000000000000),(-603241/25000000000000)⟩
def e196 : ℝ := (658609/100000000000000)
theorem h196 : Model (fun x => f196 ((91/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(57380725190839/25000000000000),(2648211849/390625000000),(118619157/10000000000000),(-2263731/25000000000000)⟩
def e197 : ℝ := (376713/25000000000000)
theorem h197 : Model (fun x => f197 ((91/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(46563291420447/100000000000000),(-18373421837/25000000000000),(-125919/1000000000000),(240891/20000000000000)⟩
def e198 : ℝ := (167297/100000000000000)
theorem h198 : Model (fun x => f198 ((91/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (214421880888333/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(1669897143111/1562500000000),(29397474939/20000000000000),(12591899/50000000000000),(-2408913/100000000000000)⟩
def e199 : ℝ := (1102557/100000000000000)
theorem h199 : Model (fun x => f199 ((91/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(107397143111/1562500000000),(29397474939/20000000000000),(12591899/50000000000000),(-2408913/100000000000000)⟩
def e200 : ℝ := (1102557/100000000000000)
theorem h200 : Model (fun x => f200 ((91/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(197206900710251/50000000000000),(135613351653/25000000000000),(46470103/50000000000000),(-8890037/100000000000000)⟩
def e201 : ℝ := (1017241/25000000000000)
theorem h201 : Model (fun x => f201 ((91/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2750128087134787/100000000000000),(135613351653/25000000000000),(46470103/50000000000000),(-8890037/100000000000000)⟩
def e202 : ℝ := (813793/20000000000000)
theorem h202 : Model (fun x => f202 ((91/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(45924310358957/1562500000000),(4622079568171/100000000000000),(1589253097/100000000000000),(-75476059/100000000000000)⟩
def e203 : ℝ := (34708453/100000000000000)
theorem h203 : Model (fun x => f203 ((91/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(41107684076771/500000000000),(4622079568171/100000000000000),(1589253097/100000000000000),(-75476059/100000000000000)⟩
def e204 : ℝ := (17354227/50000000000000)
theorem h204 : Model (fun x => f204 ((91/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(1098329667195351/12500000000000),(17024395502789/100000000000000),(10562857729/100000000000000),(-34401687/12500000000000)⟩
def e205 : ℝ := (128065189/100000000000000)
theorem h205 : Model (fun x => f205 ((91/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14055684956610427/100000000000000),(17024395502789/100000000000000),(10562857729/100000000000000),(-34401687/12500000000000)⟩
def e206 : ℝ := (12806519/10000000000000)
theorem h206 : Model (fun x => f206 ((91/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15021790818247687/100000000000000),(38854635537633/100000000000000),(19926177159/50000000000000),(-306452917/50000000000000)⟩
def e207 : ℝ := (73256997/25000000000000)
theorem h207 : Model (fun x => f207 ((91/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(4339376275990493/25000000000000),(38854635537633/100000000000000),(19926177159/50000000000000),(-306452917/50000000000000)⟩
def e208 : ℝ := (293027989/100000000000000)
theorem h208 : Model (fun x => f208 ((91/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9275279419085023/50000000000000),(8379827223581/12500000000000),(166518817/160000000000),(-251199401/25000000000000)⟩
def e209 : ℝ := (101446603/20000000000000)
theorem h209 : Model (fun x => f209 ((91/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(9476469895275499/50000000000000),(8379827223581/12500000000000),(166518817/160000000000),(-251199401/25000000000000)⟩
def e210 : ℝ := (63404127/12500000000000)
theorem h210 : Model (fun x => f210 ((91/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(1012782720313469/5000000000000),(49752445136307/50000000000000),(13408693319/6250000000000),(-170070309/12500000000000)⟩
def e211 : ℝ := (188904659/25000000000000)
theorem h211 : Model (fun x => f211 ((91/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(5059508839662583/25000000000000),(49752445136307/50000000000000),(13408693319/6250000000000),(-170070309/12500000000000)⟩
def e212 : ℝ := (755618637/100000000000000)
theorem h212 : Model (fun x => f212 ((91/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(10814539976828669/50000000000000),(27218326667657/20000000000000),(380641591791/100000000000000),(-80059589/5000000000000)⟩
def e213 : ℝ := (20745001/2000000000000)
theorem h213 : Model (fun x => f213 ((91/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(21632413286990671/100000000000000),(27218326667657/20000000000000),(380641591791/100000000000000),(-80059589/5000000000000)⟩
def e214 : ℝ := (1037250051/100000000000000)
theorem h214 : Model (fun x => f214 ((91/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(148688600679631/10000000000000),(20575531025849/50000000000000),(231648466773/100000000000000),(-18697241/50000000000000)⟩
def e215 : ℝ := (79594867/25000000000000)
theorem h215 : Model (fun x => f215 ((91/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(57109636476319/50000000000000),(157090430129/50000000000000),(134941227/50000000000000),(-2537471/50000000000000)⟩
def e216 : ℝ := (2367001/100000000000000)
theorem h216 : Model (fun x => f216 ((91/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(3232397143111/1562500000000),(29397474939/20000000000000),(12591899/50000000000000),(-2408913/100000000000000)⟩
def e217 : ℝ := (1102557/100000000000000)
theorem h217 : Model (fun x => f217 ((91/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(213983053635423/50000000000000),(38009725603/6250000000000),(6405001/2000000000000),(-309149/3125000000000)⟩
def e218 : ℝ := (914423/20000000000000)
theorem h218 : Model (fun x => f218 ((91/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(177069622078799/20000000000000),(377433687397/20000000000000),(832101153/50000000000000),(-6030191/20000000000000)⟩
def e219 : ℝ := (2843923/20000000000000)
theorem h219 : Model (fun x => f219 ((91/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1831549889725613/100000000000000),(2602699888759/50000000000000),(32198279/500000000000),(-80780149/100000000000000)⟩
def e220 : ℝ := (9827303/25000000000000)
theorem h220 : Model (fun x => f220 ((91/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1045991483904719/50000000000000),(11699948979753/100000000000000),(3581591203/12500000000000),(-150935967/100000000000000)⟩
def e221 : ℝ := (1390619/1562500000000)
theorem h221 : Model (fun x => f221 ((91/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(1669897143111/195312500000),(29397474939/2500000000000),(12591899/6250000000000),(-2408913/12500000000000)⟩
def e222 : ℝ := (1102557/12500000000000)
theorem h222 : Model (fun x => f222 ((91/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(96920661022547/10000000000000),(745039928909/50000000000000),(235676419/50000000000000),(-12173123/50000000000000)⟩
def e223 : ℝ := (11187457/100000000000000)
theorem h223 : Model (fun x => f223 ((91/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(106920661022547/10000000000000),(745039928909/50000000000000),(235676419/50000000000000),(-12173123/50000000000000)⟩
def e224 : ℝ := (11187457/100000000000000)
theorem h224 : Model (fun x => f224 ((91/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(22367620176609477/100000000000000),(78134422358419/50000000000000),(490556083361/100000000000000),(-820520031/50000000000000)⟩
def e225 : ℝ := (1193238473/100000000000000)
theorem h225 : Model (fun x => f225 ((91/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(223537415269/50000000000000),(-3123437663/100000000000000),(12016509/100000000000000),(347/2000000000000)⟩
def e226 : ℝ := (3101/12500000000000)
theorem h226 : Model (fun x => f226 ((91/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (22210857941530743/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(6647493095177/100000000000000),(13753408339/10000000000000),(-7101399/10000000000000),(-2199681/100000000000000)⟩
def e227 : ℝ := (1848691/100000000000000)
theorem h227 : Model (fun x => f227 ((91/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(1376854434351/10000000000000),(2307579627/781250000000),(16117947/20000000000000),(-922529/20000000000000)⟩
def e228 : ℝ := (25073/1000000000000)
theorem h228 : Model (fun x => f228 ((91/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(252369331719/1562500000000),(140226404319/50000000000000),(-357357787/50000000000000),(1930739/100000000000000)⟩
def e229 : ℝ := (682373/3125000000000)
theorem h229 : Model (fun x => f229 ((91/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3549810380223/50000000000000),(22629074643/50000000000000),(-50718937/6250000000000),(9766291/100000000000000)⟩
def e230 : ℝ := (501137/5000000000000)
theorem h230 : Model (fun x => f230 ((91/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-154862102020329/100000000000000),(-20658451363/2500000000000),(839301873/5000000000000),(-108375301/50000000000000)⟩
def e231 : ℝ := (26532019/100000000000000)
theorem h231 : Model (fun x => f231 ((91/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((91/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-8281/320),(-91/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((91/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1911/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((91/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7007/320),(-7/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((91/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((91/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15327/320),(-7/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((91/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((91/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(383175/32),(-175/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((91/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13559/1600),(29/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((91/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23159/1600),(29/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((91/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((91/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4377051/1600),(5481/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((91/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(36554291919/100000000000000),(-91547517/100000000000000),(1807679/100000000000000),(-8481/100000000000000)⟩
def e244 : ℝ := (103/100000000000000)
theorem h244 : Model (fun x => f244 ((91/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (43659/16))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(437709087689463/100000000000000),(-748011281221/50000000000000),(-5911195819/100000000000000),(-49803341/100000000000000)⟩
def e245 : ℝ := (640167/25000000000000)
theorem h245 : Model (fun x => f245 ((91/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(819/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((91/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(73801/1600),(451/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((91/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(107401/1600),(451/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((91/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(29241/1600),(171/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((91/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3140512641/2560000),(15776631/640000),(222563/1280000),(311/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((91/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((91/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(154449/160),(1179/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((91/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(103594066649/100000000000000),(-395397201/25000000000000),(3621959/20000000000000),(-46081/25000000000000)⟩
def e253 : ℝ := (9/500000000000)
theorem h253 : Model (fun x => f253 ((91/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (76041/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(31771335531619/25000000000000),(61346164899/10000000000000),(620679847/50000000000000),(-2179867/50000000000000)⟩
def e254 : ℝ := (448073/10000000000000)
theorem h254 : Model (fun x => f254 ((91/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(56771335531619/25000000000000),(61346164899/10000000000000),(620679847/50000000000000),(-2179867/50000000000000)⟩
def e255 : ℝ := (448073/10000000000000)
theorem h255 : Model (fun x => f255 ((91/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(56771335531619/50000000000000),(61346164899/20000000000000),(620679847/100000000000000),(-2179867/100000000000000)⟩
def e256 : ℝ := (448073/20000000000000)
theorem h256 : Model (fun x => f256 ((91/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(6771335531619/50000000000000),(61346164899/20000000000000),(620679847/100000000000000),(-2179867/100000000000000)⟩
def e257 : ℝ := (448073/20000000000000)
theorem h257 : Model (fun x => f257 ((91/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(419026524161949/100000000000000),(1131982804683/100000000000000),(2290604197/100000000000000),(-2011187/25000000000000)⟩
def e258 : ℝ := (8268017/100000000000000)
theorem h258 : Model (fun x => f258 ((91/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1387370404938117/50000000000000),(1131982804683/100000000000000),(2290604197/100000000000000),(-2011187/25000000000000)⟩
def e259 : ℝ := (4134009/50000000000000)
theorem h259 : Model (fun x => f259 ((91/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1575257415307599/50000000000000),(4898134438073/50000000000000),(2911901299/12500000000000),(-55567903/100000000000000)⟩
def e260 : ℝ := (7163811/10000000000000)
theorem h260 : Model (fun x => f260 ((91/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(168657915659923/2000000000000),(4898134438073/50000000000000),(2911901299/12500000000000),(-55567903/100000000000000)⟩
def e261 : ℝ := (71638111/100000000000000)
theorem h261 : Model (fun x => f261 ((91/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(9574935119992987/100000000000000),(73978472221/200000000000),(21767893009/20000000000000),(-114662137/100000000000000)⟩
def e262 : ℝ := (67736977/25000000000000)
theorem h262 : Model (fun x => f262 ((91/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7421991369520303/50000000000000),(73978472221/200000000000),(21767893009/20000000000000),(-114662137/100000000000000)⟩
def e263 : ℝ := (270947909/100000000000000)
theorem h263 : Model (fun x => f263 ((91/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(16854254494072701/100000000000000),(5470602333069/6250000000000),(20573139627/6250000000000),(27414847/25000000000000)⟩
def e264 : ℝ := (642350361/100000000000000)
theorem h264 : Model (fun x => f264 ((91/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(9594984389893493/50000000000000),(5470602333069/6250000000000),(20573139627/6250000000000),(27414847/25000000000000)⟩
def e265 : ℝ := (321175181/50000000000000)
theorem h265 : Model (fun x => f265 ((91/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(5447200782192901/25000000000000),(158245037654003/100000000000000),(761337323183/100000000000000),(1259139793/100000000000000)⟩
def e266 : ℝ := (145460961/12500000000000)
theorem h266 : Model (fun x => f266 ((91/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(5547796020288139/25000000000000),(158245037654003/100000000000000),(761337323183/100000000000000),(1259139793/100000000000000)⟩
def e267 : ℝ := (1163687689/100000000000000)
theorem h267 : Model (fun x => f267 ((91/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(629911578657517/2500000000000),(15483927779669/6250000000000),(185945656083/12500000000000),(106584349/2500000000000)⟩
def e268 : ℝ := (1830731537/100000000000000)
theorem h268 : Model (fun x => f268 ((91/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(786838878083801/3125000000000),(15483927779669/6250000000000),(185945656083/12500000000000),(106584349/2500000000000)⟩
def e269 : ℝ := (915365769/50000000000000)
theorem h269 : Model (fun x => f269 ((91/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(14294366066245799/50000000000000),(358525119086819/100000000000000),(1302602498827/50000000000000),(5196197209/50000000000000)⟩
def e270 : ℝ := (1335442911/50000000000000)
theorem h270 : Model (fun x => f270 ((91/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(28592065465824931/100000000000000),(358525119086819/100000000000000),(1302602498827/50000000000000),(5196197209/50000000000000)⟩
def e271 : ℝ := (2670885823/100000000000000)
theorem h271 : Model (fun x => f271 ((91/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1936064688111169/50000000000000),(27250911140097/20000000000000),(1629986585339/100000000000000),(11000398721/100000000000000)⟩
def e272 : ℝ := (33087973/3125000000000)
theorem h272 : Model (fun x => f272 ((91/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(64459690760873/50000000000000),(696540742211/100000000000000),(2350310941/100000000000000),(-571263/50000000000000)⟩
def e273 : ℝ := (2555431/50000000000000)
theorem h273 : Model (fun x => f273 ((91/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(106771335531619/50000000000000),(61346164899/20000000000000),(620679847/100000000000000),(-2179867/100000000000000)⟩
def e274 : ℝ := (448073/20000000000000)
theorem h274 : Model (fun x => f274 ((91/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(228002361824111/50000000000000),(1310002391201/100000000000000),(718334127/20000000000000),(-275113/5000000000000)⟩
def e275 : ℝ := (1198949/12500000000000)
theorem h275 : Model (fun x => f275 ((91/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(19475293341059/2000000000000),(839224229149/20000000000000),(7259129983/50000000000000),(-158893/6250000000000)⟩
def e276 : ℝ := (7695119/25000000000000)
theorem h276 : Model (fun x => f276 ((91/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(415880615978983/20000000000000),(2389469113513/20000000000000),(12479359539/25000000000000),(10980203/25000000000000)⟩
def e277 : ℝ := (87743763/100000000000000)
theorem h277 : Model (fun x => f277 ((91/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1340376794972331/50000000000000),(7471583415057/25000000000000),(196443820127/100000000000000),(330679891/50000000000000)⟩
def e278 : ℝ := (1734091/781250000000)
theorem h278 : Model (fun x => f278 ((91/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(56771335531619/6250000000000),(61346164899/2500000000000),(620679847/12500000000000),(-2179867/12500000000000)⟩
def e279 : ℝ := (448073/2500000000000)
theorem h279 : Model (fun x => f279 ((91/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(20745215000553/2000000000000),(3150387338171/100000000000000),(7315749717/100000000000000),(-9290731/50000000000000)⟩
def e280 : ℝ := (11516891/50000000000000)
theorem h280 : Model (fun x => f280 ((91/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(22745215000553/2000000000000),(3150387338171/100000000000000),(7315749717/100000000000000),(-9290731/50000000000000)⟩
def e281 : ℝ := (11516891/50000000000000)
theorem h281 : Model (fun x => f281 ((91/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(3810894797924727/12500000000000),(53042458000657/12500000000000),(842932739201/25000000000000),(15398412613/100000000000000)⟩
def e282 : ℝ := (1592694103/50000000000000)
theorem h282 : Model (fun x => f282 ((91/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(65601391079/20000000000000),(-4565409459/100000000000000),(1704269/6250000000000),(-8059/20000000000000)⟩
def e283 : ℝ := (2213/6250000000000)
theorem h283 : Model (fun x => f283 ((91/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (30059428404634937/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(6350426837951/50000000000000),(270145858933/100000000000000),(181755007/100000000000000),(-2739457/100000000000000)⟩
def e284 : ℝ := (2528241/50000000000000)
theorem h284 : Model (fun x => f284 ((91/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(31771335531619/12500000000000),(61346164899/5000000000000),(620679847/25000000000000),(-2179867/25000000000000)⟩
def e285 : ℝ := (448073/5000000000000)
theorem h285 : Model (fun x => f285 ((91/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(22018153849909/50000000000000),(-118962261871/100000000000000),(201619/250000000000),(1277877/100000000000000)⟩
def e286 : ℝ := (879817/100000000000000)
theorem h286 : Model (fun x => f286 ((91/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (14154414392333/6250000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(55963692300181/50000000000000),(118962261869/50000000000000),(-161295201/100000000000000),(-1277879/50000000000000)⟩
def e287 : ℝ := (6232099/100000000000000)
theorem h287 : Model (fun x => f287 ((91/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(5963692300181/50000000000000),(118962261869/50000000000000),(-161295201/100000000000000),(-1277879/50000000000000)⟩
def e288 : ℝ := (6232099/100000000000000)
theorem h288 : Model (fun x => f288 ((91/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(413065347929907/100000000000000),(175610957997/20000000000000),(-595256099/100000000000000),(-1886393/20000000000000)⟩
def e289 : ℝ := (4599883/20000000000000)
theorem h289 : Model (fun x => f289 ((91/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(86524363551381/3125000000000),(175610957997/20000000000000),(-595256099/100000000000000),(-1886393/20000000000000)⟩
def e290 : ℝ := (2874927/12500000000000)
theorem h290 : Model (fun x => f290 ((91/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(774755657321357/25000000000000),(7570389518491/100000000000000),(-1521527791/50000000000000),(-4207639/5000000000000)⟩
def e291 : ℝ := (198449207/100000000000000)
theorem h291 : Model (fun x => f291 ((91/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(419070179083319/5000000000000),(7570389518491/100000000000000),(-1521527791/50000000000000),(-4207639/5000000000000)⟩
def e292 : ℝ := (24806151/12500000000000)
theorem h292 : Model (fun x => f292 ((91/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(2345271455440061/25000000000000),(14207376773173/50000000000000),(67937433/6250000000000),(-327849249/100000000000000)⟩
def e293 : ℝ := (372894937/50000000000000)
theorem h293 : Model (fun x => f293 ((91/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14650133440807863/100000000000000),(14207376773173/50000000000000),(67937433/6250000000000),(-327849249/100000000000000)⟩
def e294 : ℝ := (5966319/800000000000)
theorem h294 : Model (fun x => f294 ((91/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(16397511200759263/100000000000000),(66660150701087/100000000000000),(45192354337/100000000000000),(-156924089/20000000000000)⟩
def e295 : ℝ := (876404521/50000000000000)
theorem h295 : Model (fun x => f295 ((91/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(4683306371618387/25000000000000),(66660150701087/100000000000000),(45192354337/100000000000000),(-156924089/20000000000000)⟩
def e296 : ℝ := (1752809043/100000000000000)
theorem h296 : Model (fun x => f296 ((91/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(20967609338298283/100000000000000),(29795475192461/25000000000000),(1431741381/800000000000),(-1356976983/100000000000000)⟩
def e297 : ℝ := (628264103/20000000000000)
theorem h297 : Model (fun x => f297 ((91/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(4273998058135847/20000000000000),(29795475192461/25000000000000),(1431741381/800000000000),(-1356976983/100000000000000)⟩
def e298 : ℝ := (785330129/25000000000000)
theorem h298 : Model (fun x => f298 ((91/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(5979717805427141/25000000000000),(2303020400883/1250000000000),(112352009061/25000000000000),(-1831420787/100000000000000)⟩
def e299 : ℝ := (1217320151/25000000000000)
theorem h299 : Model (fun x => f299 ((91/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(5975313043522379/25000000000000),(2303020400883/1250000000000),(112352009061/25000000000000),(-1831420787/100000000000000)⟩
def e300 : ℝ := (973856121/20000000000000)
theorem h300 : Model (fun x => f300 ((91/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(6688011611298889/25000000000000),(263083780524309/100000000000000),(902815114047/100000000000000),(-944320267/50000000000000)⟩
def e301 : ℝ := (697251149/10000000000000)
theorem h301 : Model (fun x => f301 ((91/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(26755379778528889/100000000000000),(263083780524309/100000000000000),(902815114047/100000000000000),(-944320267/50000000000000)⟩
def e302 : ℝ := (6972511491/100000000000000)
theorem h302 : Model (fun x => f302 ((91/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(3191217047472623/100000000000000),(11879578029583/12500000000000),(345233959567/50000000000000),(203652217/25000000000000)⟩
def e303 : ℝ := (508961363/20000000000000)
theorem h303 : Model (fun x => f303 ((91/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(125277394234773/100000000000000),(106521078697/20000000000000),(20501379/10000000000000),(-1622177/25000000000000)⟩
def e304 : ℝ := (13992439/100000000000000)
theorem h304 : Model (fun x => f304 ((91/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(105963692300181/50000000000000),(118962261869/50000000000000),(-161295201/100000000000000),(-1277879/50000000000000)⟩
def e305 : ℝ := (6232099/100000000000000)
theorem h305 : Model (fun x => f305 ((91/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(449132163435497/100000000000000),(1008454440961/100000000000000),(-29394153/25000000000000),(-362507/3125000000000)⟩
def e306 : ℝ := (26456637/100000000000000)
theorem h306 : Model (fun x => f306 ((91/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(14872406990123/1562500000000),(1602893341211/50000000000000),(1425754761/100000000000000),(-7593823/20000000000000)⟩
def e307 : ℝ := (21059569/25000000000000)
theorem h307 : Model (fun x => f307 ((91/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(2017197002322501/100000000000000),(9058586495899/100000000000000),(569603427/6250000000000),(-13321511/12500000000000)⟩
def e308 : ℝ := (11920913/5000000000000)
theorem h308 : Model (fun x => f308 ((91/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1263545920545791/50000000000000),(2761507643519/12500000000000),(63799401569/100000000000000),(-19728959/10000000000000)⟩
def e309 : ℝ := (584615947/100000000000000)
theorem h309 : Model (fun x => f309 ((91/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(55963692300181/6250000000000),(118962261869/6250000000000),(-161295201/12500000000000),(-1277879/6250000000000)⟩
def e310 : ℝ := (6232099/12500000000000)
theorem h310 : Model (fun x => f310 ((91/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1020696471037669/100000000000000),(2436001583389/100000000000000),(-542673909/50000000000000),(-6733693/25000000000000)⟩
def e311 : ℝ := (63849231/100000000000000)
theorem h311 : Model (fun x => f311 ((91/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1120696471037669/100000000000000),(2436001583389/100000000000000),(-542673909/50000000000000),(-6733693/25000000000000)⟩
def e312 : ℝ := (63849231/100000000000000)
theorem h312 : Model (fun x => f312 ((91/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(28321029082994217/100000000000000),(77286236732377/25000000000000),(1225732865143/100000000000000),(-157730517/10000000000000)⟩
def e313 : ℝ := (2051289391/25000000000000)
theorem h313 : Model (fun x => f313 ((91/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(176547256999/50000000000000),(-1927143687/50000000000000),(13395239/50000000000000),(-2649/2500000000000)⟩
def e314 : ℝ := (52399/50000000000000)
theorem h314 : Model (fun x => f314 ((91/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (437666384699013/1562500000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(5634006162197/50000000000000),(21257043073/10000000000000),(-74007593/20000000000000),(-1656927/100000000000000)⟩
def e315 : ℝ := (12582397/100000000000000)
theorem h315 : Model (fun x => f315 ((91/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(2996108250037/12500000000000),(482716289663/100000000000000),(-94141479/50000000000000),(-137387/3125000000000)⟩
def e316 : ℝ := (17638879/100000000000000)
theorem h316 : Model (fun x => f316 ((91/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(20982780939881/20000000000000),(877156712143/50000000000000),(-9462522829/100000000000000),(-28449109/50000000000000)⟩
def e317 : ℝ := (15652381/20000000000000)
theorem h317 : Model (fun x => f317 ((91/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(46116002065671/100000000000000),(66089381609/25000000000000),(-7064378459/100000000000000),(26310163/50000000000000)⟩
def e318 : ℝ := (36727737/100000000000000)
theorem h318 : Model (fun x => f318 ((91/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-54373049977329/50000000000000),(-140495132021/25000000000000),(9721659001/100000000000000),(-41032569/25000000000000)⟩
def e319 : ℝ := (15814939/25000000000000)
theorem h319 : Model (fun x => f319 ((91/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((91/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-91091/1600),(-1001/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((91/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((91/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(8827/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((91/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(261989/1600),(939/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((91/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((91/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(434789/1600),(939/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((91/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2173945/32),(4695/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((91/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((91/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(211903070356261051/20000000000000),(2653477715070413/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (137133/100000000000000)
theorem h329 : Model (fun x => f329 ((91/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9438277589/100000000000000),(-5909367/25000000000000),(23337/5000000000000),(-219/10000000000000)⟩
def e330 : ℝ := (29/100000000000000)
theorem h330 : Model (fun x => f330 ((91/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (132102015556290079/12500000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(641196761663081/100000000000000),(116371472467/10000000000000),(4275093709/50000000000000),(5761311/20000000000000)⟩
def e331 : ℝ := (3427301/100000000000000)
theorem h331 : Model (fun x => f331 ((91/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((91/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(451/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((91/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((91/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((91/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(705806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((91/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((91/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((91/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3131305376641327/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1067/100000000000000)
theorem h339 : Model (fun x => f339 ((91/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3804193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((91/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((91/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((91/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1071847311679207/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1067/100000000000000)
theorem h343 : Model (fun x => f343 ((91/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2332421766383/50000000000000),(-6131186191/100000000000000),(8058457/100000000000000),(-331/3125000000000)⟩
def e344 : ℝ := (19/100000000000000)
theorem h344 : Model (fun x => f344 ((91/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1070438540861433/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(73035248176703/50000000000000),(842790811621/100000000000000),(-1107712927/100000000000000),(181987/12500000000000)⟩
def e345 : ℝ := (3001/100000000000000)
theorem h345 : Model (fun x => f345 ((91/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(123035248176703/50000000000000),(842790811621/100000000000000),(-1107712927/100000000000000),(181987/12500000000000)⟩
def e346 : ℝ := (3001/100000000000000)
theorem h346 : Model (fun x => f346 ((91/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(123035248176703/100000000000000),(42139540581/10000000000000),(-34616029/6250000000000),(181987/25000000000000)⟩
def e347 : ℝ := (751/50000000000000)
theorem h347 : Model (fun x => f347 ((91/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(23035248176703/100000000000000),(42139540581/10000000000000),(-34616029/6250000000000),(181987/25000000000000)⟩
def e348 : ℝ := (751/50000000000000)
theorem h348 : Model (fun x => f348 ((91/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(454058653985451/100000000000000),(1555149711917/100000000000000),(-1021997047/50000000000000),(1343237/50000000000000)⟩
def e349 : ℝ := (2773/50000000000000)
theorem h349 : Model (fun x => f349 ((91/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(351221617462467/12500000000000),(1555149711917/100000000000000),(-1021997047/50000000000000),(1343237/50000000000000)⟩
def e350 : ℝ := (5547/100000000000000)
theorem h350 : Model (fun x => f350 ((91/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3457011109561413/100000000000000),(13753636389163/100000000000000),(-5761806409/50000000000000),(6532401/100000000000000)⟩
def e351 : ℝ := (8307/10000000000000)
theorem h351 : Model (fun x => f351 ((91/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(1747878412388473/20000000000000),(13753636389163/100000000000000),(-5761806409/50000000000000),(6532401/100000000000000)⟩
def e352 : ℝ := (83071/100000000000000)
theorem h352 : Model (fun x => f352 ((91/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1075253271254587/10000000000000),(13437304327369/25000000000000),(-1156150401/25000000000000),(-26539997/50000000000000)⟩
def e353 : ℝ := (425623/100000000000000)
theorem h353 : Model (fun x => f353 ((91/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(16021580331593489/100000000000000),(13437304327369/25000000000000),(-1156150401/25000000000000),(-26539997/50000000000000)⟩
def e354 : ℝ := (53203/12500000000000)
theorem h354 : Model (fun x => f354 ((91/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(4928047780701471/25000000000000),(66822343182621/50000000000000),(66035142019/50000000000000),(-132929851/50000000000000)⟩
def e355 : ℝ := (480191/50000000000000)
theorem h355 : Model (fun x => f355 ((91/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(22047905408520169/100000000000000),(66822343182621/50000000000000),(66035142019/50000000000000),(-132929851/50000000000000)⟩
def e356 : ℝ := (960383/100000000000000)
theorem h356 : Model (fun x => f356 ((91/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(27126695137137513/100000000000000),(25733893201329/10000000000000),(75443977613/12500000000000),(-350265483/100000000000000)⟩
def e357 : ℝ := (480041/20000000000000)
theorem h357 : Model (fun x => f357 ((91/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(5505815217903693/20000000000000),(25733893201329/10000000000000),(75443977613/12500000000000),(-350265483/100000000000000)⟩
def e358 : ℝ := (1200103/50000000000000)
theorem h358 : Model (fun x => f358 ((91/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(1058452096484139/3125000000000),(216311927780499/50000000000000),(1674524350187/100000000000000),(13867167/1562500000000)⟩
def e359 : ℝ := (3166223/50000000000000)
theorem h359 : Model (fun x => f359 ((91/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(169264240199367/500000000000),(216311927780499/50000000000000),(1674524350187/100000000000000),(13867167/1562500000000)⟩
def e360 : ℝ := (6332447/100000000000000)
theorem h360 : Model (fun x => f360 ((91/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(20825467800370187/50000000000000),(337467090368481/50000000000000),(3695816054687/100000000000000),(1199724167/20000000000000)⟩
def e361 : ℝ := (10725443/100000000000000)
theorem h361 : Model (fun x => f361 ((91/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(41654268934073707/100000000000000),(337467090368481/50000000000000),(3695816054687/100000000000000),(1199724167/20000000000000)⟩
def e362 : ℝ := (2681361/25000000000000)
theorem h362 : Model (fun x => f362 ((91/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(9595164225155177/100000000000000),(66200387834817/20000000000000),(692955433839/20000000000000),(845053193/6250000000000)⟩
def e363 : ℝ := (12879661/100000000000000)
theorem h363 : Model (fun x => f363 ((91/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(37844180734757/25000000000000),(1036929766687/100000000000000),(41286353/10000000000000),(-2876587/100000000000000)⟩
def e364 : ℝ := (6461/50000000000000)
theorem h364 : Model (fun x => f364 ((91/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(223035248176703/100000000000000),(42139540581/10000000000000),(-34616029/6250000000000),(181987/25000000000000)⟩
def e365 : ℝ := (751/50000000000000)
theorem h365 : Model (fun x => f365 ((91/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(248723609646217/50000000000000),(1879720578307/100000000000000),(-347424699/50000000000000),(-1420691/100000000000000)⟩
def e366 : ℝ := (7963/50000000000000)
theorem h366 : Model (fun x => f366 ((91/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(277370660024247/25000000000000),(6288659185283/100000000000000),(7232307/200000000000),(-6443251/50000000000000)⟩
def e367 : ℝ := (27319/50000000000000)
theorem h367 : Model (fun x => f367 ((91/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2474537359817753/100000000000000),(18701235494511/100000000000000),(28420476507/100000000000000),(-20128413/50000000000000)⟩
def e368 : ℝ := (33501/20000000000000)
theorem h368 : Model (fun x => f368 ((91/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1872936781597029/50000000000000),(53968531912441/100000000000000),(49431425171/20000000000000),(239789277/100000000000000)⟩
def e369 : ℝ := (354131/25000000000000)
theorem h369 : Model (fun x => f369 ((91/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(123035248176703/12500000000000),(42139540581/1250000000000),(-34616029/781250000000),(181987/3125000000000)⟩
def e370 : ℝ := (751/6250000000000)
theorem h370 : Model (fun x => f370 ((91/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(283914677088163/25000000000000),(4408093013167/100000000000000),(-2008994091/50000000000000),(2946997/100000000000000)⟩
def e371 : ℝ := (12469/50000000000000)
theorem h371 : Model (fun x => f371 ((91/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(308914677088163/25000000000000),(4408093013167/100000000000000),(-2008994091/50000000000000),(2946997/100000000000000)⟩
def e372 : ℝ := (12469/50000000000000)
theorem h372 : Model (fun x => f372 ((91/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(23143106443743579/50000000000000),(103998556895923/12500000000000),(13206232191/250000000000),(5899917313/50000000000000)⟩
def e373 : ℝ := (20745769/100000000000000)
theorem h373 : Model (fun x => f373 ((91/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(1080235277/500000000000),(-1941708391/50000000000000),(11286789/25000000000000),(-42339/10000000000000)⟩
def e374 : ℝ := (913/25000000000000)
theorem h374 : Model (fun x => f374 ((91/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (45448930118862979/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(20730069769241/100000000000000),(171249862561/50000000000000),(-259173011/25000000000000),(1736329/50000000000000)⟩
def e375 : ℝ := (9523/1250000000000)
theorem h375 : Model (fun x => f375 ((91/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(73035248176703/25000000000000),(842790811621/50000000000000),(-1107712927/50000000000000),(181987/6250000000000)⟩
def e376 : ℝ := (3001/50000000000000)
theorem h376 : Model (fun x => f376 ((91/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(5079845079049/12500000000000),(-17398456217/12500000000000),(659657111/100000000000000),(-625267/20000000000000)⟩
def e377 : ℝ := (1507/10000000000000)
theorem h377 : Model (fun x => f377 ((91/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (245226596369961/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(23744495747043/20000000000000),(69593824867/25000000000000),(-82457139/6250000000000),(1563167/25000000000000)⟩
def e378 : ℝ := (118183/100000000000000)
theorem h378 : Model (fun x => f378 ((91/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(3744495747043/20000000000000),(69593824867/25000000000000),(-82457139/6250000000000),(1563167/25000000000000)⟩
def e379 : ℝ := (118183/100000000000000)
theorem h379 : Model (fun x => f379 ((91/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(219071240523313/50000000000000),(1027337414703/100000000000000),(-1217224433/25000000000000),(11537661/50000000000000)⟩
def e380 : ℝ := (218077/50000000000000)
theorem h380 : Model (fun x => f380 ((91/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2793856766760911/100000000000000),(1027337414703/100000000000000),(-1217224433/25000000000000),(11537661/50000000000000)⟩
def e381 : ℝ := (87231/20000000000000)
theorem h381 : Model (fun x => f381 ((91/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3316936005810087/100000000000000),(8997087584887/100000000000000),(-1243136631/3125000000000),(43744641/25000000000000)⟩
def e382 : ℝ := (4015439/100000000000000)
theorem h382 : Model (fun x => f382 ((91/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8599316958191039/100000000000000),(8997087584887/100000000000000),(-1243136631/3125000000000),(43744641/25000000000000)⟩
def e383 : ℝ := (50193/1250000000000)
theorem h383 : Model (fun x => f383 ((91/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(10209322247062093/100000000000000),(17309969864661/50000000000000),(-27126917241/20000000000000),(515987041/100000000000000)⟩
def e384 : ℝ := (3306273/20000000000000)
theorem h384 : Model (fun x => f384 ((91/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(967398116631857/6250000000000),(17309969864661/50000000000000),(-27126917241/20000000000000),(515987041/100000000000000)⟩
def e385 : ℝ := (8265683/50000000000000)
theorem h385 : Model (fun x => f385 ((91/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(18376304372850029/100000000000000),(21047402262709/25000000000000),(-53772743431/20000000000000),(746084709/100000000000000)⟩
def e386 : ℝ := (43412383/100000000000000)
theorem h386 : Model (fun x => f386 ((91/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(10356009329282157/50000000000000),(21047402262709/25000000000000),(-53772743431/20000000000000),(746084709/100000000000000)⟩
def e387 : ℝ := (1356637/3125000000000)
theorem h387 : Model (fun x => f387 ((91/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(1229491097377389/5000000000000),(31521826933857/20000000000000),(-7161904027/2000000000000),(321648357/100000000000000)⟩
def e388 : ℝ := (43577229/50000000000000)
theorem h388 : Model (fun x => f388 ((91/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(6248050724982183/25000000000000),(31521826933857/20000000000000),(-7161904027/2000000000000),(321648357/100000000000000)⟩
def e389 : ℝ := (87154459/100000000000000)
theorem h389 : Model (fun x => f389 ((91/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(1186854510933187/4000000000000),(10267583642353/4000000000000),(-197575179/62500000000),(-565829973/50000000000000)⟩
def e390 : ℝ := (74470077/50000000000000)
theorem h390 : Model (fun x => f390 ((91/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(29653743725710627/100000000000000),(10267583642353/4000000000000),(-197575179/62500000000),(-565829973/50000000000000)⟩
def e391 : ℝ := (29788031/20000000000000)
theorem h391 : Model (fun x => f391 ((91/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(35205659588951951/100000000000000),(96824235765061/25000000000000),(-12992870227/25000000000000),(-150237107/4000000000000)⟩
def e392 : ℝ := (57416667/25000000000000)
theorem h392 : Model (fun x => f392 ((91/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(8802248230571321/25000000000000),(96824235765061/25000000000000),(-12992870227/25000000000000),(-150237107/4000000000000)⟩
def e393 : ℝ := (229666669/100000000000000)
theorem h393 : Model (fun x => f393 ((91/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(823999526594777/12500000000000),(17052472729367/10000000000000),(301945711931/50000000000000),(-234752547/6250000000000)⟩
def e394 : ℝ := (100203527/100000000000000)
theorem h394 : Model (fun x => f394 ((91/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(28190053914067/20000000000000),(660988111429/100000000000000),(-94308681/4000000000000),(1500271/20000000000000)⟩
def e395 : ℝ := (166833/50000000000000)
theorem h395 : Model (fun x => f395 ((91/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(43744495747043/20000000000000),(69593824867/25000000000000),(-82457139/6250000000000),(1563167/25000000000000)⟩
def e396 : ℝ := (118183/100000000000000)
theorem h396 : Model (fun x => f396 ((91/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(95679045408153/20000000000000),(243547742073/20000000000000),(-4996345473/100000000000000),(20006691/100000000000000)⟩
def e397 : ℝ := (35627/6250000000000)
theorem h397 : Model (fun x => f397 ((91/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(26158947468363/2500000000000),(3995202437743/100000000000000),(-13849783161/100000000000000),(10924301/25000000000000)⟩
def e398 : ℝ := (1006771/50000000000000)
theorem h398 : Model (fun x => f398 ((91/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2288619932553853/100000000000000),(1165120773643/10000000000000),(-32975680871/100000000000000),(69737243/100000000000000)⟩
def e399 : ℝ := (248267/4000000000000)
theorem h399 : Model (fun x => f399 ((91/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1612907982187537/50000000000000),(31549914382673/100000000000000),(-5856348723/25000000000000),(-222695501/100000000000000)⟩
def e400 : ℝ := (9290691/50000000000000)
theorem h400 : Model (fun x => f400 ((91/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(23744495747043/2500000000000),(69593824867/3125000000000),(-82457139/781250000000),(1563167/3125000000000)⟩
def e401 : ℝ := (118183/12500000000000)
theorem h401 : Model (fun x => f401 ((91/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(218146019890411/20000000000000),(2887990507173/100000000000000),(-12912230817/100000000000000),(57522699/100000000000000)⟩
def e402 : ℝ := (127913/10000000000000)
theorem h402 : Model (fun x => f402 ((91/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(238146019890411/20000000000000),(2887990507173/100000000000000),(-12912230817/100000000000000),(57522699/100000000000000)⟩
def e403 : ℝ := (127913/10000000000000)
theorem h403 : Model (fun x => f403 ((91/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(7682152328148717/20000000000000),(468835585735863/100000000000000),(107850250723/50000000000000),(-2773223451/50000000000000)⟩
def e404 : ℝ := (278216483/100000000000000)
theorem h404 : Model (fun x => f404 ((91/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(260343705067/100000000000000),(-3177713439/100000000000000),(18662333/50000000000000),(-400141/100000000000000)⟩
def e405 : ℝ := (621/10000000000000)
theorem h405 : Model (fun x => f405 ((91/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (37941704529842891/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(17161847178171/100000000000000),(11723782177/5000000000000),(-13861533/1000000000000),(166039/2000000000000)⟩
def e406 : ℝ := (32047/3125000000000)
theorem h406 : Model (fun x => f406 ((91/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(9472979236853/25000000000000),(288487684331/50000000000000),(-75713917/3125000000000),(735913/6250000000000)⟩
def e407 : ℝ := (111709/6250000000000)
theorem h407 : Model (fun x => f407 ((91/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(242961744398869/100000000000000),(4140501196431/100000000000000),(-697628581/12500000000000),(26887807/25000000000000)⟩
def e408 : ℝ := (12896259/100000000000000)
theorem h408 : Model (fun x => f408 ((91/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(21359274232867/20000000000000),(64641402959/10000000000000),(-9556650283/100000000000000),(76146699/50000000000000)⟩
def e409 : ℝ := (10573173/100000000000000)
theorem h409 : Model (fun x => f409 ((91/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1949728790323/100000000000000),(42216750753/50000000000000),(82504359/50000000000000),(-5918439/50000000000000)⟩
def e410 : ℝ := (73832929/100000000000000)
theorem h410 : Model (fun x => f410 ((91/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(8772773331054687/100000000000000),(113146036376953/25000000000000),(190463/2048000),(9737/10240000)⟩
def e411 : ℝ := (484375001/100000000000000)
theorem h411 : Model (fun x => f411 ((91/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(44521/1600),(211/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((91/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(9393931/64000),(133563/64000),(633/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((91/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(10059915448067369/781250000000),(84738471234531297/100000000000000),(1198162198101409/50000000000000),(37978703113647/100000000000000)⟩
def e414 : ℝ := (185347264503/50000000000000)
theorem h414 : Model (fun x => f414 ((91/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(7765969843/100000000000000),(-255530079/50000000000000),(9589681/50000000000000),(-16879/3125000000000)⟩
def e415 : ℝ := (19063/100000000000000)
theorem h415 : Model (fun x => f415 ((91/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (18757750505066351/1562500000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1424979663449/25000000000000),(-6805101271/100000000000000),(-30659719/6250000000000),(1351451/12500000000000)⟩
def e416 : ℝ := (2695939/10000000000000)
theorem h416 : Model (fun x => f416 ((91/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(3750189863473/100000000000000),(15525680047/20000000000000),(-162773393/50000000000000),(-102527/10000000000000)⟩
def e417 : ℝ := (100792319/100000000000000)
theorem h417 : Model (fun x => f417 ((91/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((91/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((2812485416669/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (9/4) (23/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (9/4) (23/10) ≤ (1125054642059/600000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(91/40)-(1/40)) (by norm_num : ((91/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel25


noncomputable section
namespace Hf4Quad.Panel26
open Hf4Quad.Dag

def p0 : Cubic := ⟨(93/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((93/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((93/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((93/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((93/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(407428571428571/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((93/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-407428571428571/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((93/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-79/25),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((93/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((93/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(8649/1600),(93/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((93/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(327197619047619/50000000000000),(2814603174603/20000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((93/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-327197619047619/50000000000000),(-2814603174603/20000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((93/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-485197619047619/50000000000000),(-18453968253967/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((93/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((93/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(804357/64000),(25947/64000),(279/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((93/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(156730451/1280000),(5055821/1280000),(4247161458333/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((93/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-156730451/1280000),(-5055821/1280000),(-4247161458333/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((93/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-6607480861235119/50000000000000),(-413439983878967/100000000000000),(-2161411416997/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((93/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((93/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(74805201/2560000),(804357/640000),(25947/1280000),(93/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((93/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(8163265982142857/100000000000000),(175554107142857/50000000000000),(1132607142857/20000000000000),(8119047619/20000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((93/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-5051695740327381/100000000000000),(-62331769593253/100000000000000),(1340212880291/100000000000000),(2537243717/10000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((93/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((93/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(106153620803833/1562500000000),(91314942626953/25000000000000),(804357/10240000),(8649/10240000)⟩
def e22 : ℝ := (227539063/50000000000000)
theorem h22 : Model (fun x => f22 ((93/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(22130277806689451/50000000000000),(297449970520019/12500000000000),(25587094238281/50000000000000),(110052018229/20000000000000)⟩
def e23 : ℝ := (2964749721/100000000000000)
theorem h23 : Model (fun x => f23 ((93/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(39208859873051521/100000000000000),(2317267994566899/100000000000000),(52514401356853/100000000000000),(115126505663/20000000000000)⟩
def e24 : ℝ := (3073876713/100000000000000)
theorem h24 : Model (fun x => f24 ((93/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((93/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(315913175512207/2000000000000),(203814951943359/20000000000000),(5478896557617/20000000000000),(196376220703/50000000000000)⟩
def e26 : ℝ := (397625733/12500000000000)
theorem h26 : Model (fun x => f26 ((93/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(35469193568090119/100000000000000),(457667013781807/20000000000000),(61514383572821/100000000000000),(220481661551/25000000000000)⟩
def e27 : ℝ := (3571478543/50000000000000)
theorem h27 : Model (fun x => f27 ((93/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(1866951336028541/2500000000000),(2302801531737967/50000000000000),(57014392464837/50000000000000),(1457559174519/100000000000000)⟩
def e28 : ℝ := (10216833799/100000000000000)
theorem h28 : Model (fun x => f28 ((93/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((93/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(36724906653294063/100000000000000),(2764240285731807/100000000000000),(89169041475217/100000000000000),(1598011495971/100000000000000)⟩
def e30 : ℝ := (17294174817/100000000000000)
theorem h30 : Model (fun x => f30 ((93/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1742975728465861/20000000000000),(655958607487151/100000000000000),(2115995508023/10000000000000),(9480266613/2500000000000)⟩
def e31 : ℝ := (128247973/3125000000000)
theorem h31 : Model (fun x => f31 ((93/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(16678586416694189/20000000000000),(1052312334192617/20000000000000),(8449296250619/6250000000000),(1836769839039/100000000000000)⟩
def e32 : ℝ := (2864153787/20000000000000)
theorem h32 : Model (fun x => f32 ((93/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((93/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(3710421/320),(39897/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((93/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((93/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(205437/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((93/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(6997413/320),(57569/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((93/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((93/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(7727013/320),(57569/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((93/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-7727013/320),(-57569/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((93/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((93/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(133/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((93/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(17689/1600),(133/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((93/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((93/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(371469/160),(2793/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((93/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(43072234829/100000000000000),(-32385139/5000000000000),(3652459/50000000000000),(-73233/100000000000000)⟩
def e46 : ℝ := (353/50000000000000)
theorem h46 : Model (fun x => f46 ((93/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (182931/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-20801232403921/2000000000000),(35591271449/25000000000000),(-43497801/4000000000000),(8322459/100000000000000)⟩
def e47 : ℝ := (33957407/100000000000000)
theorem h47 : Model (fun x => f47 ((93/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((93/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(173/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((93/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((93/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((93/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(28833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((93/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(48833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((93/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((93/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(30520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((93/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((93/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(640937499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((93/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((93/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(5520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((93/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(141540364583323/25000000000000),(197102864583/1562500000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (31/25000000000000)
theorem h60 : Model (fun x => f60 ((93/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(74521701388887/50000000000000),(1017361111109/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((93/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((93/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(30520833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((93/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(684938368055547/50000000000000),(5184027777769/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((93/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(734938368055547/50000000000000),(5184027777769/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((93/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(8321875564868363/100000000000000),(2684609913009/1250000000000),(299916314017/25000000000000),(210901331/10000000000000)⟩
def e66 : ℝ := (158771/25000000000000)
theorem h66 : Model (fun x => f66 ((93/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(55520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((93/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(246605034722219/50000000000000),(1850694444441/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((93/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1095337362557849/100000000000000),(1541281467011/25000000000000),(11566840277/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (1/1562500000000)
theorem h69 : Model (fun x => f69 ((93/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(3646104493103009/4000000000000),(2865496936445679/100000000000000),(3417965780777/12500000000000),(24501126911/20000000000000)⟩
def e70 : ℝ := (18228407/6250000000000)
theorem h70 : Model (fun x => f70 ((93/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((93/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1564955729166627/6250000000000),(21364583333289/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((93/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(5529510243055081/100000000000000),(8879654947901/6250000000000),(776562499993/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1427/100000000000000)
theorem h73 : Model (fun x => f73 ((93/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(6056679165864563/10000000000000),(1897096119339953/100000000000000),(1119039955683/6250000000000),(78020968689/100000000000000)⟩
def e74 : ℝ := (175240709/100000000000000)
theorem h74 : Model (fun x => f74 ((93/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(30343880797244171/20000000000000),(148831032993301/3125000000000),(5656045692143/12500000000000),(50131650811/25000000000000)⟩
def e75 : ℝ := (466895221/100000000000000)
theorem h75 : Model (fun x => f75 ((93/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((93/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(521651909722209/6250000000000),(7121527777763/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((93/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(487673611111/10000000000000),(184027777777/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((93/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1076945891203/100000000000000),(15239800347/25000000000000),(1150173611/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((93/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(17977308186033/20000000000000),(2850738708709/50000000000000),(131775284117/100000000000000),(263661823/20000000000000)⟩
def e80 : ℝ := (5246773/100000000000000)
theorem h80 : Model (fun x => f80 ((93/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(9981151315787/5000000000000),(3259139587931/25000000000000),(158203549691/50000000000000),(347680851/10000000000000)⟩
def e81 : ℝ := (1716703/10000000000000)
theorem h81 : Model (fun x => f81 ((93/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(30383805402507319/20000000000000),(1193907403534339/25000000000000),(22782386318263/50000000000000),(102001705877/50000000000000)⟩
def e82 : ℝ := (484062251/100000000000000)
theorem h82 : Model (fun x => f82 ((93/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(237825550973/100000000000000),(8974549093/50000000000000),(1984349/390625000000),(6389853/100000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((93/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(52519809173/100000000000000),(2477349489/50000000000000),(46742443/25000000000000),(3527731/100000000000000)⟩
def e84 : ℝ := (33409/100000000000000)
theorem h84 : Model (fun x => f84 ((93/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(463924981/4000000000000),(1312995229/100000000000000),(61933737/100000000000000),(1558081/100000000000000)⟩
def e85 : ℝ := (11109/50000000000000)
theorem h85 : Model (fun x => f85 ((93/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(2561252499/100000000000000),(338278631/100000000000000),(19147847/100000000000000),(602133/100000000000000)⟩
def e86 : ℝ := (11493/100000000000000)
theorem h86 : Model (fun x => f86 ((93/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(7683757497/100000000000000),(1014835893/100000000000000),(57443541/100000000000000),(1806399/100000000000000)⟩
def e87 : ℝ := (34479/100000000000000)
theorem h87 : Model (fun x => f87 ((93/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-7683757497/100000000000000),(-1014835893/100000000000000),(-57443541/100000000000000),(-1806399/100000000000000)⟩
def e88 : ℝ := (34479/100000000000000)
theorem h88 : Model (fun x => f88 ((93/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(75959509664389549/50000000000000),(4775628599301463/100000000000000),(9112943038597/20000000000000),(40800321071/20000000000000)⟩
def e89 : ℝ := (48409673/10000000000000)
theorem h89 : Model (fun x => f89 ((93/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1564955729166627/5000000000000),(21364583333289/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((93/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(19460493808111/800000000000),(1140976419329/6250000000000),(25688024449/50000000000000),(64260223/100000000000000)⟩
def e91 : ℝ := (30329/100000000000000)
theorem h91 : Model (fun x => f91 ((93/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(152274056387074899/20000000000000),(10910915040552691/100000000000000),(31975670152907/50000000000000),(196432626419/100000000000000)⟩
def e92 : ℝ := (66889263/20000000000000)
theorem h92 : Model (fun x => f92 ((93/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(3283553429/25000000000000),(-23527693/12500000000000),(398531/25000000000000),(-1303/12500000000000)⟩
def e93 : ℝ := (9/12500000000000)
theorem h93 : Model (fun x => f93 ((93/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (93799402348430407/12500000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(19953368673893/100000000000000),(21331058919/6250000000000),(-291208633/50000000000000),(1324799/100000000000000)⟩
def e94 : ℝ := (10447/3125000000000)
theorem h94 : Model (fun x => f94 ((93/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(28833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((93/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(40955631399317/100000000000000),(-17472538993/12500000000000),(477065911/100000000000000),(-407053/25000000000000)⟩
def e96 : ℝ := (279/5000000000000)
theorem h96 : Model (fun x => f96 ((93/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (243333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(59044368600681/50000000000000),(279560623883/100000000000000),(-954131823/100000000000000),(162821/5000000000000)⟩
def e97 : ℝ := (21663/50000000000000)
theorem h97 : Model (fun x => f97 ((93/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1239931740614301/50000000000000),(5870773101543/100000000000000),(-20036768283/100000000000000),(3419241/5000000000000)⟩
def e98 : ℝ := (454923/50000000000000)
theorem h98 : Model (fun x => f98 ((93/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(9044368600681/50000000000000),(279560623883/100000000000000),(-954131823/100000000000000),(162821/5000000000000)⟩
def e99 : ℝ := (21663/50000000000000)
theorem h99 : Model (fun x => f99 ((93/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(112143997017997/25000000000000),(1598934107519/20000000000000),(-10873195091/100000000000000),(-18905109/100000000000000)⟩
def e100 : ℝ := (227369/12500000000000)
theorem h100 : Model (fun x => f100 ((93/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(139449498538123/100000000000000),(660259220911/100000000000000),(-735951509/50000000000000),(147261/6250000000000)⟩
def e101 : ℝ := (25989/20000000000000)
theorem h101 : Model (fun x => f101 ((93/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(59044368600681/5000000000000),(279560623883/10000000000000),(-954131823/10000000000000),(162821/500000000000)⟩
def e102 : ℝ := (21663/5000000000000)
theorem h102 : Model (fun x => f102 ((93/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1320336870551743/100000000000000),(3455865459741/100000000000000),(-86040791/781250000000),(4365047/12500000000000)⟩
def e103 : ℝ := (112641/20000000000000)
theorem h103 : Model (fun x => f103 ((93/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1420336870551743/100000000000000),(3455865459741/100000000000000),(-86040791/781250000000),(4365047/12500000000000)⟩
def e104 : ℝ := (112641/20000000000000)
theorem h104 : Model (fun x => f104 ((93/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(3185645075514117/50000000000000),(12905343595707/10000000000000),(18111598203/25000000000000),(-34202639/2500000000000)⟩
def e105 : ℝ := (7951861/25000000000000)
theorem h105 : Model (fun x => f105 ((93/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(109044368600681/50000000000000),(279560623883/100000000000000),(-954131823/100000000000000),(162821/5000000000000)⟩
def e106 : ℝ := (21663/50000000000000)
theorem h106 : Model (fun x => f106 ((93/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(475626972940847/100000000000000),(1219380468677/100000000000000),(-422520833/12500000000000),(1108627/12500000000000)⟩
def e107 : ℝ := (216597/100000000000000)
theorem h107 : Model (fun x => f107 ((93/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(259322214768939/25000000000000),(1994498599363/50000000000000),(-1700192691/20000000000000),(214791/1562500000000)⟩
def e108 : ℝ := (776533/100000000000000)
theorem h108 : Model (fun x => f108 ((93/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(66088682916006779/100000000000000),(796403749542187/50000000000000),(5357795259277/100000000000000),(-10698135051/50000000000000)⟩
def e109 : ℝ := (424802761/100000000000000)
theorem h109 : Model (fun x => f109 ((93/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2928439469300583/12500000000000),(13865443639131/12500000000000),(-15454981689/6250000000000),(3092481/781250000000)⟩
def e110 : ℝ := (545769/2500000000000)
theorem h110 : Model (fun x => f110 ((93/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(4237741757621939/100000000000000),(5347423656049/6250000000000),(20919703213/50000000000000),(-28598539/3125000000000)⟩
def e111 : ℝ := (10649241/50000000000000)
theorem h111 : Model (fun x => f111 ((93/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(87915246256427/200000000000),(42261403092369/4000000000000),(3404964747/97656250000),(-7257292001/50000000000000)⟩
def e112 : ℝ := (709337/250000000000)
theorem h112 : Model (fun x => f112 ((93/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(110046306044220279/100000000000000),(2649342576393599/100000000000000),(1768895832041/20000000000000),(-4488856763/12500000000000)⟩
def e113 : ℝ := (708537561/100000000000000)
theorem h113 : Model (fun x => f113 ((93/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(976146489766861/12500000000000),(4621814546377/12500000000000),(-5151660563/6250000000000),(1030827/781250000000)⟩
def e114 : ℝ := (181923/2500000000000)
theorem h114 : Model (fun x => f114 ((93/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(3272024135399/100000000000000),(20227594629/20000000000000),(109090157/25000000000000),(-519583/12500000000000)⟩
def e115 : ℝ := (43293/100000000000000)
theorem h115 : Model (fun x => f115 ((93/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(591867847017/100000000000000),(27441873259/100000000000000),(82613663/25000000000000),(-78087/20000000000000)⟩
def e116 : ℝ := (21961/100000000000000)
theorem h116 : Model (fun x => f116 ((93/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(46219977701721/100000000000000),(1180911667171/50000000000000),(35464415447/100000000000000),(69855819/100000000000000)⟩
def e117 : ℝ := (2149497/100000000000000)
theorem h117 : Model (fun x => f117 ((93/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(50400282852217/50000000000000),(1056016708563/20000000000000),(5219101521/6250000000000),(230462423/100000000000000)⟩
def e118 : ℝ := (2390787/50000000000000)
theorem h118 : Model (fun x => f118 ((93/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(110147106609924713/100000000000000),(1327311329968207/50000000000000),(8927984784541/100000000000000),(-35680391681/100000000000000)⟩
def e119 : ℝ := (142663827/20000000000000)
theorem h119 : Model (fun x => f119 ((93/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(53530709713/50000000000000),(3309258891/50000000000000),(65422273/50000000000000),(305319/50000000000000)⟩
def e120 : ℝ := (767/10000000000000)
theorem h120 : Model (fun x => f120 ((93/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(4841514701/25000000000000),(74825393/5000000000000),(10287347/25000000000000),(416583/100000000000000)⟩
def e121 : ℝ := (267/12500000000000)
theorem h121 : Model (fun x => f121 ((93/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(3503075483/100000000000000),(20302453/6250000000000),(11442273/100000000000000),(22093/12500000000000)⟩
def e122 : ℝ := (1227/100000000000000)
theorem h122 : Model (fun x => f122 ((93/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(316831059/50000000000000),(68552537/100000000000000),(2944461/100000000000000),(60973/100000000000000)⟩
def e123 : ℝ := (313/50000000000000)
theorem h123 : Model (fun x => f123 ((93/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(950493177/50000000000000),(205657611/100000000000000),(8833383/100000000000000),(182919/100000000000000)⟩
def e124 : ℝ := (939/50000000000000)
theorem h124 : Model (fun x => f124 ((93/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-950493177/50000000000000),(-205657611/100000000000000),(-8833383/100000000000000),(-182919/100000000000000)⟩
def e125 : ℝ := (939/50000000000000)
theorem h125 : Model (fun x => f125 ((93/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(110147104708938359/100000000000000),(2654622454278803/100000000000000),(4463987975579/50000000000000),(-178402873/500000000000)⟩
def e126 : ℝ := (713321013/100000000000000)
theorem h126 : Model (fun x => f126 ((93/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2928439469300583/10000000000000),(13865443639131/10000000000000),(-15454981689/5000000000000),(3092481/625000000000)⟩
def e127 : ℝ := (545769/2000000000000)
theorem h127 : Model (fun x => f127 ((93/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2262210173888731/100000000000000),(28998512059/250000000000),(-3457016299/20000000000000),(966341/50000000000000)⟩
def e128 : ℝ := (2396707/100000000000000)
theorem h128 : Model (fun x => f128 ((93/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(662474556106909499/100000000000000),(3266735128587437/50000000000000),(4028774532081/100000000000000),(-48060928763/100000000000000)⟩
def e129 : ℝ := (1439276693/100000000000000)
theorem h129 : Model (fun x => f129 ((93/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(3773729839/25000000000000),(-74434713/50000000000000),(10753/781250000000),(-5787/50000000000000)⟩
def e130 : ℝ := (33/25000000000000)
theorem h130 : Model (fun x => f130 ((93/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (20498031486718659/3125000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(16626616628783/100000000000000),(236737756143/100000000000000),(-217640663/20000000000000),(639049/12500000000000)⟩
def e131 : ℝ := (390433/100000000000000)
theorem h131 : Model (fun x => f131 ((93/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(9144996325669/25000000000000),(578034698847/100000000000000),(-1670620581/100000000000000),(6437191/100000000000000)⟩
def e132 : ℝ := (724737/100000000000000)
theorem h132 : Model (fun x => f132 ((93/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-380454387806489/100000000000000),(-744979990833/12500000000000),(8900307923/50000000000000),(-72570589/100000000000000)⟩
def e133 : ℝ := (20232871/100000000000000)
theorem h133 : Model (fun x => f133 ((93/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(10752688172043/25000000000000),(-462481211701/100000000000000),(2486458127/50000000000000),(-26736109/50000000000000)⟩
def e134 : ℝ := (290611/50000000000000)
theorem h134 : Model (fun x => f134 ((93/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (23/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-40909073957687/25000000000000),(-200960487193/25000000000000),(4074910169/25000000000000),(-20647811/10000000000000)⟩
def e135 : ℝ := (15463791/100000000000000)
theorem h135 : Model (fun x => f135 ((93/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(74805201/256000),(804357/64000),(25947/128000),(93/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((93/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((93/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(7239213/32000),(233523/32000),(2511/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((93/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(26543781/51200),(1271403/64000),(35991/128000),(111/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((93/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-8649/1600),(-93/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((93/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(26267013/51200),(1263963/64000),(35911/128000),(111/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((93/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((93/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(279/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((93/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-279/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((93/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(25552773/51200),(1254363/64000),(35911/128000),(111/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((93/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(25706373/51200),(1254363/64000),(35911/128000),(111/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((93/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((93/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(25706373/800),(1254363/1000),(35911/2000),(111/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((93/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((93/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(14138182989/512000),(152023473/128000),(4903983/256000),(17577/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((93/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(3621398877/100000000000000),(-38939773/25000000000000),(65423/1562500000000),(-18009/20000000000000)⟩
def e151 : ℝ := (1921/100000000000000)
theorem h151 : Model (fun x => f151 ((93/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (6760105317/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(29091571973107/25000000000000),(-462452886817/100000000000000),(4188628879/100000000000000),(-9015463/25000000000000)⟩
def e152 : ℝ := (24267313/20000000000000)
theorem h152 : Model (fun x => f152 ((93/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(213/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((93/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(36849/1600),(193/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((93/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(399/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((93/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(15664160401/312500000000),(-37688205477/100000000000000),(56673993/20000000000000),(-1065301/50000000000000)⟩
def e156 : ℝ := (3229/20000000000000)
theorem h156 : Model (fun x => f156 ((93/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (99/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(115441729323289/100000000000000),(341290255693/100000000000000),(566739909/100000000000000),(-4261221/100000000000000)⟩
def e157 : ℝ := (71397/10000000000000)
theorem h157 : Model (fun x => f157 ((93/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(215441729323289/100000000000000),(341290255693/100000000000000),(566739909/100000000000000),(-4261221/100000000000000)⟩
def e158 : ℝ := (71397/10000000000000)
theorem h158 : Model (fun x => f158 ((93/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(26930216165411/25000000000000),(85322563923/50000000000000),(141684977/50000000000000),(-2130611/100000000000000)⟩
def e159 : ℝ := (356987/100000000000000)
theorem h159 : Model (fun x => f159 ((93/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(1930216165411/25000000000000),(85322563923/50000000000000),(141684977/50000000000000),(-2130611/100000000000000)⟩
def e160 : ℝ := (356987/100000000000000)
theorem h160 : Model (fun x => f160 ((93/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((93/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((93/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(79508257250261/20000000000000),(78720222667/12500000000000),(261442517/25000000000000),(-786297/10000000000000)⟩
def e163 : ℝ := (658727/50000000000000)
theorem h163 : Model (fun x => f163 ((93/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(275325557196559/10000000000000),(78720222667/12500000000000),(261442517/25000000000000),(-786297/10000000000000)⟩
def e164 : ℝ := (263491/20000000000000)
theorem h164 : Model (fun x => f164 ((93/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((93/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(118633228338649/4000000000000),(5376681326871/100000000000000),(2500767351/25000000000000),(-12712423/20000000000000)⟩
def e166 : ℝ := (5638181/50000000000000)
theorem h166 : Model (fun x => f166 ((93/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8248211660847177/100000000000000),(5376681326871/100000000000000),(2500767351/25000000000000),(-12712423/20000000000000)⟩
def e167 : ℝ := (11276363/100000000000000)
theorem h167 : Model (fun x => f167 ((93/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((93/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4442522460093563/50000000000000),(19866978949067/100000000000000),(43323391167/100000000000000),(-42380263/20000000000000)⟩
def e169 : ℝ := (20912809/50000000000000)
theorem h169 : Model (fun x => f169 ((93/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(2830818507846949/20000000000000),(19866978949067/100000000000000),(43323391167/100000000000000),(-42380263/20000000000000)⟩
def e170 : ℝ := (41825619/100000000000000)
theorem h170 : Model (fun x => f170 ((93/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((93/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(1524691086827291/10000000000000),(455541508151/1000000000000),(12067880871/10000000000000),(-99901069/25000000000000)⟩
def e172 : ℝ := (96389411/100000000000000)
theorem h172 : Model (fun x => f172 ((93/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(3516525030797439/20000000000000),(455541508151/1000000000000),(12067880871/10000000000000),(-99901069/25000000000000)⟩
def e173 : ℝ := (24097353/25000000000000)
theorem h173 : Model (fun x => f173 ((93/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((93/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(18940155846090721/100000000000000),(79075218319999/100000000000000),(128778035957/50000000000000),(-117513811/25000000000000)⟩
def e175 : ℝ := (84120621/50000000000000)
theorem h175 : Model (fun x => f175 ((93/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(19342536798471673/100000000000000),(79075218319999/100000000000000),(128778035957/50000000000000),(-117513811/25000000000000)⟩
def e176 : ℝ := (168241243/100000000000000)
theorem h176 : Model (fun x => f176 ((93/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((93/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(20835947886810359/100000000000000),(118187605555797/100000000000000),(467190572679/100000000000000),(-63719873/25000000000000)⟩
def e178 : ℝ := (50523191/20000000000000)
theorem h178 : Model (fun x => f178 ((93/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(20818328839191311/100000000000000),(118187605555797/100000000000000),(467190572679/100000000000000),(-63719873/25000000000000)⟩
def e179 : ℝ := (63153989/25000000000000)
theorem h179 : Model (fun x => f179 ((93/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((93/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(11212841916840637/50000000000000),(40709543622659/25000000000000),(763936003961/100000000000000),(103507529/25000000000000)⟩
def e181 : ℝ := (174467033/50000000000000)
theorem h181 : Model (fun x => f181 ((93/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(22429017167014607/100000000000000),(40709543622659/25000000000000),(763936003961/100000000000000),(103507529/25000000000000)⟩
def e182 : ℝ := (348934067/100000000000000)
theorem h182 : Model (fun x => f182 ((93/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(1731714060402097/100000000000000),(50846540089167/100000000000000),(400414971637/100000000000000),(329786407/25000000000000)⟩
def e183 : ℝ := (54401577/50000000000000)
theorem h183 : Model (fun x => f183 ((93/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(58018923417261/50000000000000),(367640814437/100000000000000),(36067789/4000000000000),(-452889/12500000000000)⟩
def e184 : ℝ := (776803/100000000000000)
theorem h184 : Model (fun x => f184 ((93/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(51930216165411/25000000000000),(85322563923/50000000000000),(141684977/50000000000000),(-2130611/100000000000000)⟩
def e185 : ℝ := (356987/100000000000000)
theorem h185 : Model (fun x => f185 ((93/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(43147957615781/10000000000000),(708931070129/100000000000000),(1468434633/100000000000000),(-3942167/50000000000000)⟩
def e186 : ℝ := (1490777/100000000000000)
theorem h186 : Model (fun x => f186 ((93/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(896273106433399/100000000000000),(220889662309/10000000000000),(1370671231/25000000000000),(-21055849/100000000000000)⟩
def e187 : ℝ := (4666519/100000000000000)
theorem h187 : Model (fun x => f187 ((93/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1861746246413233/100000000000000),(3058892776643/50000000000000),(8848911843/50000000000000),(-47218201/100000000000000)⟩
def e188 : ℝ := (12976431/100000000000000)
theorem h188 : Model (fun x => f188 ((93/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2160330257860449/100000000000000),(278869713861/2000000000000),(3738432367/6250000000000),(-2015963/100000000000000)⟩
def e189 : ℝ := (5970379/20000000000000)
theorem h189 : Model (fun x => f189 ((93/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((93/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(26930216165411/3125000000000),(85322563923/6250000000000),(141684977/6250000000000),(-2130611/12500000000000)⟩
def e191 : ℝ := (356987/12500000000000)
theorem h191 : Model (fun x => f191 ((93/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(488902382063837/50000000000000),(346560367441/20000000000000),(3168654357/100000000000000),(-5167/25000000000)⟩
def e192 : ℝ := (3632699/100000000000000)
theorem h192 : Model (fun x => f192 ((93/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(538902382063837/50000000000000),(346560367441/20000000000000),(3168654357/100000000000000),(-5167/25000000000)⟩
def e193 : ℝ := (3632699/100000000000000)
theorem h193 : Model (fun x => f193 ((93/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(23284142440111583/100000000000000),(93858897741527/50000000000000),(59672150599/6250000000000),(1010069659/100000000000000)⟩
def e194 : ℝ := (201142121/50000000000000)
theorem h194 : Model (fun x => f194 ((93/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(13421151361/3125000000000),(-86561537/2500000000000),(10304039/100000000000000),(20137/50000000000000)⟩
def e195 : ℝ := (8147/100000000000000)
theorem h195 : Model (fun x => f195 ((93/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (5773867119466261/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(7437310885961/100000000000000),(31682836629/20000000000000),(8599013/6250000000000),(-70691/3125000000000)⟩
def e196 : ℝ := (632683/100000000000000)
theorem h196 : Model (fun x => f196 ((93/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(115441729323289/50000000000000),(341290255693/50000000000000),(566739909/50000000000000),(-4261221/50000000000000)⟩
def e197 : ℝ := (71397/5000000000000)
theorem h197 : Model (fun x => f197 ((93/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(23208131570913/50000000000000),(-7352994411/10000000000000),(-1405131/25000000000000),(560199/50000000000000)⟩
def e198 : ℝ := (4923/3125000000000)
theorem h198 : Model (fun x => f198 ((93/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (13443741709531/6250000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(13395934214543/12500000000000),(147059888217/100000000000000),(5620523/50000000000000),(-1120399/50000000000000)⟩
def e199 : ℝ := (208503/20000000000000)
theorem h199 : Model (fun x => f199 ((93/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(895934214543/12500000000000),(147059888217/100000000000000),(5620523/50000000000000),(-1120399/50000000000000)⟩
def e200 : ℝ := (208503/20000000000000)
theorem h200 : Model (fun x => f200 ((93/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(7909980202873/2000000000000),(271360508019/50000000000000),(10371203/25000000000000),(-2067403/25000000000000)⟩
def e201 : ℝ := (192369/5000000000000)
theorem h201 : Model (fun x => f201 ((93/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(550242659171587/20000000000000),(271360508019/50000000000000),(10371203/25000000000000),(-2067403/25000000000000)⟩
def e202 : ℝ := (3847381/100000000000000)
theorem h202 : Model (fun x => f202 ((93/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2948405785719113/100000000000000),(925510319943/20000000000000),(143981037/12500000000000),(-17597363/25000000000000)⟩
def e203 : ℝ := (2052537/6250000000000)
theorem h203 : Model (fun x => f203 ((93/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1646157347620013/20000000000000),(925510319943/20000000000000),(143981037/12500000000000),(-17597363/25000000000000)⟩
def e204 : ℝ := (32840593/100000000000000)
theorem h204 : Model (fun x => f204 ((93/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4410363107100857/50000000000000),(4265853980191/25000000000000),(2241226363/25000000000000),(-257655811/100000000000000)⟩
def e205 : ℝ := (60652647/50000000000000)
theorem h205 : Model (fun x => f205 ((93/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14089773833249333/100000000000000),(4265853980191/25000000000000),(2241226363/25000000000000),(-257655811/100000000000000)⟩
def e206 : ℝ := (24261059/20000000000000)
theorem h206 : Model (fun x => f206 ((93/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15099654669439793/100000000000000),(39006837421199/100000000000000),(3628474103/10000000000000),(-144186177/25000000000000)⟩
def e207 : ℝ := (69501179/25000000000000)
theorem h207 : Model (fun x => f207 ((93/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8717684477577039/50000000000000),(39006837421199/100000000000000),(3628474103/10000000000000),(-144186177/25000000000000)⟩
def e208 : ℝ := (278004717/100000000000000)
theorem h208 : Model (fun x => f208 ((93/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(4671261110590587/25000000000000),(67443076336611/100000000000000),(98208769659/100000000000000),(-951029057/100000000000000)⟩
def e209 : ℝ := (241115959/50000000000000)
theorem h209 : Model (fun x => f209 ((93/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(190874253947433/1000000000000),(67443076336611/100000000000000),(98208769659/100000000000000),(-951029057/100000000000000)⟩
def e210 : ℝ := (482231919/100000000000000)
theorem h210 : Model (fun x => f210 ((93/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2556938949129787/12500000000000),(12543373444443/12500000000000),(206575196351/100000000000000),(-161862181/12500000000000)⟩
def e211 : ℝ := (22503111/3125000000000)
theorem h211 : Model (fun x => f211 ((93/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(1277368284088703/6250000000000),(12543373444443/12500000000000),(206575196351/100000000000000),(-161862181/12500000000000)⟩
def e212 : ℝ := (720099553/100000000000000)
theorem h212 : Model (fun x => f212 ((93/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(10951386560893401/50000000000000),(68797636722467/50000000000000),(92812254971/25000000000000),(-765305733/50000000000000)⟩
def e213 : ℝ := (991022409/100000000000000)
theorem h213 : Model (fun x => f213 ((93/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(4381221291024027/20000000000000),(68797636722467/50000000000000),(92812254971/25000000000000),(-765305733/50000000000000)⟩
def e214 : ℝ := (99102241/10000000000000)
theorem h214 : Model (fun x => f214 ((93/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(98132151402817/6250000000000),(42077200724693/100000000000000),(46283821349/20000000000000),(-39152229/100000000000000)⟩
def e215 : ℝ := (153801269/50000000000000)
theorem h215 : Model (fun x => f215 ((93/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(14356084278429/12500000000000),(39400091763/12500000000000),(240359597/100000000000000),(-596219/12500000000000)⟩
def e216 : ℝ := (2244133/100000000000000)
theorem h216 : Model (fun x => f216 ((93/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(25895934214543/12500000000000),(147059888217/100000000000000),(5620523/50000000000000),(-1120399/50000000000000)⟩
def e217 : ℝ := (208503/20000000000000)
theorem h217 : Model (fun x => f217 ((93/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(10729590541503/2500000000000),(304660255269/50000000000000),(262841689/100000000000000),(-2312837/25000000000000)⟩
def e218 : ℝ := (4329163/100000000000000)
theorem h218 : Model (fun x => f218 ((93/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(444564433298791/50000000000000),(236683857847/12500000000000),(372208319/25000000000000),(-14163947/50000000000000)⟩
def e219 : ℝ := (6741441/50000000000000)
theorem h219 : Model (fun x => f219 ((93/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(460496452753243/25000000000000),(5230207669291/100000000000000),(1492215451/25000000000000),(-38103721/50000000000000)⟩
def e220 : ℝ := (18662497/50000000000000)
theorem h220 : Model (fun x => f220 ((93/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2115496283405809/100000000000000),(5906388482963/50000000000000),(27768201289/100000000000000),(-14399619/10000000000000)⟩
def e221 : ℝ := (84914923/100000000000000)
theorem h221 : Model (fun x => f221 ((93/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(13395934214543/1562500000000),(147059888217/12500000000000),(5620523/6250000000000),(-1120399/6250000000000)⟩
def e222 : ℝ := (208503/2500000000000)
theorem h222 : Model (fun x => f222 ((93/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(121523557994773/12500000000000),(9322998999/625000000000),(66057593/20000000000000),(-2837017/12500000000000)⟩
def e223 : ℝ := (10584253/100000000000000)
theorem h223 : Model (fun x => f223 ((93/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(134023557994773/12500000000000),(9322998999/625000000000),(66057593/20000000000000),(-2837017/12500000000000)⟩
def e224 : ℝ := (10584253/100000000000000)
theorem h224 : Model (fun x => f224 ((93/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(11341053553070607/50000000000000),(158211663473897/100000000000000),(480923493019/100000000000000),(-1570817611/100000000000000)⟩
def e225 : ℝ := (1141621807/100000000000000)
theorem h225 : Model (fun x => f225 ((93/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(220438073791/50000000000000),(-1537594113/50000000000000),(605109/5000000000000),(11319/100000000000000)⟩
def e226 : ℝ := (11529/50000000000000)
theorem h226 : Model (fun x => f226 ((93/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (140771323792093/625000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1384451995661/20000000000000),(137224367711/100000000000000),(-83663407/100000000000000),(-2019207/100000000000000)⟩
def e227 : ℝ := (1771433/100000000000000)
theorem h227 : Model (fun x => f227 ((93/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(7179785432133/50000000000000),(36954818857/12500000000000),(53920801/100000000000000),(-4281319/100000000000000)⟩
def e228 : ℝ := (601029/25000000000000)
theorem h228 : Model (fun x => f228 ((93/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(4177424893007/25000000000000),(277617357213/100000000000000),(-702974247/100000000000000),(7709/390625000000)⟩
def e229 : ℝ := (258447/1250000000000)
theorem h229 : Model (fun x => f229 ((93/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7186967557861/100000000000000),(21063046939/50000000000000),(-755323267/100000000000000),(4485287/50000000000000)⟩
def e230 : ℝ := (928121/10000000000000)
theorem h230 : Model (fun x => f230 ((93/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-156449328272887/100000000000000),(-380857927447/50000000000000),(15544317409/100000000000000),(-12344221/6250000000000)⟩
def e231 : ℝ := (24745001/100000000000000)
theorem h231 : Model (fun x => f231 ((93/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((93/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-8649/320),(-93/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((93/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1953/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((93/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1395/64),(-9/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((93/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((93/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3059/64),(-9/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((93/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((93/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(382375/32),(-225/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((93/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13671/1600),(27/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((93/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23271/1600),(27/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((93/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((93/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4398219/1600),(5103/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((93/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(9094590333/25000000000000),(-10551929/12500000000000),(1759133/100000000000000),(-771/10000000000000)⟩
def e244 : ℝ := (3/3125000000000)
theorem h244 : Model (fun x => f244 ((93/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (274239/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(434692997322609/100000000000000),(-60810766763/4000000000000),(-6213237751/100000000000000),(-50916729/100000000000000)⟩
def e245 : ℝ := (605119/25000000000000)
theorem h245 : Model (fun x => f245 ((93/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(837/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((93/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(75609/1600),(453/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((93/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(109209/1600),(453/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((93/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(29929/1600),(173/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((93/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3268516161/2560000),(16225497/640000),(226307/1280000),(313/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((93/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((93/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(159201/160),(1197/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((93/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(100501881269/100000000000000),(-755653243/50000000000000),(17044809/100000000000000),(-42719/25000000000000)⟩
def e253 : ℝ := (411/25000000000000)
theorem h253 : Model (fun x => f253 ((93/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (78399/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(128317196538527/100000000000000),(123675173311/20000000000000),(608007177/50000000000000),(-2046699/50000000000000)⟩
def e254 : ℝ := (532557/12500000000000)
theorem h254 : Model (fun x => f254 ((93/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(228317196538527/100000000000000),(123675173311/20000000000000),(608007177/50000000000000),(-2046699/50000000000000)⟩
def e255 : ℝ := (532557/12500000000000)
theorem h255 : Model (fun x => f255 ((93/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(114158598269263/100000000000000),(309187933277/100000000000000),(608007177/100000000000000),(-2046699/100000000000000)⟩
def e256 : ℝ := (2130229/100000000000000)
theorem h256 : Model (fun x => f256 ((93/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(14158598269263/100000000000000),(309187933277/100000000000000),(608007177/100000000000000),(-2046699/100000000000000)⟩
def e257 : ℝ := (2130229/100000000000000)
theorem h257 : Model (fun x => f257 ((93/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(421299588850851/100000000000000),(1141050706141/100000000000000),(224383601/10000000000000),(-3776647/50000000000000)⟩
def e258 : ℝ := (7861561/100000000000000)
theorem h258 : Model (fun x => f258 ((93/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(173563367160321/6250000000000),(1141050706141/100000000000000),(224383601/10000000000000),(-3776647/50000000000000)⟩
def e259 : ℝ := (3930781/50000000000000)
theorem h259 : Model (fun x => f259 ((93/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(792550028236627/25000000000000),(1977759859451/20000000000000),(717936453/3125000000000),(-5158451/10000000000000)⟩
def e260 : ℝ := (34106637/50000000000000)
theorem h260 : Model (fun x => f260 ((93/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(422629053266373/5000000000000),(1977759859451/20000000000000),(717936453/3125000000000),(-5158451/10000000000000)⟩
def e261 : ℝ := (2728531/4000000000000)
theorem h261 : Model (fun x => f261 ((93/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(1929869612350193/20000000000000),(2338954710491/6250000000000),(10819403181/10000000000000),(-20145941/20000000000000)⟩
def e262 : ℝ := (258576113/100000000000000)
theorem h262 : Model (fun x => f262 ((93/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(1864799460099823/12500000000000),(2338954710491/6250000000000),(10819403181/10000000000000),(-20145941/20000000000000)⟩
def e263 : ℝ := (129288057/50000000000000)
theorem h263 : Model (fun x => f263 ((93/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(8515315696730969/50000000000000),(88847765869937/100000000000000),(41240744779/12500000000000),(8858301/6250000000000)⟩
def e264 : ℝ := (24600233/4000000000000)
theorem h264 : Model (fun x => f264 ((93/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(19366345679176223/100000000000000),(88847765869937/100000000000000),(41240744779/12500000000000),(8858301/6250000000000)⟩
def e265 : ℝ := (307502913/50000000000000)
theorem h265 : Model (fun x => f265 ((93/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(22108348763327557/100000000000000),(161305768067401/100000000000000),(48068386997/6250000000000),(1325721437/100000000000000)⟩
def e266 : ℝ := (559533083/50000000000000)
theorem h266 : Model (fun x => f266 ((93/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(22510729715708509/100000000000000),(161305768067401/100000000000000),(48068386997/6250000000000),(1325721437/100000000000000)⟩
def e267 : ℝ := (1119066167/100000000000000)
theorem h267 : Model (fun x => f267 ((93/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(5139586700727057/20000000000000),(3964763495731/1562500000000),(1513591971713/100000000000000),(4411395213/100000000000000)⟩
def e268 : ℝ := (176944119/10000000000000)
theorem h268 : Model (fun x => f268 ((93/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(25680314456016237/100000000000000),(3964763495731/1562500000000),(1513591971713/100000000000000),(4411395213/100000000000000)⟩
def e269 : ℝ := (1769441191/100000000000000)
theorem h269 : Model (fun x => f269 ((93/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(29316287014127047/100000000000000),(369072013136339/100000000000000),(533716406669/20000000000000),(5366509459/50000000000000)⟩
def e270 : ℝ := (324448911/12500000000000)
theorem h270 : Model (fun x => f270 ((93/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(1465981017373019/5000000000000),(369072013136339/100000000000000),(533716406669/20000000000000),(5366509459/50000000000000)⟩
def e271 : ℝ := (2595591289/100000000000000)
theorem h271 : Model (fun x => f271 ((93/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(4151247259070007/100000000000000),(142908151861231/100000000000000),(212153166911/12500000000000),(11414478619/100000000000000)⟩
def e272 : ℝ := (131237767/12500000000000)
theorem h272 : Model (fun x => f272 ((93/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(130321855588029/100000000000000),(705929221293/100000000000000),(1172078361/50000000000000),(-913197/100000000000000)⟩
def e273 : ℝ := (977173/20000000000000)
theorem h273 : Model (fun x => f273 ((93/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(214158598269263/100000000000000),(309187933277/100000000000000),(608007177/100000000000000),(-2046699/100000000000000)⟩
def e274 : ℝ := (2130229/100000000000000)
theorem h274 : Model (fun x => f274 ((93/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(91727810425311/20000000000000),(1324305087847/100000000000000),(890042769/25000000000000),(-1001319/20000000000000)⟩
def e275 : ℝ := (9146323/100000000000000)
theorem h275 : Model (fun x => f275 ((93/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(30694217660927/3125000000000),(1063542454853/25000000000000),(14507562357/100000000000000),(-524763/50000000000000)⟩
def e276 : ℝ := (14717683/50000000000000)
theorem h276 : Model (fun x => f276 ((93/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(42069956027109/2000000000000),(1214756060433/10000000000000),(50194509411/100000000000000),(1511583/3125000000000)⟩
def e277 : ℝ := (21036583/25000000000000)
theorem h277 : Model (fun x => f277 ((93/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1370658683489907/50000000000000),(30680132037267/100000000000000),(40095376231/20000000000000),(27316961/4000000000000)⟩
def e278 : ℝ := (215034931/100000000000000)
theorem h278 : Model (fun x => f278 ((93/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(114158598269263/12500000000000),(309187933277/12500000000000),(608007177/12500000000000),(-2046699/12500000000000)⟩
def e279 : ℝ := (2130229/12500000000000)
theorem h279 : Model (fun x => f279 ((93/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1043590641742133/100000000000000),(3179432687509/100000000000000),(3604107069/50000000000000),(-17286789/100000000000000)⟩
def e280 : ℝ := (21927697/100000000000000)
theorem h280 : Model (fun x => f280 ((93/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1143590641742133/100000000000000),(3179432687509/100000000000000),(3604107069/50000000000000),(-17286789/100000000000000)⟩
def e281 : ℝ := (21927697/100000000000000)
theorem h281 : Model (fun x => f281 ((93/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(15674724434616499/50000000000000),(13687920602701/3125000000000),(1732844512161/50000000000000),(3980371649/25000000000000)⟩
def e282 : ℝ := (3104726139/100000000000000)
theorem h282 : Model (fun x => f282 ((93/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(318984874079/100000000000000),(-1114211519/25000000000000),(27007051/100000000000000),(-583/1250000000000)⟩
def e283 : ℝ := (1303/4000000000000)
theorem h283 : Model (fun x => f283 ((93/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (30907950694709509/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(3310462710513/25000000000000),(67710171923/25000000000000),(41456301/25000000000000),(-4117/160000000000)⟩
def e284 : ℝ := (491479/10000000000000)
theorem h284 : Model (fun x => f284 ((93/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(128317196538527/50000000000000),(123675173311/10000000000000),(608007177/25000000000000),(-2046699/25000000000000)⟩
def e285 : ℝ := (532557/6250000000000)
theorem h285 : Model (fun x => f285 ((93/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(43798715784917/100000000000000),(-14828092911/12500000000000),(88012693/100000000000000),(1178667/100000000000000)⟩
def e286 : ℝ := (16551/2000000000000)
theorem h286 : Model (fun x => f286 ((93/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (56924399075941/25000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(22480513686033/20000000000000),(237249486573/100000000000000),(-176025387/100000000000000),(-294667/12500000000000)⟩
def e287 : ℝ := (1475663/25000000000000)
theorem h287 : Model (fun x => f287 ((93/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(2480513686033/20000000000000),(237249486573/100000000000000),(-176025387/100000000000000),(-294667/12500000000000)⟩
def e288 : ℝ := (1475663/25000000000000)
theorem h288 : Model (fun x => f288 ((93/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(207409501269947/50000000000000),(4377817907/500000000000),(-259847/40000000000),(-8699693/100000000000000)⟩
def e289 : ℝ := (21783599/100000000000000)
theorem h289 : Model (fun x => f289 ((93/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2770533288254179/100000000000000),(4377817907/500000000000),(-259847/40000000000),(-8699693/100000000000000)⟩
def e290 : ℝ := (54459/250000000000)
theorem h290 : Model (fun x => f290 ((93/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(778537643802601/25000000000000),(7557231955449/100000000000000),(-3529758597/100000000000000),(-39085943/50000000000000)⟩
def e291 : ℝ := (188163877/100000000000000)
theorem h291 : Model (fun x => f291 ((93/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(2099132881897839/25000000000000),(7557231955449/100000000000000),(-3529758597/100000000000000),(-39085943/50000000000000)⟩
def e292 : ℝ := (94081939/50000000000000)
theorem h292 : Model (fun x => f292 ((93/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(2359479274015313/25000000000000),(284152507593/1000000000000),(-32722897/4000000000000),(-6149573/2000000000000)⟩
def e293 : ℝ := (354184873/50000000000000)
theorem h293 : Model (fun x => f293 ((93/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14706964715108871/100000000000000),(284152507593/1000000000000),(-32722897/4000000000000),(-6149573/2000000000000)⟩
def e294 : ℝ := (708369747/100000000000000)
theorem h294 : Model (fun x => f294 ((93/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(16531006077900469/100000000000000),(66831669956393/100000000000000),(40607510561/100000000000000),(-372132701/50000000000000)⟩
def e295 : ℝ := (166908443/10000000000000)
theorem h295 : Model (fun x => f295 ((93/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(9433360181807377/50000000000000),(66831669956393/100000000000000),(40607510561/100000000000000),(-372132701/50000000000000)⟩
def e296 : ℝ := (1669084431/100000000000000)
theorem h296 : Model (fun x => f296 ((93/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(5301669566809987/25000000000000),(29970427687899/25000000000000),(170991461151/100000000000000),(-260525003/20000000000000)⟩
def e297 : ℝ := (1500526967/50000000000000)
theorem h297 : Model (fun x => f297 ((93/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(216090592196209/1000000000000),(29970427687899/25000000000000),(170991461151/100000000000000),(-260525003/20000000000000)⟩
def e298 : ℝ := (600210787/20000000000000)
theorem h298 : Model (fun x => f298 ((93/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(24289137576449261/100000000000000),(186017504014621/100000000000000),(214150443/48828125000),(-444731997/25000000000000)⟩
def e299 : ℝ := (4669200399/100000000000000)
theorem h299 : Model (fun x => f299 ((93/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(24271518528830213/100000000000000),(186017504014621/100000000000000),(214150443/48828125000),(-444731997/25000000000000)⟩
def e300 : ℝ := (11673001/250000000000)
theorem h300 : Model (fun x => f300 ((93/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(27281810223408557/100000000000000),(266672505335239/100000000000000),(891576843977/100000000000000),(-464657743/25000000000000)⟩
def e301 : ℝ := (3356220743/50000000000000)
theorem h301 : Model (fun x => f301 ((93/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(2728514355674189/10000000000000),(266672505335239/100000000000000),(891576843977/100000000000000),(-464657743/25000000000000)⟩
def e302 : ℝ := (6712441487/100000000000000)
theorem h302 : Model (fun x => f302 ((93/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(3384058600893669/100000000000000),(48904051478857/50000000000000),(695228798381/100000000000000),(154425937/20000000000000)⟩
def e303 : ℝ := (2487076463/100000000000000)
theorem h303 : Model (fun x => f303 ((93/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(126343373896979/100000000000000),(53334903299/10000000000000),(41789769/25000000000000),(-1533663/25000000000000)⟩
def e304 : ℝ := (6654191/50000000000000)
theorem h304 : Model (fun x => f304 ((93/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(42480513686033/20000000000000),(237249486573/100000000000000),(-176025387/100000000000000),(-294667/12500000000000)⟩
def e305 : ℝ := (1475663/25000000000000)
theorem h305 : Model (fun x => f305 ((93/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(451148510757309/100000000000000),(125981000767/12500000000000),(-92445849/50000000000000),(-2712331/25000000000000)⟩
def e306 : ℝ := (12556843/50000000000000)
theorem h306 : Model (fun x => f306 ((93/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(958251024282963/100000000000000),(1605521288179/50000000000000),(150532949/12500000000000),(-35892053/100000000000000)⟩
def e307 : ℝ := (8014017/10000000000000)
theorem h307 : Model (fun x => f307 ((93/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(2035349787585377/100000000000000),(4546891270381/50000000000000),(1061162969/12500000000000),(-5080999/5000000000000)⟩
def e308 : ℝ := (113662449/50000000000000)
theorem h308 : Model (fun x => f308 ((93/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(64288239806009/2500000000000),(22344910086903/100000000000000),(31314772961/50000000000000),(-48193259/25000000000000)⟩
def e309 : ℝ := (561592679/100000000000000)
theorem h309 : Model (fun x => f309 ((93/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(22480513686033/2500000000000),(237249486573/12500000000000),(-176025387/12500000000000),(-294667/1562500000000)⟩
def e310 : ℝ := (1475663/3125000000000)
theorem h310 : Model (fun x => f310 ((93/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1025563921338299/100000000000000),(1215672462787/50000000000000),(-62052201/5000000000000),(-1249667/5000000000000)⟩
def e311 : ℝ := (30264799/50000000000000)
theorem h311 : Model (fun x => f311 ((93/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1125563921338299/100000000000000),(1215672462787/50000000000000),(-62052201/5000000000000),(-1249667/5000000000000)⟩
def e312 : ℝ := (30264799/50000000000000)
theorem h312 : Model (fun x => f312 ((93/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(14472104658397683/50000000000000),(39253625055529/12500000000000),(121630359629/10000000000000),(-783532381/50000000000000)⟩
def e313 : ℝ := (7915908409/100000000000000)
theorem h313 : Model (fun x => f313 ((93/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(172746124977/50000000000000),(-187420193/5000000000000),(26149757/100000000000000),(-107489/100000000000000)⟩
def e314 : ℝ := (96717/100000000000000)
theorem h314 : Model (fun x => f314 ((93/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (28628954529781673/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(11691660199989/100000000000000),(8442849293/4000000000000),(-94839497/25000000000000),(-290649/20000000000000)⟩
def e315 : ℝ := (12103041/100000000000000)
theorem h315 : Model (fun x => f315 ((93/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(24933511042041/100000000000000),(481911920017/100000000000000),(-13345799/6250000000000),(-402637/10000000000000)⟩
def e316 : ℝ := (17017831/100000000000000)
theorem h316 : Model (fun x => f316 ((93/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(108384226486411/100000000000000),(428945222109/25000000000000),(-4901874361/50000000000000),(-56893737/100000000000000)⟩
def e317 : ℝ := (3751077/5000000000000)
theorem h317 : Model (fun x => f317 ((93/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(23308435803529/50000000000000),(236713590649/100000000000000),(-1352394709/20000000000000),(6029871/12500000000000)⟩
def e318 : ℝ := (8600591/25000000000000)
theorem h318 : Model (fun x => f318 ((93/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-109832456665829/100000000000000),(-105000452849/20000000000000),(1097792983/12500000000000),(-18658571/12500000000000)⟩
def e319 : ℝ := (11829473/20000000000000)
theorem h319 : Model (fun x => f319 ((93/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((93/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-95139/1600),(-1023/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((93/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((93/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(9021/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((93/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(265701/1600),(917/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((93/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((93/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(438501/1600),(917/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((93/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2192505/32),(4585/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((93/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((93/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1064639308748337777/100000000000000),(2470479251962109/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (137771/100000000000000)
theorem h329 : Model (fun x => f329 ((93/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4696426253/50000000000000),(-21795971/100000000000000),(227103/50000000000000),(-1991/100000000000000)⟩
def e330 : ℝ := (27/100000000000000)
theorem h330 : Model (fun x => f330 ((93/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (53106153994023041/5000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(64355862761461/10000000000000),(1198271315083/100000000000000),(4365202877/50000000000000),(31205311/100000000000000)⟩
def e331 : ℝ := (1606173/50000000000000)
theorem h331 : Model (fun x => f331 ((93/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((93/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(453/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((93/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((93/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((93/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(715806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((93/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((93/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((93/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(793917573343091/25000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (107/10000000000000)
theorem h339 : Model (fun x => f339 ((93/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3814193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((93/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((93/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((93/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2149329706627377/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1069/100000000000000)
theorem h343 : Model (fun x => f343 ((93/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(930522661941/20000000000000),(-1219815803/20000000000000),(7995241/100000000000000),(-10481/100000000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((93/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2146512164991827/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(14775165874179/10000000000000),(167675473977/20000000000000),(-109902317/10000000000000),(1440699/100000000000000)⟩
def e345 : ℝ := (369/12500000000000)
theorem h345 : Model (fun x => f345 ((93/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(24775165874179/10000000000000),(167675473977/20000000000000),(-109902317/10000000000000),(1440699/100000000000000)⟩
def e346 : ℝ := (369/12500000000000)
theorem h346 : Model (fun x => f346 ((93/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(24775165874179/20000000000000),(209594342471/50000000000000),(-109902317/20000000000000),(720349/100000000000000)⟩
def e347 : ℝ := (1477/100000000000000)
theorem h347 : Model (fun x => f347 ((93/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(4775165874179/20000000000000),(209594342471/50000000000000),(-109902317/20000000000000),(720349/100000000000000)⟩
def e348 : ℝ := (1477/100000000000000)
theorem h348 : Model (fun x => f348 ((93/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(457160798868779/100000000000000),(309401172219/20000000000000),(-2027959421/100000000000000),(265843/10000000000000)⟩
def e349 : ℝ := (5453/100000000000000)
theorem h349 : Model (fun x => f349 ((93/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(351609385572883/12500000000000),(309401172219/20000000000000),(-2027959421/100000000000000),(265843/10000000000000)⟩
def e350 : ℝ := (2727/50000000000000)
theorem h350 : Model (fun x => f350 ((93/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1742236170097267/50000000000000),(3426905104243/25000000000000),(-11484352489/100000000000000),(1638429/25000000000000)⟩
def e351 : ℝ := (20453/25000000000000)
theorem h351 : Model (fun x => f351 ((93/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4383426646287743/50000000000000),(3426905104243/25000000000000),(-11484352489/100000000000000),(1638429/25000000000000)⟩
def e352 : ℝ := (81813/100000000000000)
theorem h352 : Model (fun x => f352 ((93/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(10860012225907499/100000000000000),(53730085506479/100000000000000),(-2470208807/50000000000000),(-52195659/100000000000000)⟩
def e353 : ℝ := (420823/100000000000000)
theorem h353 : Model (fun x => f353 ((93/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(8064529922477559/50000000000000),(53730085506479/100000000000000),(-2470208807/50000000000000),(-52195659/100000000000000)⟩
def e354 : ℝ := (52603/12500000000000)
theorem h354 : Model (fun x => f354 ((93/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(19980006652666143/100000000000000),(134169782900417/100000000000000),(130479403159/100000000000000),(-264435001/100000000000000)⟩
def e355 : ℝ := (478867/50000000000000)
theorem h355 : Model (fun x => f355 ((93/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(5578930234595107/25000000000000),(134169782900417/100000000000000),(130479403159/100000000000000),(-264435001/100000000000000)⟩
def e356 : ℝ := (191547/20000000000000)
theorem h356 : Model (fun x => f356 ((93/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(27643784392513227/100000000000000),(32468613558743/12500000000000),(300714759759/50000000000000),(-71428717/20000000000000)⟩
def e357 : ℝ := (2383397/100000000000000)
theorem h357 : Model (fun x => f357 ((93/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(28046165344894179/100000000000000),(32468613558743/12500000000000),(300714759759/50000000000000),(-71428717/20000000000000)⟩
def e358 : ℝ := (1191699/50000000000000)
theorem h358 : Model (fun x => f358 ((93/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(17371209963860099/50000000000000),(43933246633491/10000000000000),(1640377843/97656250000),(853389843/100000000000000)⟩
def e359 : ℝ := (6317777/100000000000000)
theorem h359 : Model (fun x => f359 ((93/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(694496017602023/2000000000000),(43933246633491/10000000000000),(1640377843/97656250000),(853389843/100000000000000)⟩
def e360 : ℝ := (3158889/50000000000000)
theorem h360 : Model (fun x => f360 ((93/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(8603127017523429/20000000000000),(689789172526001/100000000000000),(932903900517/25000000000000),(593440969/10000000000000)⟩
def e361 : ℝ := (108679/1000000000000)
theorem h361 : Model (fun x => f361 ((93/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(21509484210475239/50000000000000),(689789172526001/100000000000000),(932903900517/25000000000000),(593440969/10000000000000)⟩
def e362 : ℝ := (10867901/100000000000000)
theorem h362 : Model (fun x => f362 ((93/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(10271135497305339/100000000000000),(345023533850613/100000000000000),(354607811989/10000000000000),(6789407597/50000000000000)⟩
def e363 : ℝ := (1263143/10000000000000)
theorem h363 : Model (fun x => f363 ((93/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(15345221102327/10000000000000),(1038546920201/100000000000000),(395767469/100000000000000),(-564461/20000000000000)⟩
def e364 : ℝ := (12741/100000000000000)
theorem h364 : Model (fun x => f364 ((93/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(44775165874179/20000000000000),(209594342471/50000000000000),(-109902317/20000000000000),(720349/100000000000000)⟩
def e365 : ℝ := (1477/100000000000000)
theorem h365 : Model (fun x => f365 ((93/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(25060193488253/5000000000000),(375384858017/20000000000000),(-703255701/100000000000000),(-1381607/100000000000000)⟩
def e366 : ℝ := (3139/20000000000000)
theorem h366 : Model (fun x => f366 ((93/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(280518580068887/25000000000000),(3151484865819/50000000000000),(1769630693/50000000000000),(-1593069/12500000000000)⟩
def e367 : ℝ := (6779/12500000000000)
theorem h367 : Model (fun x => f367 ((93/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(502410638134943/20000000000000),(2351804293617/12500000000000),(28178958329/100000000000000),(-20124243/50000000000000)⟩
def e368 : ℝ := (165873/100000000000000)
theorem h368 : Model (fun x => f368 ((93/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(77096023263419/2000000000000),(54960016545527/100000000000000),(49715970483/20000000000000),(366333/156250000000)⟩
def e369 : ℝ := (354289/25000000000000)
theorem h369 : Model (fun x => f369 ((93/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(24775165874179/2500000000000),(209594342471/6250000000000),(-109902317/2500000000000),(720349/12500000000000)⟩
def e370 : ℝ := (1477/12500000000000)
theorem h370 : Model (fun x => f370 ((93/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(114445884599043/10000000000000),(4392056399737/100000000000000),(-4000325211/100000000000000),(2940487/100000000000000)⟩
def e371 : ℝ := (24557/100000000000000)
theorem h371 : Model (fun x => f371 ((93/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(124445884599043/10000000000000),(4392056399737/100000000000000),(-4000325211/100000000000000),(2940487/100000000000000)⟩
def e372 : ℝ := (24557/100000000000000)
theorem h372 : Model (fun x => f372 ((93/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(11992853517605719/25000000000000),(2133149572107/250000000000),(1338286075987/25000000000000),(11750210437/100000000000000)⟩
def e373 : ℝ := (4125977/20000000000000)
theorem h373 : Model (fun x => f373 ((93/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(208457478141/100000000000000),(-3707799647/100000000000000),(10672051/25000000000000),(-198297/50000000000000)⟩
def e374 : ℝ := (3387/100000000000000)
theorem h374 : Model (fun x => f374 ((93/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (23556394663217903/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(21410950034127/100000000000000),(67678846389/20000000000000),(-40646123/4000000000000),(1687113/50000000000000)⟩
def e375 : ℝ := (9411/1250000000000)
theorem h375 : Model (fun x => f375 ((93/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(14775165874179/5000000000000),(167675473977/10000000000000),(-109902317/5000000000000),(1440699/50000000000000)⟩
def e376 : ℝ := (369/6250000000000)
theorem h376 : Model (fun x => f376 ((93/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(8072599837099/20000000000000),(-136586068767/100000000000000),(641249149/100000000000000),(-3010559/100000000000000)⟩
def e377 : ℝ := (14377/100000000000000)
theorem h377 : Model (fun x => f377 ((93/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (61728045226271/25000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(7454625101813/6250000000000),(273172137529/100000000000000),(-12824983/1000000000000),(6021117/100000000000000)⟩
def e378 : ℝ := (56857/50000000000000)
theorem h378 : Model (fun x => f378 ((93/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1204625101813/6250000000000),(273172137529/100000000000000),(-12824983/1000000000000),(6021117/100000000000000)⟩
def e379 : ℝ := (56857/50000000000000)
theorem h379 : Model (fun x => f379 ((93/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(27511116447167/6250000000000),(252033817363/25000000000000),(-4733029441/100000000000000),(5555197/25000000000000)⟩
def e380 : ℝ := (419661/100000000000000)
theorem h380 : Model (fun x => f380 ((93/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2795892148868957/100000000000000),(252033817363/25000000000000),(-4733029441/100000000000000),(5555197/25000000000000)⟩
def e381 : ℝ := (209831/50000000000000)
theorem h381 : Model (fun x => f381 ((93/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1667386223593633/50000000000000),(8840041623779/100000000000000),(-38748598227/100000000000000),(6759557/4000000000000)⟩
def e382 : ℝ := (241553/6250000000000)
theorem h382 : Model (fun x => f382 ((93/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4308576699784109/50000000000000),(8840041623779/100000000000000),(-38748598227/100000000000000),(6759557/4000000000000)⟩
def e383 : ℝ := (3864849/100000000000000)
theorem h383 : Model (fun x => f383 ((93/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(5139011843087557/50000000000000),(4260441690763/12500000000000),(-132583318877/100000000000000),(501184983/100000000000000)⟩
def e384 : ℝ := (7962369/50000000000000)
theorem h384 : Model (fun x => f384 ((93/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(15547071305222733/100000000000000),(4260441690763/12500000000000),(-132583318877/100000000000000),(501184983/100000000000000)⟩
def e385 : ℝ := (15924739/100000000000000)
theorem h385 : Model (fun x => f385 ((93/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(18543614081854397/100000000000000),(83123061340783/100000000000000),(-66105409507/25000000000000),(734589313/100000000000000)⟩
def e386 : ℝ := (2618251/6250000000000)
theorem h386 : Model (fun x => f386 ((93/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(10439664183784341/50000000000000),(83123061340783/100000000000000),(-66105409507/25000000000000),(734589313/100000000000000)⟩
def e387 : ℝ := (41892017/100000000000000)
theorem h387 : Model (fun x => f387 ((93/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(24903610457259799/100000000000000),(156180709141073/100000000000000),(-356094256771/100000000000000),(344964769/100000000000000)⟩
def e388 : ℝ := (84347027/100000000000000)
theorem h388 : Model (fun x => f388 ((93/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(25305991409640751/100000000000000),(156180709141073/100000000000000),(-356094256771/100000000000000),(344964769/100000000000000)⟩
def e389 : ℝ := (21086757/25000000000000)
theorem h389 : Model (fun x => f389 ((93/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(30183468606171533/100000000000000),(12770594961087/5000000000000),(-322634597681/100000000000000),(-520304299/50000000000000)⟩
def e390 : ℝ := (144728997/100000000000000)
theorem h390 : Model (fun x => f390 ((93/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(6033169911710497/20000000000000),(12770594961087/5000000000000),(-322634597681/100000000000000),(-520304299/50000000000000)⟩
def e391 : ℝ := (72364499/50000000000000)
theorem h391 : Model (fun x => f391 ((93/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(35980015893871993/100000000000000),(193522344440649/50000000000000),(-9247694807/12500000000000),(-3581855513/100000000000000)⟩
def e392 : ℝ := (224294819/100000000000000)
theorem h392 : Model (fun x => f392 ((93/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(17991674613602663/50000000000000),(193522344440649/50000000000000),(-9247694807/12500000000000),(-3581855513/100000000000000)⟩
def e393 : ℝ := (11214741/5000000000000)
theorem h393 : Model (fun x => f393 ((93/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(866928914527899/12500000000000),(43223870969613/25000000000000),(116310640181/20000000000000),(-3689705893/100000000000000)⟩
def e394 : ℝ := (99714801/100000000000000)
theorem h394 : Model (fun x => f394 ((93/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(71131437322983/50000000000000),(162911669883/25000000000000),(-28914299/1250000000000),(3678199/50000000000000)⟩
def e395 : ℝ := (80347/25000000000000)
theorem h395 : Model (fun x => f395 ((93/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(13704625101813/6250000000000),(273172137529/100000000000000),(-12824983/1000000000000),(6021117/100000000000000)⟩
def e396 : ℝ := (56857/50000000000000)
theorem h396 : Model (fun x => f396 ((93/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(240405438951991/50000000000000),(119799095459/10000000000000),(-121953513/2500000000000),(2424829/12500000000000)⟩
def e397 : ℝ := (34301/6250000000000)
theorem h397 : Model (fun x => f397 ((93/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(8434346017981/800000000000),(157612962317/4000000000000),(-13590307761/100000000000000),(42796407/100000000000000)⟩
def e398 : ℝ := (970633/50000000000000)
theorem h398 : Model (fun x => f398 ((93/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1155895501553989/50000000000000),(11520141651951/100000000000000),(-8139359311/25000000000000),(69662101/100000000000000)⟩
def e399 : ℝ := (2997611/50000000000000)
theorem h399 : Model (fun x => f399 ((93/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1644410168414111/50000000000000),(1258143759473/4000000000000),(-12360789307/50000000000000),(-209469061/100000000000000)⟩
def e400 : ℝ := (18093663/100000000000000)
theorem h400 : Model (fun x => f400 ((93/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(7454625101813/781250000000),(273172137529/12500000000000),(-12824983/125000000000),(6021117/12500000000000)⟩
def e401 : ℝ := (56857/6250000000000)
theorem h401 : Model (fun x => f401 ((93/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(109645488767803/10000000000000),(709255944941/25000000000000),(-157164129/1250000000000),(27762667/50000000000000)⟩
def e402 : ℝ := (12311/1000000000000)
theorem h402 : Model (fun x => f402 ((93/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(119645488767803/10000000000000),(709255944941/25000000000000),(-157164129/1250000000000),(27762667/50000000000000)⟩
def e403 : ℝ := (12311/1000000000000)
theorem h403 : Model (fun x => f403 ((93/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(39349251666930311/100000000000000),(469632677635301/100000000000000),(91527869209/50000000000000),(-5336132769/100000000000000)⟩
def e404 : ℝ := (272517353/100000000000000)
theorem h404 : Model (fun x => f404 ((93/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(31766804883/12500000000000),(-3033090391/100000000000000),(35017631/100000000000000),(-184681/50000000000000)⟩
def e405 : ℝ := (5693/100000000000000)
theorem h405 : Model (fun x => f405 ((93/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (3887943032490647/10000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(2203164934019/12500000000000),(114514533647/50000000000000),(-1337525597/100000000000000),(7911207/100000000000000)⟩
def e406 : ℝ := (123461/12500000000000)
theorem h406 : Model (fun x => f406 ((93/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(39036269506279/100000000000000),(567423299239/100000000000000),(-147104917/6250000000000),(11285433/100000000000000)⟩
def e407 : ℝ := (217571/12500000000000)
theorem h407 : Model (fun x => f407 ((93/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(251221280306549/100000000000000),(102986550433/2500000000000),(-4940006811/100000000000000),(106144667/100000000000000)⟩
def e408 : ℝ := (2520387/20000000000000)
theorem h408 : Model (fun x => f408 ((93/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(108052163572709/100000000000000),(30498019957/5000000000000),(-2170862021/25000000000000),(139024029/100000000000000)⟩
def e409 : ℝ := (1982107/20000000000000)
theorem h409 : Model (fun x => f409 ((93/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1390853979/78125000000),(16991626979/20000000000000),(4944789/5000000000000),(-10244539/100000000000000)⟩
def e410 : ℝ := (690579/1000000000000)
theorem h410 : Model (fun x => f410 ((93/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(2428977473876953/25000000000000),(122735137939453/25000000000000),(1011933/10240000),(10137/10240000)⟩
def e411 : ℝ := (247070313/50000000000000)
theorem h411 : Model (fun x => f411 ((93/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(45369/1600),(213/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((93/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(9663597/64000),(136107/64000),(639/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((93/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(91690075896972271/6250000000000),(47395742119476707/50000000000000),(2633220413540221/100000000000000),(20508572729553/50000000000000)⟩
def e414 : ℝ := (19683923179/5000000000000)
theorem h414 : Model (fun x => f414 ((93/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(170411027/2500000000000),(-440437911/100000000000000),(16223519/100000000000000),(-448299/100000000000000)⟩
def e415 : ℝ := (15509/100000000000000)
theorem h415 : Model (fun x => f415 ((93/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (273915019775028003/20000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2842215040177/50000000000000),(-4321418401/50000000000000),(-429583319/100000000000000),(1192581/12500000000000)⟩
def e416 : ℝ := (24873593/100000000000000)
theorem h416 : Model (fun x => f416 ((93/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1952068493617/50000000000000),(76315298093/100000000000000),(-330687539/100000000000000),(-703891/100000000000000)⟩
def e417 : ℝ := (93931493/100000000000000)
theorem h417 : Model (fun x => f417 ((93/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((93/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((2927949619921/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (23/10) (47/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (23/10) (47/20) ≤ (5856181034321/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(93/40)-(1/40)) (by norm_num : ((93/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel26


noncomputable section
namespace Hf4Quad.Panel27
open Hf4Quad.Dag

def p0 : Cubic := ⟨(19/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((19/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((19/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((19/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((19/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(104047619047619/25000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((19/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-104047619047619/25000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((19/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-64952380952381/20000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((19/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((19/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(361/64),(19/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((19/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(136568783068783/20000000000000),(14375661375661/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((19/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-136568783068783/20000000000000),(-14375661375661/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((19/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-50380291005291/5000000000000),(-18756613756613/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((19/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((19/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(6859/512),(1083/2560),(57/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((19/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(652582447193287/5000000000000),(103039333767361/25000000000000),(271156141493/6250000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((19/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-652582447193287/5000000000000),(-103039333767361/25000000000000),(-271156141493/6250000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((19/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-351481369099289/2500000000000),(-430913948826057/100000000000000),(-4414159639549/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((19/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((19/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(130321/4096),(6859/5120),(1083/51200),(19/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((19/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(277764408172123/3125000000000),(93562748015873/25000000000000),(1477306547619/25000000000000),(2591765873/6250000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((19/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-646349212807953/12500000000000),(-11332591352513/20000000000000),(1495066550927/100000000000000),(26245453043/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((19/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((19/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(7556454467773437/100000000000000),(99427032470703/25000000000000),(6859/81920),(361/409600)⟩
def e22 : ℝ := (464843751/100000000000000)
theorem h22 : Model (fun x => f22 ((19/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(3076806344632749/6250000000000),(1295497408266419/50000000000000),(13636814823857/25000000000000),(574181676793/100000000000000)⟩
def e23 : ℝ := (3028370957/100000000000000)
theorem h23 : Model (fun x => f23 ((19/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(1101452695291509/2500000000000),(2534331859770273/100000000000000),(11208465169271/20000000000000),(150106782459/25000000000000)⟩
def e24 : ℝ := (62749959/2000000000000)
theorem h24 : Model (fun x => f24 ((19/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((19/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(2243322420120239/12500000000000),(566734085083007/50000000000000),(2982810974121/10000000000000),(209320068359/50000000000000)⟩
def e26 : ℝ := (1659497073/50000000000000)
theorem h26 : Model (fun x => f26 ((19/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(805981828655263/2000000000000),(2545205774700827/100000000000000),(6697909933423/10000000000000),(940057534513/100000000000000)⟩
def e27 : ℝ := (3726405069/50000000000000)
theorem h27 : Model (fun x => f27 ((19/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(8435719924442351/10000000000000),(50795376344711/1000000000000),(24604285036117/20000000000000),(1540484664349/100000000000000)⟩
def e28 : ℝ := (1323788511/12500000000000)
theorem h28 : Model (fun x => f28 ((19/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((19/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(42623125982284541/100000000000000),(3140651388168331/100000000000000),(24794616222381/25000000000000),(347994613647/20000000000000)⟩
def e30 : ℝ := (18431589369/100000000000000)
theorem h30 : Model (fun x => f30 ((19/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(10114535451351649/100000000000000),(372640779786639/50000000000000),(11767603572209/50000000000000),(206449185477/50000000000000)⟩
def e31 : ℝ := (546730677/12500000000000)
theorem h31 : Model (fun x => f31 ((19/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(94471734695775159/100000000000000),(2912409597022189/50000000000000),(146556632325003/100000000000000),(1953383035303/100000000000000)⟩
def e32 : ℝ := (467629797/3125000000000)
theorem h32 : Model (fun x => f32 ((19/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((19/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(774345/64),(8151/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((19/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((19/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(41971/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((19/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1445881/64),(58427/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((19/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((19/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1591801/64),(58427/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((19/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1591801/64),(-58427/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((19/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((19/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(27/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((19/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(729/64),(27/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((19/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((19/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(76545/32),(567/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((19/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(2612842119/6250000000000),(-123868071/20000000000000),(6881559/100000000000000),(-67967/100000000000000)⟩
def e46 : ℝ := (323/50000000000000)
theorem h46 : Model (fun x => f46 ((19/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (188517/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-51989058723329/5000000000000),(138112920527/100000000000000),(-1039102971/100000000000000),(1568131/20000000000000)⟩
def e47 : ℝ := (31988961/100000000000000)
theorem h47 : Model (fun x => f47 ((19/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((19/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(35/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((19/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((19/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((19/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(145833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((19/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(245833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((19/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((19/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(24583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((19/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((19/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(516249999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((19/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((19/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(4583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((19/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(295768229166641/50000000000000),(2552083333329/20000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (1/800000000000)
theorem h60 : Model (fun x => f60 ((19/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(3777126736111/2500000000000),(1024305555553/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((19/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((19/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(24583333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((19/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(138025173611109/10000000000000),(5190972222213/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((19/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(148025173611109/10000000000000),(5190972222213/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((19/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(8756228694208461/100000000000000),(54898195619841/25000000000000),(1212334526901/100000000000000),(2114076967/100000000000000)⟩
def e66 : ℝ := (635131/100000000000000)
theorem h66 : Model (fun x => f66 ((19/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(44583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((19/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(49691840277777/10000000000000),(371527777777/20000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((19/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1107713939525437/100000000000000),(621148003471/10000000000000),(2322048611/20000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (33/50000000000000)
theorem h69 : Model (fun x => f69 ((19/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(96993965822473273/100000000000000),(2976351258849993/100000000000000),(28085779823381/100000000000000),(62425252923/50000000000000)⟩
def e70 : ℝ := (147684767/50000000000000)
theorem h70 : Model (fun x => f70 ((19/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((19/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(79319661458331/312500000000),(21510416666613/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((19/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1454193793402629/25000000000000),(72597656249863/50000000000000),(783854166659/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (187/12500000000000)
theorem h73 : Model (fun x => f73 ((19/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(503384604913583/781250000000),(1969656544669769/100000000000000),(18376981452507/100000000000000),(39714524369/50000000000000)⟩
def e74 : ℝ := (44303933/25000000000000)
theorem h74 : Model (fun x => f74 ((19/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(161427195251411897/100000000000000),(2473003901759881/50000000000000),(2903922579743/6250000000000),(25534944323/12500000000000)⟩
def e75 : ℝ := (236292633/50000000000000)
theorem h75 : Model (fun x => f75 ((19/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((19/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(26439887152777/312500000000),(7170138888871/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((19/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(525173611111/10000000000000),(190972222221/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((19/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(240704571759/20000000000000),(16411675347/25000000000000),(298394097/25000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((19/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(101827227431447/100000000000000),(6244566489561/100000000000000),(69905724507/50000000000000),(1360506259/100000000000000)⟩
def e80 : ℝ := (664649/12500000000000)
theorem h80 : Model (fun x => f80 ((19/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(45397972229853/20000000000000),(14344459580609/100000000000000),(422102561/125000000000),(1807671453/50000000000000)⟩
def e81 : ℝ := (3508769/20000000000000)
theorem h81 : Model (fun x => f81 ((19/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(80827092556280581/50000000000000),(4960352263100371/100000000000000),(2925027707793/6250000000000),(20789489749/10000000000000)⟩
def e82 : ℝ := (490129111/100000000000000)
theorem h82 : Model (fun x => f82 ((19/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(275807321807/100000000000000),(20058714313/100000000000000),(136763961/25000000000000),(6630979/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((19/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(3160292229/5000000000000),(574598587/10000000000000),(10447247/5000000000000),(1899499/50000000000000)⟩
def e84 : ℝ := (17333/50000000000000)
theorem h84 : Model (fun x => f84 ((19/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(3621168179/25000000000000),(790073057/50000000000000),(71824823/100000000000000),(1741207/100000000000000)⟩
def e85 : ℝ := (299/1250000000000)
theorem h85 : Model (fun x => f85 ((19/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(829851041/25000000000000),(21123481/5000000000000),(23043797/100000000000000),(87287/12500000000000)⟩
def e86 : ℝ := (12839/100000000000000)
theorem h86 : Model (fun x => f86 ((19/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(2489553123/25000000000000),(63370443/5000000000000),(69131391/100000000000000),(261861/12500000000000)⟩
def e87 : ℝ := (38517/100000000000000)
theorem h87 : Model (fun x => f87 ((19/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-2489553123/25000000000000),(-63370443/5000000000000),(-69131391/100000000000000),(-261861/12500000000000)⟩
def e88 : ℝ := (38517/100000000000000)
theorem h88 : Model (fun x => f88 ((19/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(16165417515434867/10000000000000),(4960350995691511/100000000000000),(46800374193297/100000000000000),(103946401301/50000000000000)⟩
def e89 : ℝ := (122541907/25000000000000)
theorem h89 : Model (fun x => f89 ((19/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(79319661458331/250000000000),(21510416666613/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((19/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2469278990192101/100000000000000),(2307737374007/12500000000000),(51762333621/100000000000000),(64501349/100000000000000)⟩
def e91 : ℝ := (6067/20000000000000)
theorem h91 : Model (fun x => f91 ((19/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(39172474709641377/5000000000000),(2233817661245137/20000000000000),(32568988372607/50000000000000),(39823368757/20000000000000)⟩
def e92 : ℝ := (84362449/25000000000000)
theorem h92 : Model (fun x => f92 ((19/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(12764064657/100000000000000),(-181968291/100000000000000),(1532957/100000000000000),(-997/10000000000000)⟩
def e93 : ℝ := (71/100000000000000)
theorem h93 : Model (fun x => f93 ((19/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (38610753422778153/5000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(20633643437441/100000000000000),(67796613689/20000000000000),(-574546919/100000000000000),(1296857/100000000000000)⟩
def e94 : ℝ := (42339/12500000000000)
theorem h94 : Model (fun x => f94 ((19/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(145833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((19/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(8135593220339/20000000000000),(-27578282103/20000000000000),(46742851/10000000000000),(-198063/12500000000000)⟩
def e96 : ℝ := (5393/100000000000000)
theorem h96 : Model (fun x => f96 ((19/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (30624999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(926906779661/781250000000),(11031312841/4000000000000),(-467428511/50000000000000),(633801/20000000000000)⟩
def e97 : ℝ := (10559/25000000000000)
theorem h97 : Model (fun x => f97 ((19/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(19465042372881/781250000000),(231657569661/4000000000000),(-9815998731/50000000000000),(13309821/20000000000000)⟩
def e98 : ℝ := (221739/25000000000000)
theorem h98 : Model (fun x => f98 ((19/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(145656779661/781250000000),(11031312841/4000000000000),(-467428511/50000000000000),(633801/20000000000000)⟩
def e99 : ℝ := (10559/25000000000000)
theorem h99 : Model (fun x => f99 ((19/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(116130422292429/25000000000000),(7950958958703/100000000000000),(-5490304389/50000000000000),(-528729/3125000000000)⟩
def e100 : ℝ := (1774437/100000000000000)
theorem h100 : Model (fun x => f100 ((19/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(140764148233261/100000000000000),(81799989287/12500000000000),(-291548631/20000000000000),(1181661/50000000000000)⟩
def e101 : ℝ := (7921/6250000000000)
theorem h101 : Model (fun x => f101 ((19/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(926906779661/78125000000),(11031312841/400000000000),(-467428511/5000000000000),(633801/2000000000000)⟩
def e102 : ℝ := (10559/2500000000000)
theorem h102 : Model (fun x => f102 ((19/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1327204826199341/100000000000000),(1706114062273/50000000000000),(-86450507/800000000000),(8513343/25000000000000)⟩
def e103 : ℝ := (68637/12500000000000)
theorem h103 : Model (fun x => f103 ((19/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1427204826199341/100000000000000),(1706114062273/50000000000000),(-86450507/800000000000),(8513343/25000000000000)⟩
def e104 : ℝ := (68637/12500000000000)
theorem h104 : Model (fun x => f104 ((19/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(828709495821611/12500000000000),(129327009710203/100000000000000),(64391409907/100000000000000),(-131717713/10000000000000)⟩
def e105 : ℝ := (31298741/100000000000000)
theorem h105 : Model (fun x => f105 ((19/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(1708156779661/781250000000),(11031312841/4000000000000),(-467428511/50000000000000),(633801/20000000000000)⟩
def e106 : ℝ := (10559/25000000000000)
theorem h106 : Model (fun x => f106 ((19/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(478052283826477/100000000000000),(602982778173/50000000000000),(-3327457199/100000000000000),(2175333/25000000000000)⟩
def e107 : ℝ := (26401/12500000000000)
theorem h107 : Model (fun x => f107 ((19/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(209046591910559/20000000000000),(3955158222931/100000000000000),(-8418547287/100000000000000),(13723837/100000000000000)⟩
def e108 : ℝ := (75831/10000000000000)
theorem h108 : Model (fun x => f108 ((19/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(13859111662834033/20000000000000),(1613982705240673/100000000000000),(5230005692271/100000000000000),(-21198396899/100000000000000)⟩
def e109 : ℝ := (83905709/20000000000000)
theorem h109 : Model (fun x => f109 ((19/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2956047112898481/12500000000000),(1717799775027/1562500000000),(-6122521251/2500000000000),(24814881/6250000000000)⟩
def e110 : ℝ := (166341/781250000000)
theorem h110 : Model (fun x => f110 ((19/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(4409019422627729/100000000000000),(4285764862443/5000000000000),(36455394879/100000000000000),(-219931593/25000000000000)⟩
def e111 : ℝ := (20943117/100000000000000)
theorem h111 : Model (fun x => f111 ((19/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(23042262099194683/50000000000000),(53515411623421/5000000000000),(3400044045271/100000000000000),(-7182108819/50000000000000)⟩
def e112 : ℝ := (27999811/10000000000000)
theorem h112 : Model (fun x => f112 ((19/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(115380082512559531/100000000000000),(2684290937709093/100000000000000),(4315024868771/50000000000000),(-35562614537/100000000000000)⟩
def e113 : ℝ := (139905331/20000000000000)
theorem h113 : Model (fun x => f113 ((19/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(985349037632827/12500000000000),(572599925009/1562500000000),(-2040840417/2500000000000),(8271627/6250000000000)⟩
def e114 : ℝ := (55447/781250000000)
theorem h114 : Model (fun x => f114 ((19/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(695202528009/20000000000000),(51417136123/50000000000000),(411970889/100000000000000),(-124209/3125000000000)⟩
def e115 : ℝ := (5283/12500000000000)
theorem h115 : Model (fun x => f115 ((19/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(162017538307/25000000000000),(28758737153/100000000000000),(8197791/2500000000000),(-456097/100000000000000)⟩
def e116 : ℝ := (4223/20000000000000)
theorem h116 : Model (fun x => f116 ((19/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(51086024144141/100000000000000),(626121466927/25000000000000),(35858590879/100000000000000),(30797757/50000000000000)⟩
def e117 : ℝ := (2117843/100000000000000)
theorem h117 : Model (fun x => f117 ((19/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(111696561264307/100000000000000),(2808398128541/50000000000000),(42416021123/50000000000000),(211772327/100000000000000)⟩
def e118 : ℝ := (2372801/50000000000000)
theorem h118 : Model (fun x => f118 ((19/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(57745889536911919/50000000000000),(107596309358647/4000000000000),(2178720444947/25000000000000),(-3535084221/10000000000000)⟩
def e119 : ℝ := (704272257/100000000000000)
theorem h119 : Model (fun x => f119 ((19/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(120826638737/100000000000000),(7149064603/100000000000000),(26877839/20000000000000),(570973/100000000000000)⟩
def e120 : ℝ := (771/10000000000000)
theorem h120 : Model (fun x => f120 ((19/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(11263500221/50000000000000),(416523891/25000000000000),(10910487/25000000000000),(41407/10000000000000)⟩
def e121 : ℝ := (2061/100000000000000)
theorem h121 : Model (fun x => f121 ((19/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2099974617/50000000000000),(372753583/100000000000000),(3130211/25000000000000),(91347/50000000000000)⟩
def e122 : ℝ := (1193/100000000000000)
theorem h122 : Model (fun x => f122 ((19/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(391520691/50000000000000),(81079169/100000000000000),(3323121/100000000000000),(1631/2500000000000)⟩
def e123 : ℝ := (63/10000000000000)
theorem h123 : Model (fun x => f123 ((19/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(1174562073/50000000000000),(243237507/100000000000000),(9969363/100000000000000),(4893/2500000000000)⟩
def e124 : ℝ := (189/10000000000000)
theorem h124 : Model (fun x => f124 ((19/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-1174562073/50000000000000),(-243237507/100000000000000),(-9969363/100000000000000),(-4893/2500000000000)⟩
def e125 : ℝ := (189/10000000000000)
theorem h125 : Model (fun x => f125 ((19/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(28872944181174923/25000000000000),(672476872682167/25000000000000),(348594872417/4000000000000),(-3535103793/10000000000000)⟩
def e126 : ℝ := (704274147/100000000000000)
theorem h126 : Model (fun x => f126 ((19/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2956047112898481/10000000000000),(1717799775027/1250000000000),(-6122521251/2000000000000),(24814881/5000000000000)⟩
def e127 : ℝ := (166341/625000000000)
theorem h127 : Model (fun x => f127 ((19/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(457067972143421/20000000000000),(5765145884273/50000000000000),(-8635220517/50000000000000),(1468929/50000000000000)⟩
def e128 : ℝ := (586381/25000000000000)
theorem h128 : Model (fun x => f128 ((19/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(168889307431615373/25000000000000),(1309802721641763/20000000000000),(1170044193/31250000000),(-46820423967/100000000000000)⟩
def e129 : ℝ := (711055431/50000000000000)
theorem h129 : Model (fun x => f129 ((19/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(7401297447/50000000000000),(-143499901/100000000000000),(1309081/100000000000000),(-1087/10000000000000)⟩
def e130 : ℝ := (31/25000000000000)
theorem h130 : Model (fun x => f130 ((19/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (83625552966787531/12500000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(427394496111/2500000000000),(58111380903/25000000000000),(-1058106511/100000000000000),(615051/12500000000000)⟩
def e131 : ℝ := (190411/50000000000000)
theorem h131 : Model (fun x => f131 ((19/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(37729423281881/100000000000000),(571428592057/100000000000000),(-163265343/10000000000000),(1243453/20000000000000)⟩
def e132 : ℝ := (359767/50000000000000)
theorem h132 : Model (fun x => f132 ((19/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-39230344051981/10000000000000),(-736187214667/12500000000000),(2171649021/12500000000000),(-34940177/50000000000000)⟩
def e133 : ℝ := (198057/1000000000000)
theorem h133 : Model (fun x => f133 ((19/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(21052631578947/50000000000000),(-443213296399/100000000000000),(4665403119/100000000000000),(-49109507/100000000000000)⟩
def e134 : ℝ := (130611/25000000000000)
theorem h134 : Model (fun x => f134 ((19/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (47/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-165180396008339/100000000000000),(-185261875487/25000000000000),(3023105661/20000000000000),(-18853413/10000000000000)⟩
def e135 : ℝ := (2906553/20000000000000)
theorem h135 : Model (fun x => f135 ((19/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(651605/2048),(6859/512),(1083/5120),(19/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((19/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((19/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(61731/256),(9747/1280),(513/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((19/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(1145453/2048),(53789/2560),(7467/25600),(113/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((19/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-361/64),(-19/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((19/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(1133901/2048),(10697/512),(7451/25600),(113/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((19/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((19/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(57/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((19/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-57/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((19/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(1104717/2048),(53101/2560),(7451/25600),(113/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((19/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(1110861/2048),(53101/2560),(7451/25600),(113/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((19/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((19/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(1110861/32),(53101/40),(7451/400),(113/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((19/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((19/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(123153345/4096),(1296351/1024),(204687/10240),(3591/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((19/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(3325934833/100000000000000),(-70019681/50000000000000),(1842623/50000000000000),(-15517/20000000000000)⟩
def e151 : ℝ := (81/5000000000000)
theorem h151 : Model (fun x => f151 ((19/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (7367843133/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(115457852953787/100000000000000),(-446121664281/100000000000000),(3979223837/100000000000000),(-33813593/100000000000000)⟩
def e152 : ℝ := (11049683/10000000000000)
theorem h152 : Model (fun x => f152 ((19/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(43/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((19/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1505/64),(39/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((19/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(81/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((19/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(2469135802469/50000000000000),(-36579789667/100000000000000),(67740351/25000000000000),(-1003561/50000000000000)⟩
def e156 : ℝ := (7491/50000000000000)
theorem h156 : Model (fun x => f156 ((19/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (201/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(11612654320987/10000000000000),(68701417463/20000000000000),(541922787/100000000000000),(-802851/20000000000000)⟩
def e157 : ℝ := (338557/50000000000000)
theorem h157 : Model (fun x => f157 ((19/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(21612654320987/10000000000000),(68701417463/20000000000000),(541922787/100000000000000),(-802851/20000000000000)⟩
def e158 : ℝ := (338557/50000000000000)
theorem h158 : Model (fun x => f158 ((19/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(21612654320987/20000000000000),(171753543657/100000000000000),(270961393/100000000000000),(-250891/12500000000000)⟩
def e159 : ℝ := (338559/100000000000000)
theorem h159 : Model (fun x => f159 ((19/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(1612654320987/20000000000000),(171753543657/100000000000000),(270961393/100000000000000),(-250891/12500000000000)⟩
def e160 : ℝ := (338559/100000000000000)
theorem h160 : Model (fun x => f160 ((19/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((19/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((19/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(199402465461487/50000000000000),(79231545437/12500000000000),(999976569/100000000000000),(-7407259/100000000000000)⟩
def e163 : ℝ := (624723/50000000000000)
theorem h163 : Model (fun x => f163 ((19/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2754519216637259/100000000000000),(79231545437/12500000000000),(999976569/100000000000000),(-7407259/100000000000000)⟩
def e164 : ℝ := (1249447/100000000000000)
theorem h164 : Model (fun x => f164 ((19/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((19/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2976623582484849/100000000000000),(2707972983213/50000000000000),(9632954931/100000000000000),(-59856263/100000000000000)⟩
def e166 : ℝ := (5351471/50000000000000)
theorem h166 : Model (fun x => f166 ((19/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8259004534865801/100000000000000),(2707972983213/50000000000000),(9632954931/100000000000000),(-59856263/100000000000000)⟩
def e167 : ℝ := (10702943/100000000000000)
theorem h167 : Model (fun x => f167 ((19/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((19/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8924950502375929/100000000000000),(20037781359099/100000000000000),(21045239553/50000000000000),(-39846273/20000000000000)⟩
def e169 : ℝ := (19875051/50000000000000)
theorem h169 : Model (fun x => f169 ((19/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3548499530355887/25000000000000),(20037781359099/100000000000000),(21045239553/50000000000000),(-39846273/20000000000000)⟩
def e170 : ℝ := (39750103/100000000000000)
theorem h170 : Model (fun x => f170 ((19/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((19/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(153384987415533/1000000000000),(46032176853839/100000000000000),(59180101671/50000000000000),(-373601101/100000000000000)⟩
def e172 : ℝ := (22944599/25000000000000)
theorem h172 : Model (fun x => f172 ((19/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(3534842605453517/20000000000000),(46032176853839/100000000000000),(59180101671/50000000000000),(-373601101/100000000000000)⟩
def e173 : ℝ := (91778397/100000000000000)
theorem h173 : Model (fun x => f173 ((19/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((19/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(9549666413845487/50000000000000),(80099963487047/100000000000000),(254856096799/100000000000000),(-21522619/5000000000000)⟩
def e175 : ℝ := (80289397/50000000000000)
theorem h175 : Model (fun x => f175 ((19/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(9750856890035963/50000000000000),(80099963487047/100000000000000),(254856096799/100000000000000),(-21522619/5000000000000)⟩
def e176 : ℝ := (32115759/20000000000000)
theorem h176 : Model (fun x => f176 ((19/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((19/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(21074189929776161/100000000000000),(6002676279479/5000000000000),(465822477159/100000000000000),(-788363/390625000000)⟩
def e178 : ℝ := (30220319/12500000000000)
theorem h178 : Model (fun x => f178 ((19/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(21056570882157113/100000000000000),(6002676279479/5000000000000),(465822477159/100000000000000),(-788363/390625000000)⟩
def e179 : ℝ := (241762553/100000000000000)
theorem h179 : Model (fun x => f179 ((19/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((19/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(11377209691535549/50000000000000),(2073739676149/1250000000000),(383317185477/50000000000000),(484638689/100000000000000)⟩
def e181 : ℝ := (167436667/50000000000000)
theorem h181 : Model (fun x => f181 ((19/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(22757752716404431/100000000000000),(2073739676149/1250000000000),(383317185477/50000000000000),(484638689/100000000000000)⟩
def e182 : ℝ := (66974667/20000000000000)
theorem h182 : Model (fun x => f182 ((19/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(917509706351581/50000000000000),(52464147744497/100000000000000),(408418245723/100000000000000),(674272459/50000000000000)⟩
def e183 : ℝ := (10562473/10000000000000)
theorem h183 : Model (fun x => f183 ((19/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(116776706699619/100000000000000),(185602498373/50000000000000),(880612289/100000000000000),(-681433/20000000000000)⟩
def e184 : ℝ := (369527/50000000000000)
theorem h184 : Model (fun x => f184 ((19/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(41612654320987/20000000000000),(171753543657/100000000000000),(270961393/100000000000000),(-250891/12500000000000)⟩
def e185 : ℝ := (338559/100000000000000)
theorem h185 : Model (fun x => f185 ((19/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(432903249909489/100000000000000),(35735604203/5000000000000),(56901403/4000000000000),(-7421421/100000000000000)⟩
def e186 : ℝ := (354043/25000000000000)
theorem h186 : Model (fun x => f186 ((19/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(90071266464577/10000000000000),(139411251061/6250000000000),(167509907/3125000000000),(-9875163/50000000000000)⟩
def e187 : ℝ := (1110079/25000000000000)
theorem h187 : Model (fun x => f187 ((19/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(74962089512879/4000000000000),(3094011839391/50000000000000),(8712267387/50000000000000),(-21960543/50000000000000)⟩
def e188 : ℝ := (3091913/25000000000000)
theorem h188 : Model (fun x => f188 ((19/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1094228242579507/50000000000000),(14182745810299/100000000000000),(5982118527/10000000000000),(403159/10000000000000)⟩
def e189 : ℝ := (28606091/100000000000000)
theorem h189 : Model (fun x => f189 ((19/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((19/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(21612654320987/2500000000000),(171753543657/12500000000000),(270961393/12500000000000),(-250891/1562500000000)⟩
def e191 : ℝ := (338559/12500000000000)
theorem h191 : Model (fun x => f191 ((19/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(981282879539099/100000000000000),(872616673001/50000000000000),(3048303433/100000000000000),(-19464189/100000000000000)⟩
def e192 : ℝ := (1723763/50000000000000)
theorem h192 : Model (fun x => f192 ((19/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1081282879539099/100000000000000),(872616673001/50000000000000),(3048303433/100000000000000),(-19464189/100000000000000)⟩
def e193 : ℝ := (1723763/50000000000000)
theorem h193 : Model (fun x => f193 ((19/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(23663405300187541/100000000000000),(3830985492741/2000000000000),(120133629761/12500000000000),(546989993/50000000000000)⟩
def e194 : ℝ := (193314849/50000000000000)
theorem h194 : Model (fun x => f194 ((19/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(211296723213/50000000000000),(-1710393477/50000000000000),(10527131/100000000000000),(34181/100000000000000)⟩
def e195 : ℝ := (7573/100000000000000)
theorem h195 : Model (fun x => f195 ((19/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (23470893475902719/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(969333972341/12500000000000),(79468972709/50000000000000),(31109229/25000000000000),(-2122059/100000000000000)⟩
def e196 : ℝ := (608039/100000000000000)
theorem h196 : Model (fun x => f196 ((19/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(11612654320987/5000000000000),(68701417463/10000000000000),(541922787/50000000000000),(-802851/10000000000000)⟩
def e197 : ℝ := (338557/25000000000000)
theorem h197 : Model (fun x => f197 ((19/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(46269189575153/100000000000000),(-919241241/1250000000000),(864967/100000000000000),(1042407/100000000000000)⟩
def e198 : ℝ := (74227/50000000000000)
theorem h198 : Model (fun x => f198 ((19/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (215782489508399/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(107461620849693/100000000000000),(73539299279/50000000000000),(-345987/20000000000000),(-416963/20000000000000)⟩
def e199 : ℝ := (493243/50000000000000)
theorem h199 : Model (fun x => f199 ((19/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(7461620849693/100000000000000),(73539299279/50000000000000),(-345987/20000000000000),(-416963/20000000000000)⟩
def e200 : ℝ := (493243/50000000000000)
theorem h200 : Model (fun x => f200 ((19/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(396584553135771/100000000000000),(271395033053/50000000000000),(-1596071/25000000000000),(-7693961/100000000000000)⟩
def e201 : ℝ := (1820303/50000000000000)
theorem h201 : Model (fun x => f201 ((19/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(344037354856257/12500000000000),(271395033053/50000000000000),(-1596071/25000000000000),(-7693961/100000000000000)⟩
def e202 : ℝ := (3640607/100000000000000)
theorem h202 : Model (fun x => f202 ((19/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(59153298857111/2000000000000),(4631333563157/100000000000000),(371927193/50000000000000),(-2626687/4000000000000)⟩
def e203 : ℝ := (15548321/50000000000000)
theorem h203 : Model (fun x => f203 ((19/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4120022947618251/50000000000000),(4631333563157/100000000000000),(371927193/50000000000000),(-2626687/4000000000000)⟩
def e204 : ℝ := (31096643/100000000000000)
theorem h204 : Model (fun x => f204 ((19/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8854886877779741/100000000000000),(8548125068587/50000000000000),(7468511041/100000000000000),(-30167849/12500000000000)⟩
def e205 : ℝ := (14373557/12500000000000)
theorem h205 : Model (fun x => f205 ((19/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(88274590605171/625000000000),(8548125068587/50000000000000),(7468511041/100000000000000),(-30167849/12500000000000)⟩
def e206 : ℝ := (114988457/100000000000000)
theorem h206 : Model (fun x => f206 ((19/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3794452234509903/25000000000000),(9786298105277/25000000000000),(32926373239/100000000000000),(-271559977/50000000000000)⟩
def e207 : ℝ := (26394863/10000000000000)
theorem h207 : Model (fun x => f207 ((19/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(17513523223753897/100000000000000),(9786298105277/25000000000000),(32926373239/100000000000000),(-271559977/50000000000000)⟩
def e208 : ℝ := (263948631/100000000000000)
theorem h208 : Model (fun x => f208 ((19/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(18820315924133343/100000000000000),(847808784701/1250000000000),(92654442217/100000000000000),(-901019603/100000000000000)⟩
def e209 : ℝ := (458802827/100000000000000)
theorem h209 : Model (fun x => f209 ((19/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(3844539375302859/20000000000000),(847808784701/1250000000000),(92654442217/100000000000000),(-901019603/100000000000000)⟩
def e210 : ℝ := (114700707/25000000000000)
theorem h210 : Model (fun x => f210 ((19/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2065702163452557/10000000000000),(101157998110691/100000000000000),(198991047553/100000000000000),(-616953203/50000000000000)⟩
def e211 : ℝ := (686753763/100000000000000)
theorem h211 : Model (fun x => f211 ((19/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(10319701293453261/50000000000000),(101157998110691/100000000000000),(198991047553/100000000000000),(-616953203/50000000000000)⟩
def e212 : ℝ := (171688441/25000000000000)
theorem h212 : Model (fun x => f212 ((19/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(4435887310716643/20000000000000),(4345692764513/3125000000000),(362263722747/100000000000000),(-1465345909/100000000000000)⟩
def e213 : ℝ := (59221431/6250000000000)
theorem h213 : Model (fun x => f213 ((19/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(5545692471729137/25000000000000),(4345692764513/3125000000000),(362263722747/100000000000000),(-1465345909/100000000000000)⟩
def e214 : ℝ := (947542897/100000000000000)
theorem h214 : Model (fun x => f214 ((19/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(331038836584317/20000000000000),(21501199413599/50000000000000),(57794421617/25000000000000),(-41401549/100000000000000)⟩
def e215 : ℝ := (2973693/1000000000000)
theorem h215 : Model (fun x => f215 ((19/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(115479999556431/100000000000000),(158053045933/50000000000000),(212603109/100000000000000),(-4485841/100000000000000)⟩
def e216 : ℝ := (85169/4000000000000)
theorem h216 : Model (fun x => f216 ((19/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(207461620849693/100000000000000),(73539299279/50000000000000),(-345987/20000000000000),(-416963/20000000000000)⟩
def e217 : ℝ := (493243/50000000000000)
theorem h217 : Model (fun x => f217 ((19/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(430403241255817/100000000000000),(305131644491/50000000000000),(209143239/100000000000000),(-8655471/100000000000000)⟩
def e218 : ℝ := (4102197/100000000000000)
theorem h218 : Model (fun x => f218 ((19/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(223230385124733/25000000000000),(1899093166159/100000000000000),(26480259/2000000000000),(-6658211/25000000000000)⟩
def e219 : ℝ := (12793871/100000000000000)
theorem h219 : Model (fun x => f219 ((19/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(463117375208783/25000000000000),(5253185951947/100000000000000),(2762265689/50000000000000),(-35977103/50000000000000)⟩
def e220 : ℝ := (354673/1000000000000)
theorem h220 : Model (fun x => f220 ((19/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2139231771347429/100000000000000),(5961074028053/50000000000000),(13461888687/50000000000000),(-137559737/100000000000000)⟩
def e221 : ℝ := (10134601/12500000000000)
theorem h221 : Model (fun x => f221 ((19/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(107461620849693/12500000000000),(73539299279/6250000000000),(-345987/2500000000000),(-416963/2500000000000)⟩
def e222 : ℝ := (493243/6250000000000)
theorem h222 : Model (fun x => f222 ((19/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(39006918654159/4000000000000),(149273488033/10000000000000),(198763629/100000000000000),(-21164361/100000000000000)⟩
def e223 : ℝ := (10021113/100000000000000)
theorem h223 : Model (fun x => f223 ((19/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(43006918654159/4000000000000),(149273488033/10000000000000),(198763629/100000000000000),(-21164361/100000000000000)⟩
def e224 : ℝ := (10021113/100000000000000)
theorem h224 : Model (fun x => f224 ((19/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(5750110423295709/25000000000000),(5003649116561/3125000000000),(235847626533/50000000000000),(-150616233/10000000000000)⟩
def e225 : ℝ := (1093027783/100000000000000)
theorem h225 : Model (fun x => f225 ((19/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(108693564817/25000000000000),(-121066633/4000000000000),(3038409/25000000000000),(2967/50000000000000)⟩
def e226 : ℝ := (21447/100000000000000)
theorem h226 : Model (fun x => f226 ((19/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (4567970125401941/20000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1799089562061/25000000000000),(17108270537/12500000000000),(-2381789/2500000000000),(-926203/50000000000000)⟩
def e227 : ℝ := (1698097/100000000000000)
theorem h227 : Model (fun x => f227 ((19/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(3737757506743/25000000000000),(147902054857/50000000000000),(7291339/25000000000000),(-794893/20000000000000)⟩
def e228 : ℝ := (288267/12500000000000)
theorem h228 : Model (fun x => f228 ((19/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(17262138263617/100000000000000),(274829290041/100000000000000),(-691037573/100000000000000),(998141/50000000000000)⟩
def e229 : ℝ := (9800803/50000000000000)
theorem h229 : Model (fun x => f229 ((19/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(290730749703/4000000000000),(39209503779/100000000000000),(-87961851/12500000000000),(8247853/100000000000000)⟩
def e230 : ℝ := (1076153/12500000000000)
theorem h230 : Model (fun x => f230 ((19/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-39478031816441/25000000000000),(-701837998169/100000000000000),(14411833497/100000000000000),(-180286277/100000000000000)⟩
def e231 : ℝ := (23141989/100000000000000)
theorem h231 : Model (fun x => f231 ((19/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((19/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-1805/64),(-19/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((19/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(399/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((19/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1387/64),(-11/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((19/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((19/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3051/64),(-11/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((19/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((19/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(381375/32),(-275/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((19/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(551/64),(1/32),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((19/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(935/64),(1/32),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((19/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((19/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(176715/64),(189/32),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((19/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(9054126701/25000000000000),(-4841779/6250000000000),(1715077/100000000000000),(-6983/100000000000000)⟩
def e244 : ℝ := (91/100000000000000)
theorem h244 : Model (fun x => f244 ((19/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1102059/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(215813598162117/50000000000000),(-1545737943757/100000000000000),(-3261211313/50000000000000),(-2087153/4000000000000)⟩
def e245 : ℝ := (288939/12500000000000)
theorem h245 : Model (fun x => f245 ((19/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(171/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((19/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(3097/64),(91/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((19/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(4441/64),(91/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((19/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(1225/64),(7/32),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((19/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(5440225/4096),(26691/1024),(9203/51200),(63/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((19/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((19/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(32805/32),(243/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((19/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(6096631611/6250000000000),(-1445127493/100000000000000),(4014243/25000000000000),(-39647/25000000000000)⟩
def e253 : ℝ := (1501/100000000000000)
theorem h253 : Model (fun x => f253 ((19/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (80793/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(506088984771/390625000000),(623191826529/100000000000000),(298052597/25000000000000),(-3846573/100000000000000)⟩
def e254 : ℝ := (4051111/100000000000000)
theorem h254 : Model (fun x => f254 ((19/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(896713984771/390625000000),(623191826529/100000000000000),(298052597/25000000000000),(-3846573/100000000000000)⟩
def e255 : ℝ := (4051111/100000000000000)
theorem h255 : Model (fun x => f255 ((19/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(896713984771/781250000000),(19474744579/6250000000000),(298052597/50000000000000),(-1923287/100000000000000)⟩
def e256 : ℝ := (2025557/100000000000000)
theorem h256 : Model (fun x => f256 ((19/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(115463984771/781250000000),(19474744579/6250000000000),(298052597/50000000000000),(-1923287/100000000000000)⟩
def e257 : ℝ := (2025557/100000000000000)
theorem h257 : Model (fun x => f257 ((19/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(423590606139443/100000000000000),(22998745979/2000000000000),(87996481/4000000000000),(-1419569/20000000000000)⟩
def e258 : ℝ := (934409/12500000000000)
theorem h258 : Model (fun x => f258 ((19/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(86853277870429/3125000000000),(22998745979/2000000000000),(87996481/4000000000000),(-1419569/20000000000000)⟩
def e259 : ℝ := (7475273/100000000000000)
theorem h259 : Model (fun x => f259 ((19/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1595034601259321/50000000000000),(4990045738931/50000000000000),(453515681/2000000000000),(-47891201/100000000000000)⟩
def e260 : ℝ := (64954359/100000000000000)
theorem h260 : Model (fun x => f260 ((19/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4236225077449797/50000000000000),(4990045738931/50000000000000),(453515681/2000000000000),(-47891201/100000000000000)⟩
def e261 : ℝ := (1623859/2500000000000)
theorem h261 : Model (fun x => f261 ((19/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2431156652535581/25000000000000),(37854896560787/100000000000000),(107629399239/100000000000000),(-87770101/100000000000000)⟩
def e262 : ℝ := (246780649/100000000000000)
theorem h262 : Model (fun x => f262 ((19/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14993674229189943/100000000000000),(37854896560787/100000000000000),(107629399239/100000000000000),(-87770101/100000000000000)⟩
def e263 : ℝ := (4935613/2000000000000)
theorem h263 : Model (fun x => f263 ((19/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(4302411956612853/25000000000000),(90169295523063/100000000000000),(330868749467/100000000000000),(4297761/2500000000000)⟩
def e264 : ℝ := (117772139/20000000000000)
theorem h264 : Model (fun x => f264 ((19/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(19545362112165697/100000000000000),(90169295523063/100000000000000),(330868749467/100000000000000),(4297761/2500000000000)⟩
def e265 : ℝ := (73607587/12500000000000)
theorem h265 : Model (fun x => f265 ((19/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(4486809483108411/20000000000000),(41099579247133/25000000000000),(97155486389/12500000000000),(1389881701/100000000000000)⟩
def e266 : ℝ := (1076243823/100000000000000)
theorem h266 : Model (fun x => f266 ((19/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(22836428367923007/100000000000000),(41099579247133/25000000000000),(97155486389/12500000000000),(1389881701/100000000000000)⟩
def e267 : ℝ := (67265239/6250000000000)
theorem h267 : Model (fun x => f267 ((19/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(26211513190064311/100000000000000),(129926381511471/50000000000000),(77025168513/5000000000000),(4557934787/100000000000000)⟩
def e268 : ℝ := (1710385561/100000000000000)
theorem h268 : Model (fun x => f268 ((19/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(26193894142445263/100000000000000),(129926381511471/50000000000000),(77025168513/5000000000000),(4557934787/100000000000000)⟩
def e269 : ℝ := (855192781/50000000000000)
theorem h269 : Model (fun x => f269 ((19/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(6013038385444313/20000000000000),(7597530402003/2000000000000),(2734014125671/100000000000000),(11076927349/100000000000000)⟩
def e270 : ℝ := (2522767081/100000000000000)
theorem h270 : Model (fun x => f270 ((19/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(15034262630277449/50000000000000),(7597530402003/2000000000000),(2734014125671/100000000000000),(11076927349/100000000000000)⟩
def e271 : ℝ := (1261383541/50000000000000)
theorem h271 : Model (fun x => f271 ((19/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(2221972315373529/50000000000000),(149835728507223/100000000000000),(110436897787/6250000000000),(11842338211/100000000000000)⟩
def e272 : ℝ := (1041051303/100000000000000)
theorem h272 : Model (fun x => f272 ((19/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(131743083804079/100000000000000),(357647888667/50000000000000),(2339331943/100000000000000),(-175049/25000000000000)⟩
def e273 : ℝ := (4670949/100000000000000)
theorem h273 : Model (fun x => f273 ((19/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(1677963984771/781250000000),(19474744579/6250000000000),(298052597/50000000000000),(-1923287/100000000000000)⟩
def e274 : ℝ := (2025557/100000000000000)
theorem h274 : Model (fun x => f274 ((19/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(92260372781091/20000000000000),(669243801931/50000000000000),(3531542331/100000000000000),(-454677/10000000000000)⟩
def e275 : ℝ := (8722063/100000000000000)
theorem h275 : Model (fun x => f275 ((19/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(990781329588591/100000000000000),(2156096633609/50000000000000),(14505542121/100000000000000),(86313/25000000000000)⟩
def e276 : ℝ := (879703/3125000000000)
theorem h276 : Model (fun x => f276 ((19/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(265999262053309/12500000000000),(6174468264759/50000000000000),(1009952637/2000000000000),(26294923/50000000000000)⟩
def e277 : ℝ := (20177679/25000000000000)
theorem h277 : Model (fun x => f277 ((19/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(140174252290049/5000000000000),(629806434293/2000000000000),(204639404631/100000000000000),(3522367/500000000000)⟩
def e278 : ℝ := (41671717/20000000000000)
theorem h278 : Model (fun x => f278 ((19/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(896713984771/97656250000),(19474744579/781250000000),(298052597/6250000000000),(-1923287/12500000000000)⟩
def e279 : ℝ := (2025557/12500000000000)
theorem h279 : Model (fun x => f279 ((19/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1049978204209583/100000000000000),(1604031541723/50000000000000),(1421634699/20000000000000),(-4021623/25000000000000)⟩
def e280 : ℝ := (4175081/20000000000000)
theorem h280 : Model (fun x => f280 ((19/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1149978204209583/100000000000000),(1604031541723/50000000000000),(1421634699/20000000000000),(-4021623/25000000000000)⟩
def e281 : ℝ := (4175081/20000000000000)
theorem h281 : Model (fun x => f281 ((19/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(6447893396997263/20000000000000),(226034702479111/50000000000000),(890703629307/25000000000000),(4113414013/25000000000000)⟩
def e282 : ℝ := (94585331/3125000000000)
theorem h282 : Model (fun x => f282 ((19/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(310178825371/100000000000000),(-21747003/500000000000),(26710159/100000000000000),(-26091/50000000000000)⟩
def e283 : ℝ := (14983/50000000000000)
theorem h283 : Model (fun x => f283 ((19/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (31783815285124221/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(3446043813947/25000000000000),(67868437059/25000000000000),(150858559/100000000000000),(-1209321/50000000000000)⟩
def e284 : ℝ := (2387663/50000000000000)
theorem h284 : Model (fun x => f284 ((19/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(506088984771/195312500000),(623191826529/50000000000000),(298052597/12500000000000),(-3846573/50000000000000)⟩
def e285 : ℝ := (4051111/50000000000000)
theorem h285 : Model (fun x => f285 ((19/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(43561827587617/100000000000000),(-118258926491/100000000000000),(11850523/12500000000000),(217349/20000000000000)⟩
def e286 : ℝ := (77839/10000000000000)
theorem h286 : Model (fun x => f286 ((19/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (9157375526671/4000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(56438172412381/50000000000000),(236517852979/100000000000000),(-189608373/100000000000000),(-434699/20000000000000)⟩
def e287 : ℝ := (43677/781250000000)
theorem h287 : Model (fun x => f287 ((19/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(6438172412381/50000000000000),(236517852979/100000000000000),(-189608373/100000000000000),(-434699/20000000000000)⟩
def e288 : ℝ := (43677/781250000000)
theorem h288 : Model (fun x => f288 ((19/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(104141865760941/25000000000000),(872863505041/100000000000000),(-699745187/100000000000000),(-501327/6250000000000)⟩
def e289 : ℝ := (10316093/50000000000000)
theorem h289 : Model (fun x => f289 ((19/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2772281748758049/100000000000000),(872863505041/100000000000000),(-699745187/100000000000000),(-501327/6250000000000)⟩
def e290 : ℝ := (20632187/100000000000000)
theorem h290 : Model (fun x => f290 ((19/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3129250306242077/100000000000000),(754219769049/10000000000000),(-248865443/6250000000000),(-18154881/25000000000000)⟩
def e291 : ℝ := (178411923/100000000000000)
theorem h291 : Model (fun x => f291 ((19/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8411631258623029/100000000000000),(754219769049/10000000000000),(-248865443/6250000000000),(-18154881/25000000000000)⟩
def e292 : ℝ := (44602981/25000000000000)
theorem h292 : Model (fun x => f292 ((19/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4747370952435399/50000000000000),(110970182523/390625000000),(-2605076577/100000000000000),(-288515067/100000000000000)⟩
def e293 : ℝ := (168205701/25000000000000)
theorem h293 : Model (fun x => f293 ((19/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14763789523918417/100000000000000),(110970182523/390625000000),(-2605076577/100000000000000),(-288515067/100000000000000)⟩
def e294 : ℝ := (134564561/20000000000000)
theorem h294 : Model (fun x => f294 ((19/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(208310324652753/1250000000000),(33492661992453/50000000000000),(36256962717/100000000000000),(-706581603/100000000000000)⟩
def e295 : ℝ := (1589327041/100000000000000)
theorem h295 : Model (fun x => f295 ((19/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(760021610317381/4000000000000),(33492661992453/50000000000000),(36256962717/100000000000000),(-706581603/100000000000000)⟩
def e296 : ℝ := (794663521/50000000000000)
theorem h296 : Model (fun x => f296 ((19/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(21447115340113897/100000000000000),(120550255155663/100000000000000),(32666233823/20000000000000),(-1251794873/100000000000000)⟩
def e297 : ℝ := (2866934711/100000000000000)
theorem h297 : Model (fun x => f297 ((19/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(21849496292494849/100000000000000),(120550255155663/100000000000000),(32666233823/20000000000000),(-1251794873/100000000000000)⟩
def e298 : ℝ := (358366839/12500000000000)
theorem h298 : Model (fun x => f298 ((19/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(12331456388795037/50000000000000),(187750681214371/100000000000000),(214028327241/50000000000000),(-173014401/10000000000000)⟩
def e299 : ℝ := (4477048277/100000000000000)
theorem h299 : Model (fun x => f299 ((19/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(12322646864985513/50000000000000),(187750681214371/100000000000000),(214028327241/50000000000000),(-173014401/10000000000000)⟩
def e300 : ℝ := (2238524139/50000000000000)
theorem h300 : Model (fun x => f300 ((19/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(27818706733717543/100000000000000),(67554156482217/25000000000000),(880509045057/100000000000000),(-1832148149/100000000000000)⟩
def e301 : ℝ := (6461470969/100000000000000)
theorem h301 : Model (fun x => f301 ((19/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(6955510016762719/25000000000000),(67554156482217/25000000000000),(880509045057/100000000000000),(-1832148149/100000000000000)⟩
def e302 : ℝ := (646147097/10000000000000)
theorem h302 : Model (fun x => f302 ((19/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(716492363263383/20000000000000),(3143691135937/3125000000000),(699735025387/100000000000000),(729583377/100000000000000)⟩
def e303 : ℝ := (2429779059/100000000000000)
theorem h303 : Model (fun x => f303 ((19/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(25482138441997/20000000000000),(533945414601/100000000000000),(26272189/20000000000000),(-5803639/100000000000000)⟩
def e304 : ℝ := (12657457/100000000000000)
theorem h304 : Model (fun x => f304 ((19/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(106438172412381/50000000000000),(236517852979/100000000000000),(-189608373/100000000000000),(-434699/20000000000000)⟩
def e305 : ℝ := (43677/781250000000)
theorem h305 : Model (fun x => f305 ((19/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(453163381859509/100000000000000),(1006981120559/100000000000000),(-247855801/100000000000000),(-10150629/100000000000000)⟩
def e306 : ℝ := (23838769/100000000000000)
theorem h306 : Model (fun x => f306 ((19/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(964677643386801/100000000000000),(1607718451891/50000000000000),(994828041/100000000000000),(-8488329/25000000000000)⟩
def e307 : ℝ := (76240099/100000000000000)
theorem h307 : Model (fun x => f307 ((19/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1026785253291737/50000000000000),(1140817425153/12500000000000),(1578745263/20000000000000),(-96989591/100000000000000)⟩
def e308 : ℝ := (54185341/25000000000000)
theorem h308 : Model (fun x => f308 ((19/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2616468397458099/100000000000000),(22593132581417/100000000000000),(61485779607/100000000000000),(-18862003/10000000000000)⟩
def e309 : ℝ := (67429131/12500000000000)
theorem h309 : Model (fun x => f309 ((19/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(56438172412381/6250000000000),(236517852979/12500000000000),(-189608373/12500000000000),(-434699/2500000000000)⟩
def e310 : ℝ := (43677/97656250000)
theorem h310 : Model (fun x => f310 ((19/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1030421450808081/100000000000000),(2426088238433/100000000000000),(-1385506039/100000000000000),(-23191599/100000000000000)⟩
def e311 : ℝ := (11476541/20000000000000)
theorem h311 : Model (fun x => f311 ((19/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1130421450808081/100000000000000),(2426088238433/100000000000000),(-1385506039/100000000000000),(-23191599/100000000000000)⟩
def e312 : ℝ := (11476541/20000000000000)
theorem h312 : Model (fun x => f312 ((19/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(29577120018480789/100000000000000),(159437724581447/50000000000000),(120692644647/10000000000000),(-195041511/12500000000000)⟩
def e313 : ℝ := (381802079/5000000000000)
theorem h313 : Model (fun x => f313 ((19/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(169049589577/50000000000000),(-3645098899/100000000000000),(3187733/12500000000000),(-108361/100000000000000)⟩
def e314 : ℝ := (44637/50000000000000)
theorem h314 : Model (fun x => f314 ((19/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (29257028446497757/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1514034249309/12500000000000),(1047685647/500000000000),(-77501583/20000000000000),(-253383/20000000000000)⟩
def e315 : ℝ := (11636313/100000000000000)
theorem h315 : Model (fun x => f315 ((19/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1294822462513/5000000000000),(120252719409/25000000000000),(-59162339/25000000000000),(-3685557/100000000000000)⟩
def e316 : ℝ := (16411639/100000000000000)
theorem h316 : Model (fun x => f316 ((19/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(4471044713857/4000000000000),(1675882523007/100000000000000),(-2029137299/20000000000000),(-57135913/100000000000000)⟩
def e317 : ℝ := (71880531/100000000000000)
theorem h317 : Model (fun x => f317 ((19/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(23531814283457/50000000000000),(42045626007/20000000000000),(-1621198921/25000000000000),(2210189/5000000000000)⟩
def e318 : ℝ := (6445141/20000000000000)
theorem h318 : Model (fun x => f318 ((19/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-2216969973977/2000000000000),(-245804934067/50000000000000),(7927037813/100000000000000),(-136082497/100000000000000)⟩
def e319 : ℝ := (27683847/50000000000000)
theorem h319 : Model (fun x => f319 ((19/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((19/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-3971/64),(-209/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((19/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((19/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(1843/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((19/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(10773/64),(179/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((19/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((19/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(17685/64),(179/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((19/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2210625/32),(4475/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((19/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((19/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1069397268789153691/100000000000000),(571870197213451/25000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (69181/50000000000000)
theorem h329 : Model (fun x => f329 ((19/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9351061847/100000000000000),(-625071/3125000000000),(442831/100000000000000),(-1803/100000000000000)⟩
def e330 : ℝ := (1/4000000000000)
theorem h330 : Model (fun x => f330 ((19/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (16672875599756007/1562500000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(20187198335473/3125000000000),(1233577530957/100000000000000),(446257099/5000000000000),(33678297/100000000000000)⟩
def e331 : ℝ := (3002581/100000000000000)
theorem h331 : Model (fun x => f331 ((19/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((19/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(91/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((19/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((19/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((19/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(725806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((19/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((19/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((19/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1610017605051701/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (67/6250000000000)
theorem h339 : Model (fun x => f339 ((19/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3824193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((19/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((19/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((19/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2154964789896339/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (67/6250000000000)
theorem h343 : Model (fun x => f343 ((19/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(1160111762253/25000000000000),(-758402923/12500000000000),(7932683/100000000000000),(-2593/25000000000000)⟩
def e344 : ℝ := (19/100000000000000)
theorem h344 : Model (fun x => f344 ((19/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1076073624130393/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(14942402888439/10000000000000),(41699925269/5000000000000),(-272606029/25000000000000),(712841/50000000000000)⟩
def e345 : ℝ := (2969/100000000000000)
theorem h345 : Model (fun x => f345 ((19/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(24942402888439/10000000000000),(41699925269/5000000000000),(-272606029/25000000000000),(712841/50000000000000)⟩
def e346 : ℝ := (2969/100000000000000)
theorem h346 : Model (fun x => f346 ((19/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(24942402888439/20000000000000),(41699925269/10000000000000),(-272606029/50000000000000),(712841/100000000000000)⟩
def e347 : ℝ := (297/20000000000000)
theorem h347 : Model (fun x => f347 ((19/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(4942402888439/20000000000000),(41699925269/10000000000000),(-272606029/50000000000000),(712841/100000000000000)⟩
def e348 : ℝ := (297/20000000000000)
theorem h348 : Model (fun x => f348 ((19/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(460246719965243/100000000000000),(769462906749/50000000000000),(-2012092119/100000000000000),(1315361/50000000000000)⟩
def e349 : ℝ := (5483/100000000000000)
theorem h349 : Model (fun x => f349 ((19/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(351995125709941/12500000000000),(769462906749/50000000000000),(-2012092119/100000000000000),(1315361/50000000000000)⟩
def e350 : ℝ := (1371/25000000000000)
theorem h350 : Model (fun x => f350 ((19/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(109745053002801/3125000000000),(13661761732509/100000000000000),(-1430621303/12500000000000),(1643333/25000000000000)⟩
def e351 : ℝ := (20411/25000000000000)
theorem h351 : Model (fun x => f351 ((19/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(1099277831058823/12500000000000),(13661761732509/100000000000000),(-1430621303/12500000000000),(1643333/25000000000000)⟩
def e352 : ℝ := (16329/20000000000000)
theorem h352 : Model (fun x => f352 ((19/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5483726109719709/50000000000000),(53709700988921/100000000000000),(-5250971127/100000000000000),(-10264891/20000000000000)⟩
def e353 : ℝ := (420277/100000000000000)
theorem h353 : Model (fun x => f353 ((19/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(16236499838487037/100000000000000),(53709700988921/100000000000000),(-5250971127/100000000000000),(-10264891/20000000000000)⟩
def e354 : ℝ := (210139/50000000000000)
theorem h354 : Model (fun x => f354 ((19/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(20248866023480921/100000000000000),(67344266521833/50000000000000),(64448552479/50000000000000),(-262995611/100000000000000)⟩
def e355 : ℝ := (965519/100000000000000)
theorem h355 : Model (fun x => f355 ((19/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(11292290154597603/50000000000000),(67344266521833/50000000000000),(64448552479/50000000000000),(-262995611/100000000000000)⟩
def e356 : ℝ := (12069/1250000000000)
theorem h356 : Model (fun x => f356 ((19/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(28165685056912653/100000000000000),(131075156946957/50000000000000),(599266497307/100000000000000),(-72766627/20000000000000)⟩
def e357 : ℝ := (596807/25000000000000)
theorem h357 : Model (fun x => f357 ((19/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(5713613201858721/20000000000000),(131075156946957/50000000000000),(599266497307/100000000000000),(-72766627/20000000000000)⟩
def e358 : ℝ := (2387229/100000000000000)
theorem h358 : Model (fun x => f358 ((19/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(35627810607366041/100000000000000),(446061559090377/100000000000000),(168476562991/10000000000000),(819562949/100000000000000)⟩
def e359 : ℝ := (1584317/25000000000000)
theorem h359 : Model (fun x => f359 ((19/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(35610191559746993/100000000000000),(446061559090377/100000000000000),(168476562991/10000000000000),(819562949/100000000000000)⟩
def e360 : ℝ := (6337269/100000000000000)
theorem h360 : Model (fun x => f360 ((19/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(22205093620442487/50000000000000),(704786588679493/100000000000000),(1883513732687/50000000000000),(1467354047/25000000000000)⟩
def e361 : ℝ := (691317/6250000000000)
theorem h361 : Model (fun x => f361 ((19/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(44413520574218307/100000000000000),(704786588679493/100000000000000),(1883513732687/50000000000000),(1467354047/25000000000000)⟩
def e362 : ℝ := (11061073/100000000000000)
theorem h362 : Model (fun x => f362 ((19/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(439019024743523/4000000000000),(359371012468939/100000000000000),(226732206849/6250000000000),(6816471837/50000000000000)⟩
def e363 : ℝ := (3103999/25000000000000)
theorem h363 : Model (fun x => f363 ((19/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(77765432731151/50000000000000),(1040096336477/100000000000000),(189496943/50000000000000),(-346133/12500000000000)⟩
def e364 : ℝ := (3161/25000000000000)
theorem h364 : Model (fun x => f364 ((19/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(44942402888439/20000000000000),(41699925269/10000000000000),(-272606029/50000000000000),(712841/100000000000000)⟩
def e365 : ℝ := (297/20000000000000)
theorem h365 : Model (fun x => f365 ((19/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(126238723586673/25000000000000),(1874094841857/100000000000000),(-71143023/10000000000000),(-671691/50000000000000)⟩
def e366 : ℝ := (7807/50000000000000)
theorem h366 : Model (fun x => f366 ((19/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1134694315110909/100000000000000),(6316974407541/100000000000000),(108225541/3125000000000),(-6301833/50000000000000)⟩
def e367 : ℝ := (54319/100000000000000)
theorem h367 : Model (fun x => f367 ((19/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2549794453246791/100000000000000),(18926667257311/100000000000000),(2793751123/10000000000000),(-20116351/50000000000000)⟩
def e368 : ℝ := (82869/50000000000000)
theorem h368 : Model (fun x => f368 ((19/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(793143476128901/20000000000000),(55957128084379/100000000000000),(1952895241/781250000000),(28641029/12500000000000)⟩
def e369 : ℝ := (142189/10000000000000)
theorem h369 : Model (fun x => f369 ((19/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(24942402888439/2500000000000),(41699925269/1250000000000),(-272606029/6250000000000),(712841/12500000000000)⟩
def e370 : ℝ := (297/2500000000000)
theorem h370 : Model (fun x => f370 ((19/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(576613490499931/50000000000000),(4376090357997/100000000000000),(-1991351289/50000000000000),(91677/3125000000000)⟩
def e371 : ℝ := (6131/25000000000000)
theorem h371 : Model (fun x => f371 ((19/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(626613490499931/50000000000000),(4376090357997/100000000000000),(-1991351289/50000000000000),(91677/3125000000000)⟩
def e372 : ℝ := (6131/25000000000000)
theorem h372 : Model (fun x => f372 ((19/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(9939888040887587/20000000000000),(218703300716471/25000000000000),(5423490647429/100000000000000),(2924542647/25000000000000)⟩
def e373 : ℝ := (4116559/20000000000000)
theorem h373 : Model (fun x => f373 ((19/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(100604754891/50000000000000),(-708340919/20000000000000),(20192099/50000000000000),(-74343/20000000000000)⟩
def e374 : ℝ := (393/12500000000000)
theorem h374 : Model (fun x => f374 ((19/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (48819191792171239/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(22083700688403/100000000000000),(16718486409/5000000000000),(-498096833/50000000000000),(3279431/100000000000000)⟩
def e375 : ℝ := (743593/100000000000000)
theorem h375 : Model (fun x => f375 ((19/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(14942402888439/5000000000000),(41699925269/2500000000000),(-272606029/12500000000000),(712841/25000000000000)⟩
def e376 : ℝ := (2969/50000000000000)
theorem h376 : Model (fun x => f376 ((19/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(40092368184121/100000000000000),(-134056751839/100000000000000),(31175989/5000000000000),(-2900091/100000000000000)⟩
def e377 : ℝ := (13733/100000000000000)
theorem h377 : Model (fun x => f377 ((19/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (248588938526243/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(119815263631753/100000000000000),(10724540147/4000000000000),(-311759891/25000000000000),(5800179/100000000000000)⟩
def e378 : ℝ := (3423/3125000000000)
theorem h378 : Model (fun x => f378 ((19/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(19815263631753/100000000000000),(10724540147/4000000000000),(-311759891/25000000000000),(5800179/100000000000000)⟩
def e379 : ℝ := (3423/3125000000000)
theorem h379 : Model (fun x => f379 ((19/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(110543844422153/25000000000000),(989466501657/100000000000000),(-230108491/5000000000000),(10702711/50000000000000)⟩
def e380 : ℝ := (202121/50000000000000)
theorem h380 : Model (fun x => f380 ((19/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2797889663402897/100000000000000),(989466501657/100000000000000),(-230108491/5000000000000),(10702711/50000000000000)⟩
def e381 : ℝ := (404243/100000000000000)
theorem h381 : Model (fun x => f381 ((19/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3352298876331747/100000000000000),(4343525951509/50000000000000),(-18875999829/50000000000000),(81625747/50000000000000)⟩
def e382 : ℝ := (3723929/100000000000000)
theorem h382 : Model (fun x => f382 ((19/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8634679828712699/100000000000000),(4343525951509/50000000000000),(-18875999829/50000000000000),(81625747/50000000000000)⟩
def e383 : ℝ := (372393/10000000000000)
theorem h383 : Model (fun x => f383 ((19/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(5172832200264959/50000000000000),(8389789189827/25000000000000),(-129619372383/100000000000000),(48687791/10000000000000)⟩
def e384 : ℝ := (3839023/25000000000000)
theorem h384 : Model (fun x => f384 ((19/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(15614712019577537/100000000000000),(8389789189827/25000000000000),(-129619372383/100000000000000),(48687791/10000000000000)⟩
def e385 : ℝ := (15356093/100000000000000)
theorem h385 : Model (fun x => f385 ((19/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(18708808371595849/100000000000000),(5129633976763/6250000000000),(-260048798437/100000000000000),(90376537/12500000000000)⟩
def e386 : ℝ := (20231421/50000000000000)
theorem h386 : Model (fun x => f386 ((19/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(10522261328655067/50000000000000),(5129633976763/6250000000000),(-260048798437/100000000000000),(90376537/12500000000000)⟩
def e387 : ℝ := (40462843/100000000000000)
theorem h387 : Model (fun x => f387 ((19/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(25214550301900129/100000000000000),(77380279294917/50000000000000),(-176979907459/50000000000000),(91544021/25000000000000)⟩
def e388 : ℝ := (40848583/50000000000000)
theorem h388 : Model (fun x => f388 ((19/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(25616931254281081/100000000000000),(77380279294917/50000000000000),(-176979907459/50000000000000),(91544021/25000000000000)⟩
def e389 : ℝ := (81697167/100000000000000)
theorem h389 : Model (fun x => f389 ((19/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(30692993716681807/100000000000000),(63527305798063/25000000000000),(-82154299319/25000000000000),(-3817507/400000000000)⟩
def e390 : ℝ := (70366353/50000000000000)
theorem h390 : Model (fun x => f390 ((19/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(30675374669062759/100000000000000),(63527305798063/25000000000000),(-82154299319/25000000000000),(-3817507/400000000000)⟩
def e391 : ℝ := (140732707/100000000000000)
theorem h391 : Model (fun x => f391 ((19/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(9188445257441381/25000000000000),(386706457471053/100000000000000),(-47483239161/50000000000000),(-341417201/10000000000000)⟩
def e392 : ℝ := (219162811/100000000000000)
theorem h392 : Model (fun x => f392 ((19/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(36757114363098857/100000000000000),(386706457471053/100000000000000),(-47483239161/50000000000000),(-341417201/10000000000000)⟩
def e393 : ℝ := (54790703/25000000000000)
theorem h393 : Model (fun x => f393 ((19/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(3641759557236493/50000000000000),(2737151424963/1562500000000),(559618615329/100000000000000),(-362154923/10000000000000)⟩
def e394 : ℝ := (99201351/100000000000000)
theorem h394 : Model (fun x => f394 ((19/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(17944621748933/12500000000000),(642481802521/100000000000000),(-1134719487/50000000000000),(1803009/25000000000000)⟩
def e395 : ℝ := (19367/6250000000000)
theorem h395 : Model (fun x => f395 ((19/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(219815263631753/100000000000000),(10724540147/4000000000000),(-311759891/25000000000000),(5800179/100000000000000)⟩
def e396 : ℝ := (3423/3125000000000)
theorem h396 : Model (fun x => f396 ((19/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(48318750125497/10000000000000),(1178708809871/100000000000000),(-2381759051/50000000000000),(9406197/50000000000000)⟩
def e397 : ℝ := (33059/6250000000000)
theorem h397 : Model (fun x => f397 ((19/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(265529969929823/25000000000000),(3886472816803/100000000000000),(-2667240339/20000000000000),(10476913/25000000000000)⟩
def e398 : ℝ := (3659/195312500000)
theorem h398 : Model (fun x => f398 ((19/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2334701613690219/100000000000000),(355960852843/3125000000000),(-16069951797/50000000000000),(34751129/50000000000000)⟩
def e399 : ℝ := (115923/2000000000000)
theorem h399 : Model (fun x => f399 ((19/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1675813494171779/50000000000000),(31352245137063/100000000000000),(-6485055719/25000000000000),(-24605529/12500000000000)⟩
def e400 : ℝ := (8814737/50000000000000)
theorem h400 : Model (fun x => f400 ((19/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(119815263631753/12500000000000),(10724540147/500000000000),(-311759891/3125000000000),(5800179/12500000000000)⟩
def e401 : ℝ := (3423/390625000000)
theorem h401 : Model (fun x => f401 ((19/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(68879942690343/6250000000000),(2787389831921/100000000000000),(-6122877743/50000000000000),(13403367/25000000000000)⟩
def e402 : ℝ := (14827/1250000000000)
theorem h402 : Model (fun x => f402 ((19/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(75129942690343/6250000000000),(2787389831921/100000000000000),(-6122877743/50000000000000),(13403367/25000000000000)⟩
def e403 : ℝ := (14827/1250000000000)
theorem h403 : Model (fun x => f403 ((19/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(20144603484292673/50000000000000),(117575422683697/25000000000000),(75827626973/50000000000000),(-513167429/10000000000000)⟩
def e404 : ℝ := (267050739/100000000000000)
theorem h404 : Model (fun x => f404 ((19/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(248205431489/100000000000000),(-2897337597/100000000000000),(131547/400000000000),(-85343/25000000000000)⟩
def e405 : ℝ := (2613/50000000000000)
theorem h405 : Model (fun x => f405 ((19/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (39818748223871583/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(18078090045661/100000000000000),(223772406621/100000000000000),(-322793147/25000000000000),(942929/12500000000000)⟩
def e406 : ℝ := (475553/50000000000000)
theorem h406 : Model (fun x => f406 ((19/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2510111920879/6250000000000),(558142134801/100000000000000),(-1143683127/50000000000000),(10822863/100000000000000)⟩
def e407 : ℝ := (1694699/100000000000000)
theorem h407 : Model (fun x => f407 ((19/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(259441291218019/100000000000000),(4100971138401/100000000000000),(-861310477/20000000000000),(105038999/100000000000000)⟩
def e408 : ℝ := (12308899/100000000000000)
theorem h408 : Model (fun x => f408 ((19/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(21847687681517/20000000000000),(23073855633/4000000000000),(-788535249/10000000000000),(1987979/1562500000000)⟩
def e409 : ℝ := (4651107/50000000000000)
theorem h409 : Model (fun x => f409 ((19/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-322012058253/20000000000000),(85236522691/100000000000000),(41685323/100000000000000),(-8851841/100000000000000)⟩
def e410 : ℝ := (16167477/25000000000000)
theorem h410 : Model (fun x => f410 ((19/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(10738119506835937/100000000000000),(132918243408203/25000000000000),(42959/409600),(2109/2048000)⟩
def e411 : ℝ := (503906251/100000000000000)
theorem h411 : Model (fun x => f411 ((19/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1849/64),(43/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((19/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(79507/512),(5547/2560),(129/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((19/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(1667491538339853209/100000000000000),(105829282999038617/100000000000000),(2888904414176939/100000000000000),(44242731857299/100000000000000)⟩
def e414 : ℝ := (26105692121/6250000000000)
theorem h414 : Model (fun x => f414 ((19/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(599703193/10000000000000),(-190304291/50000000000000),(2753199/20000000000000),(-373393/100000000000000)⟩
def e415 : ℝ := (12669/100000000000000)
theorem h415 : Model (fun x => f415 ((19/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (779364345251853209/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(566550009453/10000000000000),(-2050252577/20000000000000),(-93934857/25000000000000),(4215679/50000000000000)⟩
def e416 : ℝ := (287209/1250000000000)
theorem h416 : Model (fun x => f416 ((19/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(811087960653/20000000000000),(37492629903/50000000000000),(-66810821/20000000000000),(-420483/100000000000000)⟩
def e417 : ℝ := (21911657/25000000000000)
theorem h417 : Model (fun x => f417 ((19/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((19/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((6082861207903/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (47/20) (12/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (47/20) (12/5) ≤ (6083124147787/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(19/8)-(1/40)) (by norm_num : ((19/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel27

