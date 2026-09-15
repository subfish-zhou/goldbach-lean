import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel31
open Hf4Quad.Dag

def p0 : Cubic := ⟨(103/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((103/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((103/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((103/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((103/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(90247619047619/20000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((103/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-90247619047619/20000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((103/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-89952380952381/25000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((103/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((103/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(10609/1600),(103/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((103/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(401345767195767/50000000000000),(15586243386243/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((103/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-401345767195767/50000000000000),(-15586243386243/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((103/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-581250529100529/50000000000000),(-3993439153439/20000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((103/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((103/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1092727/64000),(31827/64000),(309/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((103/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(16634365587384259/100000000000000),(121124021267361/25000000000000),(4703845486111/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((103/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-16634365587384259/100000000000000),(-121124021267361/25000000000000),(-4703845486111/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((103/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-17796866645585317/100000000000000),(-504463280836639/100000000000000),(-1194876715443/25000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((103/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((103/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(112550881/2560000),(1092727/640000),(31827/1280000),(103/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((103/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(12282338204365079/100000000000000),(476984007936507/100000000000000),(6946369047619/100000000000000),(2248015873/5000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((103/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2757264220610119/50000000000000),(-6869818225033/25000000000000),(2166862185847/100000000000000),(5947503307/20000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((103/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((103/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(11321035881835937/100000000000000),(137391212158203/25000000000000),(1092727/10240000),(10609/10240000)⟩
def e22 : ℝ := (503906251/100000000000000)
theorem h22 : Model (fun x => f22 ((103/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(73754452282034863/100000000000000),(447539152196813/12500000000000),(34760322500723/50000000000000),(33747885923/5000000000000)⟩
def e23 : ℝ := (3282855913/100000000000000)
theorem h23 : Model (fun x => f23 ((103/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(545919390726517/800000000000),(888208486168593/25000000000000),(71687507187293/100000000000000),(140939046999/20000000000000)⟩
def e24 : ℝ := (678396581/20000000000000)
theorem h24 : Model (fun x => f24 ((103/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((103/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(29151667395727537/100000000000000),(1698155382275389/100000000000000),(2060868182373/5000000000000),(133389526367/25000000000000)⟩
def e26 : ℝ := (1950122073/50000000000000)
theorem h26 : Model (fun x => f26 ((103/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(327300731289597/500000000000),(1906606201686971/50000000000000),(11569212388877/12500000000000),(1198106137357/100000000000000)⟩
def e27 : ℝ := (175160171/2000000000000)
theorem h27 : Model (fun x => f27 ((103/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(5348002803949361/4000000000000),(3683023174024157/50000000000000),(164241206298309/100000000000000),(29731271443/1562500000000)⟩
def e28 : ℝ := (2429998291/20000000000000)
theorem h28 : Model (fun x => f28 ((103/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((103/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(75065543543998407/100000000000000),(1020308358850463/20000000000000),(74294297974547/50000000000000),(1202173106383/50000000000000)⟩
def e30 : ℝ := (11739793709/50000000000000)
theorem h30 : Model (fun x => f30 ((103/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(17813172634647241/100000000000000),(605301982730731/50000000000000),(17630154836817/50000000000000),(570555172711/100000000000000)⟩
def e31 : ℝ := (1114348673/20000000000000)
theorem h31 : Model (fun x => f31 ((103/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(75756621366690633/50000000000000),(536040644594361/6250000000000),(199501515971943/100000000000000),(2473356545063/100000000000000)⟩
def e32 : ℝ := (886086741/5000000000000)
theorem h32 : Model (fun x => f32 ((103/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((103/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(4551261/320),(44187/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((103/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((103/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(227527/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((103/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(8191693/320),(61859/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((103/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((103/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(8921293/320),(61859/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((103/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-8921293/320),(-61859/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((103/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((103/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(143/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((103/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(20449/1600),(143/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((103/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((103/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(429429/160),(3003/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((103/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(37258778517/100000000000000),(-260550899/50000000000000),(2733051/50000000000000),(-25483/50000000000000)⟩
def e46 : ℝ := (457/100000000000000)
theorem h46 : Model (fun x => f46 ((103/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (211701/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1038738999913321/100000000000000),(122875819433/100000000000000),(-872003903/100000000000000),(6187759/100000000000000)⟩
def e47 : ℝ := (12681383/50000000000000)
theorem h47 : Model (fun x => f47 ((103/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((103/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(183/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((103/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((103/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((103/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(76249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((103/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(126249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((103/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((103/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(126249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((103/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((103/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2651249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((103/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((103/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(26249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((103/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(695953124999967/100000000000000),(6671874999989/50000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (131/100000000000000)
theorem h60 : Model (fun x => f60 ((103/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(159390624999997/100000000000000),(1052083333331/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((103/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((103/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(126249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((103/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1421890624999987/100000000000000),(5218749999991/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((103/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1521890624999987/100000000000000),(5218749999991/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((103/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(5295822681884469/50000000000000),(119698666991987/50000000000000),(1263315429679/100000000000000),(2134331597/100000000000000)⟩
def e66 : ℝ := (9927/1562500000000)
theorem h66 : Model (fun x => f66 ((103/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(226249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((103/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(102378124999999/20000000000000),(1885416666663/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((103/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1158152539062483/100000000000000),(799829101561/12500000000000),(5891927083/50000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (17/25000000000000)
theorem h69 : Model (fun x => f69 ((103/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(122667409708983719/100000000000000),(345030679761177/10000000000000),(31197380133161/100000000000000),(134530141923/100000000000000)⟩
def e70 : ℝ := (62100403/20000000000000)
theorem h70 : Model (fun x => f70 ((103/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((103/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3347203124999937/12500000000000),(22093749999951/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((103/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(7029126562499599/100000000000000),(78985156249857/50000000000000),(32520833333/4000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1619/100000000000000)
theorem h73 : Model (fun x => f73 ((103/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(10176000969688067/12500000000000),(455861036767957/20000000000000),(162818109577/800000000000),(85220452171/100000000000000)⟩
def e74 : ℝ := (92609727/50000000000000)
theorem h74 : Model (fun x => f74 ((103/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(40815083493297651/20000000000000),(1145922396290311/20000000000000),(25774821915143/50000000000000),(109875297047/50000000000000)⟩
def e75 : ℝ := (495721469/100000000000000)
theorem h75 : Model (fun x => f75 ((103/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((103/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1115734374999979/12500000000000),(7364583333317/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((103/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(6890624999999/100000000000000),(218749999999/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((103/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1808789062499/100000000000000),(86132812499/100000000000000),(1367187499/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((103/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(161450250732329/100000000000000),(4376892700149/50000000000000),(10908660883/6250000000000),(383730281/25000000000000)⟩
def e80 : ℝ := (5598529/100000000000000)
theorem h80 : Model (fun x => f80 ((103/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(91320298070473/25000000000000),(1279884302889/6250000000000),(431367629799/100000000000000),(4200003101/100000000000000)⟩
def e81 : ℝ := (19085513/100000000000000)
theorem h81 : Model (fun x => f81 ((103/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(204440698658770147/100000000000000),(5750090130297779/100000000000000),(10396202292017/20000000000000),(44790119439/20000000000000)⟩
def e82 : ℝ := (257403491/50000000000000)
theorem h82 : Model (fun x => f82 ((103/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(94961425781/20000000000000),(15073242187/50000000000000),(717773437/100000000000000),(3797743/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((103/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(124636871337/100000000000000),(1978363037/20000000000000),(157012939/50000000000000),(4984537/100000000000000)⟩
def e84 : ℝ := (39689/100000000000000)
theorem h84 : Model (fun x => f84 ((103/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(1308687149/4000000000000),(3115921783/100000000000000),(123647689/100000000000000),(1308441/50000000000000)⟩
def e85 : ℝ := (6271/20000000000000)
theorem h85 : Model (fun x => f85 ((103/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1717651883/20000000000000),(477125523/50000000000000),(1817621/4000000000000),(120213/10000000000000)⟩
def e86 : ℝ := (19267/100000000000000)
theorem h86 : Model (fun x => f86 ((103/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(5152955649/20000000000000),(1431376569/50000000000000),(5452863/4000000000000),(360639/10000000000000)⟩
def e87 : ℝ := (57801/100000000000000)
theorem h87 : Model (fun x => f87 ((103/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-5152955649/20000000000000),(-1431376569/50000000000000),(-5452863/4000000000000),(-360639/10000000000000)⟩
def e88 : ℝ := (57801/100000000000000)
theorem h88 : Model (fun x => f88 ((103/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(102220336446995951/50000000000000),(5750087267544641/100000000000000),(5198087513851/10000000000000),(44789398161/20000000000000)⟩
def e89 : ℝ := (514864783/100000000000000)
theorem h89 : Model (fun x => f89 ((103/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3347203124999937/10000000000000),(22093749999951/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((103/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(327540014953607/12500000000000),(19302542317673/100000000000000),(26660970051/50000000000000),(13093171/20000000000000)⟩
def e91 : ℝ := (3793/12500000000000)
theorem h91 : Model (fun x => f91 ((103/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(219268592323047889/25000000000000),(12250222760908023/100000000000000),(70047741322597/100000000000000),(210094765051/100000000000000)⟩
def e92 : ℝ := (174785317/50000000000000)
theorem h92 : Model (fun x => f92 ((103/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(2280308341/20000000000000),(-159246959/100000000000000),(656819/50000000000000),(-8361/100000000000000)⟩
def e93 : ℝ := (29/50000000000000)
theorem h93 : Model (fun x => f93 ((103/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (864753888345625251/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(23309388581991/100000000000000),(16501652167/5000000000000),(-54460759/10000000000000),(1197493/100000000000000)⟩
def e94 : ℝ := (42181/12500000000000)
theorem h94 : Model (fun x => f94 ((103/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(76249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((103/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(39603960396039/100000000000000),(-130706139921/100000000000000),(431373399/100000000000000),(-56947/4000000000000)⟩
def e96 : ℝ := (4717/100000000000000)
theorem h96 : Model (fun x => f96 ((103/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (251666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(120792079207917/100000000000000),(261412279841/100000000000000),(-862746799/100000000000000),(2847347/100000000000000)⟩
def e97 : ℝ := (38201/100000000000000)
theorem h97 : Model (fun x => f97 ((103/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2536633663366257/100000000000000),(5489657876661/100000000000000),(-18117682779/100000000000000),(59794287/100000000000000)⟩
def e98 : ℝ := (802221/100000000000000)
theorem h98 : Model (fun x => f98 ((103/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(20792079207917/100000000000000),(261412279841/100000000000000),(-862746799/100000000000000),(2847347/100000000000000)⟩
def e99 : ℝ := (38201/100000000000000)
theorem h99 : Model (fun x => f99 ((103/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(263709440250899/50000000000000),(7772485904579/100000000000000),(-11301128877/100000000000000),(-5032229/50000000000000)⟩
def e100 : ℝ := (1609991/100000000000000)
theorem h100 : Model (fun x => f100 ((103/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(36476815998429/25000000000000),(631530656249/100000000000000),(-700447897/50000000000000),(2368087/100000000000000)⟩
def e101 : ℝ := (11487/10000000000000)
theorem h101 : Model (fun x => f101 ((103/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(120792079207917/10000000000000),(261412279841/10000000000000),(-862746799/10000000000000),(2847347/10000000000000)⟩
def e102 : ℝ := (38201/10000000000000)
theorem h102 : Model (fun x => f102 ((103/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(676914028036443/50000000000000),(3245653454659/100000000000000),(-1253545473/12500000000000),(30841557/100000000000000)⟩
def e103 : ℝ := (6211/1250000000000)
theorem h103 : Model (fun x => f103 ((103/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(726914028036443/50000000000000),(3245653454659/100000000000000),(-1253545473/12500000000000),(30841557/100000000000000)⟩
def e104 : ℝ := (6211/1250000000000)
theorem h104 : Model (fun x => f104 ((103/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(7667763657760667/100000000000000),(13011676985061/10000000000000),(7015498201/20000000000000),(-1129904361/100000000000000)⟩
def e105 : ℝ := (29324531/100000000000000)
theorem h105 : Model (fun x => f105 ((103/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(220792079207917/100000000000000),(261412279841/100000000000000),(-862746799/100000000000000),(2847347/100000000000000)⟩
def e106 : ℝ := (38201/100000000000000)
theorem h106 : Model (fun x => f106 ((103/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(9749828448191/2000000000000),(1154355215931/100000000000000),(-195399337/6250000000000),(8062781/100000000000000)⟩
def e107 : ℝ := (23909/12500000000000)
theorem h107 : Model (fun x => f107 ((103/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(538171223749147/50000000000000),(3823087324049/100000000000000),(-4045505249/50000000000000),(21681/160000000000)⟩
def e108 : ℝ := (172641/25000000000000)
theorem h108 : Model (fun x => f108 ((103/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(41265697511162937/50000000000000),(1693647325653661/100000000000000),(4731632097313/100000000000000),(-20309328751/100000000000000)⟩
def e109 : ℝ := (99776377/25000000000000)
theorem h109 : Model (fun x => f109 ((103/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(766013135967009/3125000000000),(13262143781229/12500000000000),(-14709405837/6250000000000),(49729827/12500000000000)⟩
def e110 : ℝ := (241227/1250000000000)
theorem h110 : Model (fun x => f110 ((103/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(2548320927572951/50000000000000),(861382804009/1000000000000),(2117074547/12500000000000),(-749912273/100000000000000)⟩
def e111 : ℝ := (19569293/100000000000000)
theorem h111 : Model (fun x => f111 ((103/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(54857319683899857/100000000000000),(1121991944216249/100000000000000),(3063067627571/100000000000000),(-13702953729/100000000000000)⟩
def e112 : ℝ := (132801911/50000000000000)
theorem h112 : Model (fun x => f112 ((103/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(137388714706225731/100000000000000),(281563926986991/10000000000000),(1948674931221/25000000000000),(-425153531/1250000000000)⟩
def e113 : ℝ := (66470933/10000000000000)
theorem h113 : Model (fun x => f113 ((103/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(255337711989003/3125000000000),(4420714593743/12500000000000),(-4903135279/6250000000000),(16576609/12500000000000)⟩
def e114 : ℝ := (80409/1250000000000)
theorem h114 : Model (fun x => f114 ((103/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(2161552788941/50000000000000),(108706096567/100000000000000),(81149451/25000000000000),(-3326607/100000000000000)⟩
def e115 : ℝ := (9617/25000000000000)
theorem h115 : Model (fun x => f115 ((103/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(179772707199/20000000000000),(33903386553/100000000000000),(157182131/50000000000000),(-657897/100000000000000)⟩
def e116 : ℝ := (9117/50000000000000)
theorem h116 : Model (fun x => f116 ((103/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(36722201387409/50000000000000),(3088069740467/100000000000000),(36971112179/100000000000000),(32016427/100000000000000)⟩
def e117 : ℝ := (31119/1562500000000)
theorem h117 : Model (fun x => f117 ((103/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(162159423948357/100000000000000),(1752551518769/25000000000000),(89068241563/100000000000000),(35696439/25000000000000)⟩
def e118 : ℝ := (4579929/100000000000000)
theorem h118 : Model (fun x => f118 ((103/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(17193859266271761/12500000000000),(1411324737972493/50000000000000),(7883767966447/100000000000000),(-8467374181/25000000000000)⟩
def e119 : ℝ := (669289259/100000000000000)
theorem h119 : Model (fun x => f119 ((103/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(1495139347/800000000000),(1174869831/12500000000000),(29247113/20000000000000),(418089/100000000000000)⟩
def e120 : ℝ := (7679/100000000000000)
theorem h120 : Model (fun x => f120 ((103/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(19429409831/50000000000000),(1221399329/50000000000000),(26681519/50000000000000),(393439/100000000000000)⟩
def e121 : ℝ := (1793/100000000000000)
theorem h121 : Model (fun x => f121 ((103/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(8079556563/100000000000000),(304745179/50000000000000),(17145807/100000000000000),(50333/25000000000000)⟩
def e122 : ℝ := (259/25000000000000)
theorem h122 : Model (fun x => f122 ((103/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(8399539/500000000000),(147846671/100000000000000),(2544273/50000000000000),(40827/50000000000000)⟩
def e123 : ℝ := (31/5000000000000)
theorem h123 : Model (fun x => f123 ((103/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(25198617/500000000000),(443540013/100000000000000),(7632819/50000000000000),(122481/50000000000000)⟩
def e124 : ℝ := (93/5000000000000)
theorem h124 : Model (fun x => f124 ((103/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-25198617/500000000000),(-443540013/100000000000000),(-7632819/50000000000000),(-122481/50000000000000)⟩
def e125 : ℝ := (93/5000000000000)
theorem h125 : Model (fun x => f125 ((103/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(537308082384573/390625000000),(2822649032404973/100000000000000),(7883752700809/100000000000000),(-16934870843/50000000000000)⟩
def e126 : ℝ := (669291119/100000000000000)
theorem h126 : Model (fun x => f126 ((103/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(766013135967009/2500000000000),(13262143781229/10000000000000),(-14709405837/5000000000000),(49729827/10000000000000)⟩
def e127 : ℝ := (241227/1000000000000)
theorem h127 : Model (fun x => f127 ((103/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(475295773845773/20000000000000),(11254765323603/100000000000000),(-8578200293/50000000000000),(1607863/25000000000000)⟩
def e128 : ℝ := (1076797/50000000000000)
theorem h128 : Model (fun x => f128 ((103/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(364082806235466873/50000000000000),(1650059919429731/25000000000000),(2678101878537/100000000000000),(-21037214147/50000000000000)⟩
def e129 : ℝ := (1353800557/100000000000000)
theorem h129 : Model (fun x => f129 ((103/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(13733139589/100000000000000),(-62239971/50000000000000),(538901/50000000000000),(-8519/100000000000000)⟩
def e130 : ℝ := (19/20000000000000)
theorem h130 : Model (fun x => f130 ((103/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (360781325631553717/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(9445026429037/50000000000000),(216415089663/100000000000000),(-474209549/50000000000000),(4239539/100000000000000)⟩
def e131 : ℝ := (340489/100000000000000)
theorem h131 : Model (fun x => f131 ((103/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(8439888288013/20000000000000),(546448133003/100000000000000),(-11664271/781250000000),(679629/12500000000000)⟩
def e132 : ℝ := (677937/100000000000000)
theorem h132 : Model (fun x => f132 ((103/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-438342055983539/100000000000000),(-1124863392467/20000000000000),(3953030583/25000000000000),(-6046499/10000000000000)⟩
def e133 : ℝ := (1793841/10000000000000)
theorem h133 : Model (fun x => f133 ((103/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(3883495145631/10000000000000),(-188519181827/50000000000000),(3660566637/100000000000000),(-17769741/50000000000000)⟩
def e134 : ℝ := (87107/25000000000000)
theorem h134 : Model (fun x => f134 ((103/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (51/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-170229924653799/100000000000000),(-106296609397/20000000000000),(353145613/3125000000000),(-33299173/25000000000000)⟩
def e135 : ℝ := (11395129/100000000000000)
theorem h135 : Model (fun x => f135 ((103/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(112550881/256000),(1092727/64000),(31827/128000),(103/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((103/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((103/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(9834543/32000),(286443/32000),(2781/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((103/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(7649089/10240),(1665613/64000),(42951/128000),(121/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((103/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-10609/1600),(-103/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((103/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(37905957/51200),(1657373/64000),(42871/128000),(121/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((103/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((103/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(309/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((103/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-309/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((103/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(37114917/51200),(1647773/64000),(42871/128000),(121/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((103/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(37268517/51200),(1647773/64000),(42871/128000),(121/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((103/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((103/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(37268517/800),(1647773/1000),(42871/2000),(121/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((103/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((103/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(21272116509/512000),(206525403/128000),(6015303/256000),(19467/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((103/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(2406906711/100000000000000),(-46736053/50000000000000),(113437/5000000000000),(-22027/50000000000000)⟩
def e151 : ℝ := (169/20000000000000)
theorem h151 : Model (fun x => f151 ((103/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (10216953117/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(28031826148849/25000000000000),(-194211286227/50000000000000),(815788839/25000000000000),(-26301161/100000000000000)⟩
def e152 : ℝ := (19336451/25000000000000)
theorem h152 : Model (fun x => f152 ((103/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(223/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((103/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(40809/1600),(203/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((103/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(429/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((103/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1165501165501/25000000000000),(-32601431203/100000000000000),(56995509/25000000000000),(-39857/2500000000000)⟩
def e156 : ℝ := (11229/100000000000000)
theorem h156 : Model (fun x => f156 ((103/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (213/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(4756293706293/4000000000000),(10983243883/3125000000000),(227982031/50000000000000),(-3188561/100000000000000)⟩
def e157 : ℝ := (276159/50000000000000)
theorem h157 : Model (fun x => f157 ((103/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(8756293706293/4000000000000),(10983243883/3125000000000),(227982031/50000000000000),(-3188561/100000000000000)⟩
def e158 : ℝ := (276159/50000000000000)
theorem h158 : Model (fun x => f158 ((103/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(54726835664331/50000000000000),(10983243883/6250000000000),(227982031/100000000000000),(-1594281/100000000000000)⟩
def e159 : ℝ := (863/312500000000)
theorem h159 : Model (fun x => f159 ((103/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(4726835664331/50000000000000),(10983243883/6250000000000),(227982031/100000000000000),(-1594281/100000000000000)⟩
def e160 : ℝ := (863/312500000000)
theorem h160 : Model (fun x => f160 ((103/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((103/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((103/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(403936167998633/100000000000000),(64853440071/10000000000000),(841362257/100000000000000),(-5883657/100000000000000)⟩
def e163 : ℝ := (203833/20000000000000)
theorem h163 : Model (fun x => f163 ((103/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(1379825226856459/50000000000000),(64853440071/10000000000000),(841362257/100000000000000),(-5883657/100000000000000)⟩
def e164 : ℝ := (509583/50000000000000)
theorem h164 : Model (fun x => f164 ((103/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((103/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1510269368713433/50000000000000),(27797154729/500000000000),(835209087/10000000000000),(-23739689/50000000000000)⟩
def e166 : ℝ := (4379471/50000000000000)
theorem h166 : Model (fun x => f166 ((103/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4151459844903909/50000000000000),(27797154729/500000000000),(835209087/10000000000000),(-23739689/50000000000000)⟩
def e167 : ℝ := (8758943/100000000000000)
theorem h167 : Model (fun x => f167 ((103/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((103/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(9087850427965011/100000000000000),(20675879978219/100000000000000),(37840528779/100000000000000),(-78494001/50000000000000)⟩
def e169 : ℝ := (32700389/100000000000000)
theorem h169 : Model (fun x => f169 ((103/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(1435689804701263/10000000000000),(20675879978219/100000000000000),(37840528779/100000000000000),(-78494001/50000000000000)⟩
def e170 : ℝ := (3270039/10000000000000)
theorem h170 : Model (fun x => f170 ((103/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((103/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15714152001368297/100000000000000),(47860159740261/100000000000000),(55241556461/50000000000000),(-143541629/50000000000000)⟩
def e172 : ℝ := (76074737/100000000000000)
theorem h172 : Model (fun x => f172 ((103/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(9024933143541291/50000000000000),(47860159740261/100000000000000),(55241556461/50000000000000),(-143541629/50000000000000)⟩
def e173 : ℝ := (38037369/50000000000000)
theorem h173 : Model (fun x => f173 ((103/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((103/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(308691270642599/1562500000000),(5256504706083/6250000000000),(123091922059/50000000000000),(-59744423/20000000000000)⟩
def e175 : ℝ := (134397507/100000000000000)
theorem h175 : Model (fun x => f175 ((103/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(2519827784188411/12500000000000),(5256504706083/6250000000000),(123091922059/50000000000000),(-59744423/20000000000000)⟩
def e176 : ℝ := (33599377/25000000000000)
theorem h176 : Model (fun x => f176 ((103/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((103/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(11032176083815559/50000000000000),(6374006425699/5000000000000),(463212983373/100000000000000),(-5995419/25000000000000)⟩
def e178 : ℝ := (51137913/25000000000000)
theorem h178 : Model (fun x => f178 ((103/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(2204673312001207/10000000000000),(6374006425699/5000000000000),(463212983373/100000000000000),(-5995419/25000000000000)⟩
def e179 : ℝ := (204551653/100000000000000)
theorem h179 : Model (fun x => f179 ((103/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((103/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(150818492549283/625000000000),(22284353042741/12500000000000),(781289460981/100000000000000),(72690907/10000000000000)⟩
def e181 : ℝ := (71628187/25000000000000)
theorem h181 : Model (fun x => f181 ((103/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(24134292141218613/100000000000000),(22284353042741/12500000000000),(781289460981/100000000000000),(72690907/10000000000000)⟩
def e182 : ℝ := (286512749/100000000000000)
theorem h182 : Model (fun x => f182 ((103/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(228157665652991/10000000000000),(59265166599927/100000000000000),(442168126989/100000000000000),(365840139/25000000000000)⟩
def e183 : ℝ := (23740273/25000000000000)
theorem h183 : Model (fun x => f183 ((103/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(119801061673227/100000000000000),(384690037149/100000000000000),(40394321/5000000000000),(-672181/25000000000000)⟩
def e184 : ℝ := (610599/100000000000000)
theorem h184 : Model (fun x => f184 ((103/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(104726835664331/50000000000000),(10983243883/6250000000000),(227982031/100000000000000),(-1594281/100000000000000)⟩
def e185 : ℝ := (863/312500000000)
theorem h185 : Model (fun x => f185 ((103/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(438708404330551/100000000000000),(147230768281/20000000000000),(631925241/50000000000000),(-2938643/50000000000000)⟩
def e186 : ℝ := (1162919/100000000000000)
theorem h186 : Model (fun x => f186 ((103/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(918890859297729/100000000000000),(92514074847/4000000000000),(4941014713/100000000000000),(-308103/2000000000000)⟩
def e187 : ℝ := (458827/12500000000000)
theorem h187 : Model (fun x => f187 ((103/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1924650640302583/100000000000000),(6459137542093/100000000000000),(16508461347/100000000000000),(-32960529/100000000000000)⟩
def e188 : ℝ := (5145753/50000000000000)
theorem h188 : Model (fun x => f188 ((103/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(461150380116611/20000000000000),(15142054613529/100000000000000),(2406958469/4000000000000),(24453293/100000000000000)⟩
def e189 : ℝ := (12164127/50000000000000)
theorem h189 : Model (fun x => f189 ((103/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((103/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(54726835664331/6250000000000),(10983243883/781250000000),(227982031/12500000000000),(-1594281/12500000000000)⟩
def e191 : ℝ := (863/39062500000)
theorem h191 : Model (fun x => f191 ((103/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(995430432302523/100000000000000),(1790545254173/100000000000000),(657935667/25000000000000),(-3860743/25000000000000)⟩
def e192 : ℝ := (2819879/100000000000000)
theorem h192 : Model (fun x => f192 ((103/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1095430432302523/100000000000000),(1790545254173/100000000000000),(657935667/25000000000000),(-3860743/25000000000000)⟩
def e193 : ℝ := (2819879/100000000000000)
theorem h193 : Model (fun x => f193 ((103/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(25257908012380599/100000000000000),(103578102770679/50000000000000),(99097068591/10000000000000),(34693353/2500000000000)⟩
def e194 : ℝ := (166354509/50000000000000)
theorem h194 : Model (fun x => f194 ((103/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(395915607701/100000000000000),(-405894537/12500000000000),(2219723/20000000000000),(14619/100000000000000)⟩
def e195 : ℝ := (5687/100000000000000)
theorem h195 : Model (fun x => f195 ((103/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (25049759115710193/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(35285617519/390625000000),(5017302639/3125000000000),(79403447/100000000000000),(-1653061/100000000000000)⟩
def e196 : ℝ := (522659/100000000000000)
theorem h196 : Model (fun x => f196 ((103/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(4756293706293/2000000000000),(10983243883/1562500000000),(227982031/25000000000000),(-3188561/50000000000000)⟩
def e197 : ℝ := (276159/25000000000000)
theorem h197 : Model (fun x => f197 ((103/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(2284071397197/5000000000000),(-18335803923/25000000000000),(1130249/5000000000000),(39093/5000000000000)⟩
def e198 : ℝ := (59003/50000000000000)
theorem h198 : Model (fun x => f198 ((103/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (6829856848379/3125000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(108637144112119/100000000000000),(73343215691/50000000000000),(-22604981/50000000000000),(-390931/25000000000000)⟩
def e199 : ℝ := (797279/100000000000000)
theorem h199 : Model (fun x => f199 ((103/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(8637144112119/100000000000000),(73343215691/50000000000000),(-22604981/50000000000000),(-390931/25000000000000)⟩
def e200 : ℝ := (797279/100000000000000)
theorem h200 : Model (fun x => f200 ((103/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(80184558749421/20000000000000),(541342782481/100000000000000),(-166846289/100000000000000),(-5770887/100000000000000)⟩
def e201 : ℝ := (1471171/50000000000000)
theorem h201 : Model (fun x => f201 ((103/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(275663707946139/10000000000000),(541342782481/100000000000000),(-166846289/100000000000000),(-5770887/100000000000000)⟩
def e202 : ℝ := (2942343/100000000000000)
theorem h202 : Model (fun x => f202 ((103/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1497365898331289/50000000000000),(4631711896759/100000000000000),(-633455211/100000000000000),(-9973001/20000000000000)⟩
def e203 : ℝ := (393751/1562500000000)
theorem h203 : Model (fun x => f203 ((103/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(827711274904353/10000000000000),(4631711896759/100000000000000),(-633455211/100000000000000),(-9973001/20000000000000)⟩
def e204 : ℝ := (5040013/20000000000000)
theorem h204 : Model (fun x => f204 ((103/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4496009452750497/50000000000000),(2146645105147/12500000000000),(1181922857/50000000000000),(-729009/390625000000)⟩
def e205 : ℝ := (11698443/12500000000000)
theorem h205 : Model (fun x => f205 ((103/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14261066524548613/100000000000000),(2146645105147/12500000000000),(1181922857/50000000000000),(-729009/390625000000)⟩
def e206 : ℝ := (18717509/20000000000000)
theorem h206 : Model (fun x => f206 ((103/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15492815392199037/100000000000000),(39575481053507/100000000000000),(21311288511/100000000000000),(-215022873/50000000000000)⟩
def e207 : ℝ := (108094503/50000000000000)
theorem h207 : Model (fun x => f207 ((103/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8914264838956661/50000000000000),(39575481053507/100000000000000),(21311288511/100000000000000),(-215022873/50000000000000)⟩
def e208 : ℝ := (216189007/100000000000000)
theorem h208 : Model (fun x => f208 ((103/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(19368405479266601/100000000000000),(34572853168787/50000000000000),(36571782289/50000000000000),(-366304853/50000000000000)⟩
def e209 : ℝ := (189448531/50000000000000)
theorem h209 : Model (fun x => f209 ((103/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(19770786431647553/100000000000000),(34572853168787/50000000000000),(36571782289/50000000000000),(-366304853/50000000000000)⟩
def e210 : ℝ := (378897063/100000000000000)
theorem h210 : Model (fun x => f210 ((103/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(21478417747848221/100000000000000),(104118981714033/100000000000000),(85975041853/50000000000000),(-514507929/50000000000000)⟩
def e211 : ℝ := (572548903/100000000000000)
theorem h211 : Model (fun x => f211 ((103/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(21460798700229173/100000000000000),(104118981714033/100000000000000),(85975041853/50000000000000),(-514507929/50000000000000)⟩
def e212 : ℝ := (71568613/12500000000000)
theorem h212 : Model (fun x => f212 ((103/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(23314398811579727/100000000000000),(28918393594437/20000000000000),(164913829983/50000000000000),(-1248325811/100000000000000)⟩
def e213 : ℝ := (398996191/50000000000000)
theorem h213 : Model (fun x => f213 ((103/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(1165886607245653/5000000000000),(28918393594437/20000000000000),(164913829983/50000000000000),(-1248325811/100000000000000)⟩
def e214 : ℝ := (797992383/100000000000000)
theorem h214 : Model (fun x => f214 ((103/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(2013986129034037/100000000000000),(46692565810893/100000000000000),(115021275177/50000000000000),(-54002223/100000000000000)⟩
def e215 : ℝ := (130701687/50000000000000)
theorem h215 : Model (fun x => f215 ((103/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(118020290808373/100000000000000),(159355949853/50000000000000),(29234867/25000000000000),(-882551/25000000000000)⟩
def e216 : ℝ := (217399/12500000000000)
theorem h216 : Model (fun x => f216 ((103/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(208637144112119/100000000000000),(73343215691/50000000000000),(-22604981/50000000000000),(-390931/25000000000000)⟩
def e217 : ℝ := (797279/100000000000000)
theorem h217 : Model (fun x => f217 ((103/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(435294579032611/100000000000000),(61208476247/10000000000000),(3314943/12500000000000),(-1664413/25000000000000)⟩
def e218 : ℝ := (2667/80000000000)
theorem h218 : Model (fun x => f218 ((103/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(90818617816851/10000000000000),(383110850389/20000000000000),(945473/125000000000),(-5233741/25000000000000)⟩
def e219 : ℝ := (10455079/100000000000000)
theorem h219 : Model (fun x => f219 ((103/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(94740685267589/5000000000000),(1332185895059/25000000000000),(3977353839/100000000000000),(-28818077/50000000000000)⟩
def e220 : ℝ := (5829117/20000000000000)
theorem h220 : Model (fun x => f220 ((103/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1118132322666539/50000000000000),(12327995426043/100000000000000),(2986651191/12500000000000),(-58002721/50000000000000)⟩
def e221 : ℝ := (16976299/25000000000000)
theorem h221 : Model (fun x => f221 ((103/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(108637144112119/12500000000000),(73343215691/6250000000000),(-22604981/6250000000000),(-390931/3125000000000)⟩
def e222 : ℝ := (797279/12500000000000)
theorem h222 : Model (fun x => f222 ((103/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(39484697748213/4000000000000),(746101675381/50000000000000),(-61185057/25000000000000),(-4009999/25000000000000)⟩
def e223 : ℝ := (507339/6250000000000)
theorem h223 : Model (fun x => f223 ((103/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(43484697748213/4000000000000),(746101675381/50000000000000),(-61185057/25000000000000),(-4009999/25000000000000)⟩
def e224 : ℝ := (507339/6250000000000)
theorem h224 : Model (fun x => f224 ((103/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(24310823046830909/100000000000000),(83694702352637/50000000000000),(438232970277/100000000000000),(-1293448447/100000000000000)⟩
def e225 : ℝ := (462761469/50000000000000)
theorem h225 : Model (fun x => f225 ((103/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(82267885219/20000000000000),(-566446159/20000000000000),(2417219/20000000000000),(-5139/50000000000000)⟩
def e226 : ℝ := (16181/100000000000000)
theorem h226 : Model (fun x => f226 ((103/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (24142993190183973/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(8284318984801/100000000000000),(67512098441/50000000000000),(-26554649/20000000000000),(-1301159/100000000000000)⟩
def e227 : ℝ := (360183/25000000000000)
theorem h227 : Model (fun x => f227 ((103/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(3463487413933/20000000000000),(29557788133/10000000000000),(-26684899/50000000000000),(-147711/5000000000000)⟩
def e228 : ℝ := (1963391/100000000000000)
theorem h228 : Model (fun x => f228 ((103/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(19417575411219/100000000000000),(132079338383/50000000000000),(-642838451/100000000000000),(1985291/100000000000000)⟩
def e229 : ℝ := (15900253/100000000000000)
theorem h229 : Model (fun x => f229 ((103/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7540805984939/100000000000000),(29374185297/100000000000000),(-267416133/50000000000000),(5963533/100000000000000)⟩
def e230 : ℝ := (3214587/50000000000000)
theorem h230 : Model (fun x => f230 ((103/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-8134455933443/5000000000000),(-62763607711/12500000000000),(215316547/2000000000000),(-127233159/100000000000000)⟩
def e231 : ℝ := (17824303/100000000000000)
theorem h231 : Model (fun x => f231 ((103/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((103/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-10609/320),(-103/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((103/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2163/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((103/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1339/64),(-19/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((103/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((103/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3003/64),(-19/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((103/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((103/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(375375/32),(-475/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((103/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14111/1600),(17/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((103/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23711/1600),(17/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((103/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((103/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4481379/1600),(3213/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((103/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(35703295793/100000000000000),(-51196157/100000000000000),(1579181/100000000000000),(-553/12500000000000)⟩
def e244 : ℝ := (19/25000000000000)
theorem h244 : Model (fun x => f244 ((103/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1118691/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(26176024723237/6250000000000),(-12972629013/781250000000),(-7848780557/100000000000000),(-58780533/100000000000000)⟩
def e245 : ℝ := (1999689/100000000000000)
theorem h245 : Model (fun x => f245 ((103/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(927/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((103/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(84769/1600),(463/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((103/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(118369/1600),(463/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((103/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(33489/1600),(183/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((103/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3964059441/2560000),(18583467/640000),(245387/1280000),(323/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((103/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((103/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(184041/160),(1287/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((103/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(43468574937/50000000000000),(-243180839/20000000000000),(12754239/100000000000000),(-118921/100000000000000)⟩
def e253 : ℝ := (1063/100000000000000)
theorem h253 : Model (fun x => f253 ((103/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (90729/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(13461876161393/10000000000000),(25663408117/4000000000000),(555115699/50000000000000),(-605419/20000000000000)⟩
def e254 : ℝ := (837393/25000000000000)
theorem h254 : Model (fun x => f254 ((103/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(23461876161393/10000000000000),(25663408117/4000000000000),(555115699/50000000000000),(-605419/20000000000000)⟩
def e255 : ℝ := (837393/25000000000000)
theorem h255 : Model (fun x => f255 ((103/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(23461876161393/20000000000000),(160396300731/50000000000000),(555115699/100000000000000),(-378387/25000000000000)⟩
def e256 : ℝ := (1674787/100000000000000)
theorem h256 : Model (fun x => f256 ((103/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(3461876161393/20000000000000),(160396300731/50000000000000),(555115699/100000000000000),(-378387/25000000000000)⟩
def e257 : ℝ := (1674787/100000000000000)
theorem h257 : Model (fun x => f257 ((103/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(54115934598451/12500000000000),(73992341111/6250000000000),(204864127/10000000000000),(-5585713/100000000000000)⟩
def e258 : ℝ := (1545191/25000000000000)
theorem h258 : Model (fun x => f258 ((103/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2788641762501893/100000000000000),(73992341111/6250000000000),(204864127/10000000000000),(-5585713/100000000000000)⟩
def e259 : ℝ := (1236153/20000000000000)
theorem h259 : Model (fun x => f259 ((103/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1635669192257703/50000000000000),(2066911154123/20000000000000),(2710153487/12500000000000),(-17808109/50000000000000)⟩
def e260 : ℝ := (1350467/2500000000000)
theorem h260 : Model (fun x => f260 ((103/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4276859668448179/50000000000000),(2066911154123/20000000000000),(2710153487/12500000000000),(-17808109/50000000000000)⟩
def e261 : ℝ := (54018681/100000000000000)
theorem h261 : Model (fun x => f261 ((103/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8027452152063/80000000000),(19781551083123/50000000000000),(106069643389/100000000000000),(-44325297/100000000000000)⟩
def e262 : ℝ := (207123441/100000000000000)
theorem h262 : Model (fun x => f262 ((103/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(15303362809126369/100000000000000),(19781551083123/50000000000000),(106069643389/100000000000000),(-44325297/100000000000000)⟩
def e263 : ℝ := (103561721/50000000000000)
theorem h263 : Model (fun x => f263 ((103/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(4488070038507377/25000000000000),(47751642922907/50000000000000),(33629651597/10000000000000),(138131543/50000000000000)⟩
def e264 : ℝ := (50075797/10000000000000)
theorem h264 : Model (fun x => f264 ((103/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(20287994439743793/100000000000000),(47751642922907/50000000000000),(33629651597/10000000000000),(138131543/50000000000000)⟩
def e265 : ℝ := (500757971/100000000000000)
theorem h265 : Model (fun x => f265 ((103/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(23799720655414931/100000000000000),(141693358739/80000000000),(813496677853/100000000000000),(203247757/12500000000000)⟩
def e266 : ℝ := (931742213/100000000000000)
theorem h266 : Model (fun x => f266 ((103/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(24202101607795883/100000000000000),(141693358739/80000000000),(813496677853/100000000000000),(203247757/12500000000000)⟩
def e267 : ℝ := (465871107/50000000000000)
theorem h267 : Model (fun x => f267 ((103/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(28391335538377871/100000000000000),(57082610716553/20000000000000),(414208711421/25000000000000),(5133958811/100000000000000)⟩
def e268 : ℝ := (1511383259/100000000000000)
theorem h268 : Model (fun x => f268 ((103/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(28373716490758823/100000000000000),(57082610716553/20000000000000),(414208711421/25000000000000),(5133958811/100000000000000)⟩
def e269 : ℝ := (75569163/5000000000000)
theorem h269 : Model (fun x => f269 ((103/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(33285031127232893/100000000000000),(8516741383247/2000000000000),(754178403149/25000000000000),(780783859/6250000000000)⟩
def e270 : ℝ := (569802187/25000000000000)
theorem h270 : Model (fun x => f270 ((103/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(16644182230283113/50000000000000),(8516741383247/2000000000000),(754178403149/25000000000000),(780783859/6250000000000)⟩
def e271 : ℝ := (2279208749/100000000000000)
theorem h271 : Model (fun x => f271 ((103/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(360125610555613/6250000000000),(45124092563933/25000000000000),(518254299069/25000000000000),(13699828747/100000000000000)⟩
def e272 : ℝ := (1016933009/100000000000000)
theorem h272 : Model (fun x => f272 ((103/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(27522981650627/20000000000000),(752639628899/100000000000000),(233148451/10000000000000),(1309/12500000000000)⟩
def e273 : ℝ := (493347/12500000000000)
theorem h273 : Model (fun x => f273 ((103/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(43461876161393/20000000000000),(160396300731/50000000000000),(555115699/100000000000000),(-378387/25000000000000)⟩
def e274 : ℝ := (1674787/100000000000000)
theorem h274 : Model (fun x => f274 ((103/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(94446733973413/20000000000000),(1394224831823/100000000000000),(860428977/25000000000000),(-188539/6250000000000)⟩
def e275 : ℝ := (145927/2000000000000)
theorem h275 : Model (fun x => f275 ((103/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(513104031975063/50000000000000),(4544672023637/100000000000000),(7286592437/50000000000000),(15867/312500000000)⟩
def e276 : ℝ := (23823161/100000000000000)
theorem h276 : Model (fun x => f276 ((103/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1115023194780581/50000000000000),(13167998179031/100000000000000),(51944511493/100000000000000),(1054367/1562500000000)⟩
def e277 : ℝ := (69138271/100000000000000)
theorem h277 : Model (fun x => f277 ((103/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1534438146498471/50000000000000),(8726335370879/25000000000000),(1112920753/500000000000),(395530091/50000000000000)⟩
def e278 : ℝ := (4648129/2500000000000)
theorem h278 : Model (fun x => f278 ((103/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(23461876161393/2500000000000),(160396300731/6250000000000),(555115699/12500000000000),(-378387/3125000000000)⟩
def e279 : ℝ := (1674787/12500000000000)
theorem h279 : Model (fun x => f279 ((103/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(215217990941771/20000000000000),(663796088119/20000000000000),(3386205051/50000000000000),(-1512239/12500000000000)⟩
def e280 : ℝ := (1084067/6250000000000)
theorem h280 : Model (fun x => f280 ((103/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(235217990941771/20000000000000),(663796088119/20000000000000),(3386205051/50000000000000),(-1512239/12500000000000)⟩
def e281 : ℝ := (1084067/6250000000000)
theorem h281 : Model (fun x => f281 ((103/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(36092745804378523/100000000000000),(512373618755079/100000000000000),(1992064090313/50000000000000),(18683766677/100000000000000)⟩
def e282 : ℝ := (2768355871/100000000000000)
theorem h282 : Model (fun x => f282 ((103/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(138531992747/50000000000000),(-393320801/10000000000000),(6312997/25000000000000),(-67733/100000000000000)⟩
def e283 : ℝ := (22089/100000000000000)
theorem h283 : Model (fun x => f283 ((103/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (3557636660532027/10000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(15964453910239/100000000000000),(54691721467/20000000000000),(49654193/50000000000000),(-237831/12500000000000)⟩
def e284 : ℝ := (21553/500000000000)
theorem h284 : Model (fun x => f284 ((103/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(13461876161393/5000000000000),(25663408117/2000000000000),(555115699/25000000000000),(-605419/10000000000000)⟩
def e285 : ℝ := (837393/12500000000000)
theorem h285 : Model (fun x => f285 ((103/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(8524467464759/20000000000000),(-56911353/48828125000),(117036479/100000000000000),(390709/50000000000000)⟩
def e286 : ℝ := (77007/12500000000000)
theorem h286 : Model (fun x => f286 ((103/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (11698802990147/5000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(114755325352409/100000000000000),(233108901887/100000000000000),(-234072961/100000000000000),(-781419/50000000000000)⟩
def e287 : ℝ := (2274707/50000000000000)
theorem h287 : Model (fun x => f287 ((103/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(14755325352409/100000000000000),(233108901887/100000000000000),(-234072961/100000000000000),(-781419/50000000000000)⟩
def e288 : ℝ := (2274707/50000000000000)
theorem h288 : Model (fun x => f288 ((103/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(211750897971707/50000000000000),(430141426101/50000000000000),(-86384069/10000000000000),(-5767617/100000000000000)⟩
def e289 : ℝ := (8394753/50000000000000)
theorem h289 : Model (fun x => f289 ((103/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2779216081657699/100000000000000),(430141426101/50000000000000),(-86384069/10000000000000),(-5767617/100000000000000)⟩
def e290 : ℝ := (16789507/100000000000000)
theorem h290 : Model (fun x => f290 ((103/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(637859691350553/20000000000000),(3732910237507/50000000000000),(-274565033/5000000000000),(-1690021/3125000000000)⟩
def e291 : ℝ := (18226019/12500000000000)
theorem h291 : Model (fun x => f291 ((103/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8471679409133717/100000000000000),(3732910237507/50000000000000),(-274565033/5000000000000),(-1690021/3125000000000)⟩
def e292 : ℝ := (145808153/100000000000000)
theorem h292 : Model (fun x => f292 ((103/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9721703268764437/100000000000000),(28315665418347/100000000000000),(-2181994663/25000000000000),(-112367627/50000000000000)⟩
def e293 : ℝ := (276822321/50000000000000)
theorem h293 : Model (fun x => f293 ((103/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1873843860976507/12500000000000),(28315665418347/100000000000000),(-2181994663/25000000000000),(-112367627/50000000000000)⟩
def e294 : ℝ := (553644643/100000000000000)
theorem h294 : Model (fun x => f294 ((103/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(3440536990815573/20000000000000),(33719254377859/50000000000000),(1045061097/5000000000000),(-115760367/20000000000000)⟩
def e295 : ℝ := (330213801/25000000000000)
theorem h295 : Model (fun x => f295 ((103/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(390767984795843/2000000000000),(33719254377859/50000000000000),(1045061097/5000000000000),(-115760367/20000000000000)⟩
def e296 : ℝ := (264171041/20000000000000)
theorem h296 : Model (fun x => f296 ((103/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(2802669202034511/12500000000000),(61467514024807/50000000000000),(529126261/390625000000),(-1078692163/100000000000000)⟩
def e297 : ℝ := (1206619377/50000000000000)
theorem h297 : Model (fun x => f297 ((103/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(285296682108213/1250000000000),(61467514024807/50000000000000),(529126261/390625000000),(-1078692163/100000000000000)⟩
def e298 : ℝ := (482647751/20000000000000)
theorem h298 : Model (fun x => f298 ((103/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(26191450861832629/100000000000000),(194278648433009/100000000000000),(388591646563/100000000000000),(-391637903/25000000000000)⟩
def e299 : ℝ := (1911824881/50000000000000)
theorem h299 : Model (fun x => f299 ((103/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(26173831814213581/100000000000000),(194278648433009/100000000000000),(388591646563/100000000000000),(-391637903/25000000000000)⟩
def e300 : ℝ := (3823649763/100000000000000)
theorem h300 : Model (fun x => f300 ((103/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(3003586585559313/10000000000000),(11358345080937/4000000000000),(418772284567/50000000000000),(-877834027/50000000000000)⟩
def e301 : ℝ := (5603976489/100000000000000)
theorem h301 : Model (fun x => f301 ((103/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(30039199188926463/100000000000000),(11358345080937/4000000000000),(418772284567/50000000000000),(-877834027/50000000000000)⟩
def e302 : ℝ := (560397649/10000000000000)
theorem h302 : Model (fun x => f302 ((103/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(886476314716861/20000000000000),(22384613329699/20000000000000),(178800405103/25000000000000),(139800507/25000000000000)⟩
def e303 : ℝ := (557506467/25000000000000)
theorem h303 : Model (fun x => f303 ((103/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(32921961741843/25000000000000),(535009757571/100000000000000),(247009/4000000000000),(-467817/10000000000000)⟩
def e304 : ℝ := (1046937/10000000000000)
theorem h304 : Model (fun x => f304 ((103/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(214755325352409/100000000000000),(233108901887/100000000000000),(-234072961/100000000000000),(-781419/50000000000000)⟩
def e305 : ℝ := (2274707/50000000000000)
theorem h305 : Model (fun x => f305 ((103/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(46119849767219/10000000000000),(200245512269/20000000000000),(-461970697/100000000000000),(-3901923/50000000000000)⟩
def e306 : ℝ := (9784099/50000000000000)
theorem h306 : Model (fun x => f306 ((103/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(495224167098167/50000000000000),(3225284260327/100000000000000),(6557573/2500000000000),(-27387459/100000000000000)⟩
def e307 : ℝ := (15782399/25000000000000)
theorem h307 : Model (fun x => f307 ((103/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(531760135637713/25000000000000),(1154411617801/12500000000000),(1440840617/25000000000000),(-81233197/100000000000000)⟩
def e308 : ℝ := (90521373/50000000000000)
theorem h308 : Model (fun x => f308 ((103/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(112042155784333/4000000000000),(5885408221781/25000000000000),(14282678967/25000000000000),(-17507597/10000000000000)⟩
def e309 : ℝ := (57987717/12500000000000)
theorem h309 : Model (fun x => f309 ((103/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(114755325352409/12500000000000),(233108901887/12500000000000),(-234072961/12500000000000),(-781419/6250000000000)⟩
def e310 : ℝ := (2274707/6250000000000)
theorem h310 : Model (fun x => f310 ((103/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(262432612446661/25000000000000),(2399880972667/100000000000000),(-1866408463/100000000000000),(-8590437/50000000000000)⟩
def e311 : ℝ := (23432341/50000000000000)
theorem h311 : Model (fun x => f311 ((103/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(287432612446661/25000000000000),(2399880972667/100000000000000),(-1866408463/100000000000000),(-8590437/50000000000000)⟩
def e312 : ℝ := (23432341/50000000000000)
theorem h312 : Model (fun x => f312 ((103/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(8051142385311651/25000000000000),(10558977535347/3125000000000),(584770648943/50000000000000),(-1562461127/100000000000000)⟩
def e313 : ℝ := (267113811/4000000000000)
theorem h313 : Model (fun x => f313 ((103/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(310514940657/100000000000000),(-3257893229/100000000000000),(22904843/100000000000000),(-106937/100000000000000)⟩
def e314 : ℝ := (65901/100000000000000)
theorem h314 : Model (fun x => f314 ((103/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (7966376119627803/25000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(13763207012907/100000000000000),(40627116963/20000000000000),(-410296083/100000000000000),(-668153/100000000000000)⟩
def e315 : ℝ := (5009747/50000000000000)
theorem h315 : Model (fun x => f315 ((103/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(14863830461573/50000000000000),(9531883843/2000000000000),(-310987697/100000000000000),(-2570801/100000000000000)⟩
def e316 : ℝ := (7165047/50000000000000)
theorem h316 : Model (fun x => f316 ((103/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(31126079491531/25000000000000),(375606960961/25000000000000),(-11549556279/100000000000000),(-60483907/100000000000000)⟩
def e317 : ℝ := (61073301/100000000000000)
theorem h317 : Model (fun x => f317 ((103/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(24175595721577/50000000000000),(28509520171/25000000000000),(-5592430407/100000000000000),(1925409/6250000000000)⟩
def e318 : ℝ := (25119999/100000000000000)
theorem h318 : Model (fun x => f318 ((103/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-57168963612853/50000000000000),(-97017695251/25000000000000),(5173396943/100000000000000),(-19285323/20000000000000)⟩
def e319 : ℝ := (21472151/50000000000000)
theorem h319 : Model (fun x => f319 ((103/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((103/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-116699/1600),(-1133/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((103/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((103/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(9991/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((103/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(282941/1600),(807/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((103/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((103/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(455741/1600),(807/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((103/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2278705/32),(4035/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((103/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((103/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(542384569845125629/50000000000000),(1555486936420587/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (35063/25000000000000)
theorem h329 : Model (fun x => f329 ((103/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4609275667/50000000000000),(-13218791/100000000000000),(203871/50000000000000),(-1143/100000000000000)⟩
def e330 : ℝ := (11/50000000000000)
theorem h330 : Model (fun x => f330 ((103/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (541583951568956671/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(328224359649101/50000000000000),(1383499503741/100000000000000),(985711773/10000000000000),(22077369/50000000000000)⟩
def e331 : ℝ := (2563219/100000000000000)
theorem h331 : Model (fun x => f331 ((103/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((103/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(463/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((103/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((103/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((103/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(765806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((103/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((103/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((103/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(106171714907111/3125000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (541/50000000000000)
theorem h339 : Model (fun x => f339 ((103/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3864193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((103/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((103/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((103/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2177505122972189/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (541/50000000000000)
theorem h343 : Model (fun x => f343 ((103/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(459241169837/10000000000000),(-1485566099/25000000000000),(96111/1250000000000),(-9949/100000000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((103/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1087343790668313/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(78013476092067/50000000000000),(81682168453/10000000000000),(-528455511/50000000000000),(273513/20000000000000)⟩
def e345 : ℝ := (23/800000000000)
theorem h345 : Model (fun x => f345 ((103/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(128013476092067/50000000000000),(81682168453/10000000000000),(-528455511/50000000000000),(273513/20000000000000)⟩
def e346 : ℝ := (23/800000000000)
theorem h346 : Model (fun x => f346 ((103/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(128013476092067/100000000000000),(81682168453/20000000000000),(-528455511/100000000000000),(341891/50000000000000)⟩
def e347 : ℝ := (719/50000000000000)
theorem h347 : Model (fun x => f347 ((103/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(28013476092067/100000000000000),(81682168453/20000000000000),(-528455511/100000000000000),(341891/50000000000000)⟩
def e348 : ℝ := (719/50000000000000)
theorem h348 : Model (fun x => f348 ((103/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(236215342788933/50000000000000),(1507230489311/100000000000000),(-975126241/50000000000000),(2523481/100000000000000)⟩
def e349 : ℝ := (5309/100000000000000)
theorem h349 : Model (fun x => f349 ((103/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2828144971292151/100000000000000),(1507230489311/100000000000000),(-975126241/50000000000000),(2523481/100000000000000)⟩
def e350 : ℝ := (531/10000000000000)
theorem h350 : Model (fun x => f350 ((103/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(452550835834259/12500000000000),(2695981767963/20000000000000),(-11286381219/100000000000000),(103729/1562500000000)⟩
def e351 : ℝ := (78459/100000000000000)
theorem h351 : Model (fun x => f351 ((103/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(556424227440939/6250000000000),(2695981767963/20000000000000),(-11286381219/100000000000000),(103729/1562500000000)⟩
def e352 : ℝ := (3923/5000000000000)
theorem h352 : Model (fun x => f352 ((103/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(11396767925849199/100000000000000),(53616049861617/100000000000000),(-3220975803/50000000000000),(-47956093/100000000000000)⟩
def e353 : ℝ := (204011/50000000000000)
theorem h353 : Model (fun x => f353 ((103/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(8332907772448409/50000000000000),(53616049861617/100000000000000),(-3220975803/50000000000000),(-47956093/100000000000000)⟩
def e354 : ℝ := (408023/100000000000000)
theorem h354 : Model (fun x => f354 ((103/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(21334489798114473/100000000000000),(34175191702089/25000000000000),(122655773949/100000000000000),(-128539507/50000000000000)⟩
def e355 : ℝ := (969433/100000000000000)
theorem h355 : Model (fun x => f355 ((103/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(11835102041914379/50000000000000),(34175191702089/25000000000000),(122655773949/100000000000000),(-128539507/50000000000000)⟩
def e356 : ℝ := (484717/50000000000000)
theorem h356 : Model (fun x => f356 ((103/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(30301051045795593/100000000000000),(16979192706281/6250000000000),(295115087509/50000000000000),(-97176611/25000000000000)⟩
def e357 : ℝ := (1176451/50000000000000)
theorem h357 : Model (fun x => f357 ((103/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(6140686399635309/20000000000000),(16979192706281/6250000000000),(295115087509/50000000000000),(-97176611/25000000000000)⟩
def e358 : ℝ := (2352903/100000000000000)
theorem h358 : Model (fun x => f358 ((103/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(1965226529021489/5000000000000),(47316662195891/10000000000000),(425709502147/25000000000000),(343636133/50000000000000)⟩
def e359 : ℝ := (6322193/100000000000000)
theorem h359 : Model (fun x => f359 ((103/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(9821727883202683/25000000000000),(47316662195891/10000000000000),(425709502147/25000000000000),(343636133/50000000000000)⟩
def e360 : ℝ := (3161097/50000000000000)
theorem h360 : Model (fun x => f360 ((103/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(50292541102366179/100000000000000),(191542261692017/25000000000000),(976178015993/25000000000000),(560253791/10000000000000)⟩
def e361 : ℝ := (5827663/50000000000000)
theorem h361 : Model (fun x => f361 ((103/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(6286984304462439/12500000000000),(191542261692017/25000000000000),(976178015993/25000000000000),(560253791/10000000000000)⟩
def e362 : ℝ := (11655327/100000000000000)
theorem h362 : Model (fun x => f362 ((103/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(176120284504259/1250000000000),(420044387148577/100000000000000),(1978585858661/50000000000000),(13811784631/100000000000000)⟩
def e363 : ℝ := (2307127/20000000000000)
theorem h363 : Model (fun x => f363 ((103/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(81937250305871/50000000000000),(6535261449/625000000000),(157502811/50000000000000),(-2565873/100000000000000)⟩
def e364 : ℝ := (151/1250000000000)
theorem h364 : Model (fun x => f364 ((103/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(228013476092067/100000000000000),(81682168453/20000000000000),(-528455511/100000000000000),(341891/50000000000000)⟩
def e365 : ℝ := (719/50000000000000)
theorem h365 : Model (fun x => f365 ((103/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(129975363198969/25000000000000),(186246351637/10000000000000),(-3709527/500000000000),(-1198309/100000000000000)⟩
def e366 : ℝ := (3739/25000000000000)
theorem h366 : Model (fun x => f366 ((103/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1185445374773033/100000000000000),(6370001706933/100000000000000),(3167410763/100000000000000),(-12049627/100000000000000)⟩
def e367 : ℝ := (53431/100000000000000)
theorem h367 : Model (fun x => f367 ((103/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2702975206192623/100000000000000),(19365949758803/100000000000000),(26973349593/100000000000000),(-156623/390625000000)⟩
def e368 : ℝ := (161669/100000000000000)
theorem h368 : Model (fun x => f368 ((103/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1107371780201841/25000000000000),(14999823229043/25000000000000),(51043087523/20000000000000),(41597453/20000000000000)⟩
def e369 : ℝ := (1427503/100000000000000)
theorem h369 : Model (fun x => f369 ((103/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(128013476092067/12500000000000),(81682168453/2500000000000),(-528455511/12500000000000),(341891/6250000000000)⟩
def e370 : ℝ := (719/6250000000000)
theorem h370 : Model (fun x => f370 ((103/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(593991154674139/50000000000000),(107823214249/2500000000000),(-1956319233/50000000000000),(2904383/100000000000000)⟩
def e371 : ℝ := (737/3125000000000)
theorem h371 : Model (fun x => f371 ((103/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(643991154674139/50000000000000),(107823214249/2500000000000),(-1956319233/50000000000000),(2904383/100000000000000)⟩
def e372 : ℝ := (737/3125000000000)
theorem h372 : Model (fun x => f372 ((103/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(11410202102171847/20000000000000),(963820894030349/100000000000000),(5701546516227/100000000000000),(11467192559/100000000000000)⟩
def e373 : ℝ := (10117249/50000000000000)
theorem h373 : Model (fun x => f373 ((103/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(21910216643/12500000000000),(-2961213049/100000000000000),(32509539/100000000000000),(-1127/390625000000)⟩
def e374 : ℝ := (587/25000000000000)
theorem h374 : Model (fun x => f374 ((103/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (28040738291442801/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(771766717743/3125000000000),(159518667017/50000000000000),(-921738629/100000000000000),(2933491/100000000000000)⟩
def e375 : ℝ := (175683/25000000000000)
theorem h375 : Model (fun x => f375 ((103/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(78013476092067/25000000000000),(81682168453/5000000000000),(-528455511/25000000000000),(273513/10000000000000)⟩
def e376 : ℝ := (23/400000000000)
theorem h376 : Model (fun x => f376 ((103/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(39058387856009/100000000000000),(-4984434317/4000000000000),(558793089/100000000000000),(-1252899/50000000000000)⟩
def e377 : ℝ := (5729/50000000000000)
theorem h377 : Model (fun x => f377 ((103/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (127604536109071/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(121883224287977/100000000000000),(249221715849/100000000000000),(-1117586179/100000000000000),(1002319/20000000000000)⟩
def e378 : ℝ := (47211/50000000000000)
theorem h378 : Model (fun x => f378 ((103/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(21883224287977/100000000000000),(249221715849/100000000000000),(-1117586179/100000000000000),(1002319/20000000000000)⟩
def e379 : ℝ := (47211/50000000000000)
theorem h379 : Model (fun x => f379 ((103/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(3514118259791/781250000000),(91974680849/10000000000000),(-824885037/20000000000000),(4623793/25000000000000)⟩
def e380 : ℝ := (21779/6250000000000)
theorem h380 : Model (fun x => f380 ((103/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2805521422967533/100000000000000),(91974680849/10000000000000),(-824885037/20000000000000),(4623793/25000000000000)⟩
def e381 : ℝ := (69693/20000000000000)
theorem h381 : Model (fun x => f381 ((103/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1709729984201381/50000000000000),(253530802947/3125000000000),(-17044446647/50000000000000),(35646489/25000000000000)⟩
def e382 : ℝ := (3214193/100000000000000)
theorem h382 : Model (fun x => f382 ((103/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4350920460391857/50000000000000),(253530802947/3125000000000),(-17044446647/50000000000000),(35646489/25000000000000)⟩
def e383 : ℝ := (1607097/50000000000000)
theorem h383 : Model (fun x => f383 ((103/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(10606084286661777/100000000000000),(31575245803467/100000000000000),(-118579891567/100000000000000),(434262853/100000000000000)⟩
def e384 : ℝ := (830999/6250000000000)
theorem h384 : Model (fun x => f384 ((103/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3968782976427349/25000000000000),(31575245803467/100000000000000),(-118579891567/100000000000000),(434262853/100000000000000)⟩
def e385 : ℝ := (2659197/20000000000000)
theorem h385 : Model (fun x => f385 ((103/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(967456131332399/5000000000000),(3902460189541/5000000000000),(-243254905901/100000000000000),(33824173/5000000000000)⟩
def e386 : ℝ := (17629579/50000000000000)
theorem h386 : Model (fun x => f386 ((103/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(4336967382472453/20000000000000),(3902460189541/5000000000000),(-243254905901/100000000000000),(33824173/5000000000000)⟩
def e387 : ℝ := (35259159/100000000000000)
theorem h387 : Model (fun x => f387 ((103/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(1057207136415061/4000000000000),(149172208743391/100000000000000),(-344318097929/100000000000000),(43276489/10000000000000)⟩
def e388 : ℝ := (35974139/50000000000000)
theorem h388 : Model (fun x => f388 ((103/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(26832559362757477/100000000000000),(149172208743391/100000000000000),(-344318097929/100000000000000),(43276489/10000000000000)⟩
def e389 : ℝ := (71948279/100000000000000)
theorem h389 : Model (fun x => f389 ((103/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(32704388510314267/100000000000000),(124344231304051/50000000000000),(-347773436273/100000000000000),(-130607291/20000000000000)⟩
def e390 : ℝ := (25154927/20000000000000)
theorem h390 : Model (fun x => f390 ((103/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(32686769462695219/100000000000000),(124344231304051/50000000000000),(-347773436273/100000000000000),(-130607291/20000000000000)⟩
def e391 : ℝ := (31443659/25000000000000)
theorem h391 : Model (fun x => f391 ((103/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(9959922134177697/25000000000000),(38457204436949/10000000000000),(-169394641593/100000000000000),(-700962049/25000000000000)⟩
def e392 : ℝ := (99722141/50000000000000)
theorem h392 : Model (fun x => f392 ((103/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(39843021870044121/100000000000000),(38457204436949/10000000000000),(-169394641593/100000000000000),(-700962049/25000000000000)⟩
def e393 : ℝ := (199444283/100000000000000)
theorem h393 : Model (fun x => f393 ((103/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(4359468919464741/50000000000000),(3669084515377/2000000000000),(238043966293/50000000000000),(-3336893747/100000000000000)⟩
def e394 : ℝ := (48164757/50000000000000)
theorem h394 : Model (fun x => f394 ((103/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(148555203628333/100000000000000),(121503785161/20000000000000),(-1051592751/50000000000000),(1661513/25000000000000)⟩
def e395 : ℝ := (10729/4000000000000)
theorem h395 : Model (fun x => f395 ((103/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(221883224287977/100000000000000),(249221715849/100000000000000),(-1117586179/100000000000000),(1002319/20000000000000)⟩
def e396 : ℝ := (47211/50000000000000)
theorem h396 : Model (fun x => f396 ((103/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(492321652204287/100000000000000),(1105962357503/100000000000000),(-216917893/5000000000000),(8334621/50000000000000)⟩
def e397 : ℝ := (457069/100000000000000)
theorem h397 : Model (fun x => f397 ((103/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(136547394472339/12500000000000),(1840458703679/50000000000000),(-12371908679/100000000000000),(19243603/50000000000000)⟩
def e398 : ℝ := (813537/50000000000000)
theorem h398 : Model (fun x => f398 ((103/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2423806092291589/100000000000000),(10889784302431/100000000000000),(-30485822829/100000000000000),(13634273/20000000000000)⟩
def e399 : ℝ := (1267231/25000000000000)
theorem h399 : Model (fun x => f399 ((103/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(360069007595971/10000000000000),(3862802747581/12500000000000),(-6021582779/20000000000000),(-30375997/20000000000000)⟩
def e400 : ℝ := (3968533/25000000000000)
theorem h400 : Model (fun x => f400 ((103/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(121883224287977/12500000000000),(249221715849/12500000000000),(-1117586179/12500000000000),(1002319/2500000000000)⟩
def e401 : ℝ := (47211/6250000000000)
theorem h401 : Model (fun x => f401 ((103/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1123620997932149/100000000000000),(2601292652597/100000000000000),(-5521937467/50000000000000),(11684703/25000000000000)⟩
def e402 : ℝ := (1023601/100000000000000)
theorem h402 : Model (fun x => f402 ((103/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1223620997932149/100000000000000),(2601292652597/100000000000000),(-5521937467/50000000000000),(11684703/25000000000000)⟩
def e403 : ℝ := (1023601/100000000000000)
theorem h403 : Model (fun x => f403 ((103/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(44058799839902057/100000000000000),(235896505306769/50000000000000),(2362497953/6250000000000),(-437153541/10000000000000)⟩
def e404 : ℝ := (245647669/100000000000000)
theorem h404 : Model (fun x => f404 ((103/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(113484707213/50000000000000),(-607611781/25000000000000),(3228891/12500000000000),(-126001/50000000000000)⟩
def e405 : ℝ := (47/1250000000000)
theorem h405 : Model (fun x => f405 ((103/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (2724185275758637/6250000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(3957864431437/20000000000000),(204475808017/100000000000000),(-35186999/3125000000000),(1567901/25000000000000)⟩
def e406 : ℝ := (816053/100000000000000)
theorem h406 : Model (fun x => f406 ((103/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(44485857124961/100000000000000),(523513142051/100000000000000),(-2047722597/100000000000000),(1841019/20000000000000)⟩
def e407 : ℝ := (303757/20000000000000)
theorem h407 : Model (fun x => f407 ((103/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(146013419682817/50000000000000),(405205692891/10000000000000),(-1814423731/100000000000000),(6458901/6250000000000)⟩
def e408 : ℝ := (11301621/100000000000000)
theorem h408 : Model (fun x => f408 ((103/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(708803008169/625000000000),(472561124749/100000000000000),(-2646301331/50000000000000),(22879367/25000000000000)⟩
def e409 : ℝ := (7364243/100000000000000)
theorem h409 : Model (fun x => f409 ((103/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-464722959333/50000000000000),(16898068749/20000000000000),(-119205719/100000000000000),(-4909147/100000000000000)⟩
def e410 : ℝ := (10061709/20000000000000)
theorem h410 : Model (fun x => f410 ((103/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(15717554670898437/100000000000000),(180075860595703/25000000000000),(1347343/10240000),(12257/10240000)⟩
def e411 : ℝ := (542968751/100000000000000)
theorem h411 : Model (fun x => f411 ((103/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(49729/1600),(223/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((103/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(11089567/64000),(149187/64000),(669/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((103/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(2723451181235799489/100000000000000),(6457942570826349/4000000000000),(4123243062256041/100000000000000),(14796645353729/25000000000000)⟩
def e414 : ℝ := (524625870829/100000000000000)
theorem h414 : Model (fun x => f414 ((103/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(917952933/25000000000000),(-108834103/50000000000000),(7344521/100000000000000),(-92821/50000000000000)⟩
def e415 : ℝ := (5851/100000000000000)
theorem h415 : Model (fun x => f415 ((103/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (1278909831347799489/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5563281022217/100000000000000),(-14877704887/100000000000000),(-107699437/50000000000000),(2603647/50000000000000)⟩
def e416 : ℝ := (16915739/100000000000000)
theorem h416 : Model (fun x => f416 ((103/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(4633835103551/100000000000000),(34806319429/50000000000000),(-334604593/100000000000000),(298147/100000000000000)⟩
def e417 : ℝ := (16806071/25000000000000)
theorem h417 : Model (fun x => f417 ((103/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((103/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((1737621129151/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (51/20) (13/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (51/20) (13/5) ≤ (434417886841/187500000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(103/40)-(1/40)) (by norm_num : ((103/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel31


noncomputable section
namespace Hf4Quad.Panel32
open Hf4Quad.Dag

def p0 : Cubic := ⟨(21/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((21/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((21/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((21/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((21/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(23/5),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((21/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-23/5),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((21/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-368571428571429/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((21/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((21/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(441/64),(21/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((21/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(417083333333333/50000000000000),(1986111111111/12500000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((21/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-417083333333333/50000000000000),(-1986111111111/12500000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((21/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-240547619047619/20000000000000),(-253373015873/1250000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((21/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((21/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(9261/512),(1323/2560),(63/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((21/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1804523/10240),(257789/51200),(2397591145833/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((21/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1804523/10240),(-257789/51200),(-2397591145833/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((21/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-3765006603422619/20000000000000),(-13094099547371/2500000000000),(-4870843667327/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((21/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((21/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(194481/4096),(9261/5120),(1323/51200),(21/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((21/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(33957/256),(1617/320),(231/3200),(45833333333/100000000000000)⟩
def e19 : ℝ := (21825397/20000000000000)
theorem h19 : Model (fun x => f19 ((21/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1112115978422619/20000000000000),(-461287047371/2500000000000),(2347906332673/100000000000000),(3826316551/12500000000000)⟩
def e20 : ℝ := (109126991/100000000000000)
theorem h20 : Model (fun x => f20 ((21/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((21/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(6231843566894531/50000000000000),(148377227783203/25000000000000),(9261/81920),(441/409600)⟩
def e22 : ℝ := (128417969/25000000000000)
theorem h22 : Model (fun x => f22 ((21/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(81198613586425777/100000000000000),(966650161743163/25000000000000),(18412384033203/25000000000000),(140284830729/20000000000000)⟩
def e23 : ℝ := (104577411/3125000000000)
theorem h23 : Model (fun x => f23 ((21/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(37819016847156341/50000000000000),(962037291269453/25000000000000),(15199488493097/20000000000000),(732034686053/100000000000000)⟩
def e24 : ℝ := (3455604143/100000000000000)
theorem h24 : Model (fun x => f24 ((21/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((21/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(32717178726196287/100000000000000),(934776535034179/50000000000000),(556414604187/1250000000000),(565246582031/100000000000000)⟩
def e26 : ℝ := (126652527/3125000000000)
theorem h26 : Model (fun x => f26 ((21/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(14693302276611327/20000000000000),(419808636474609/10000000000000),(99954437255857/100000000000000),(1269262695311/100000000000000)⟩
def e27 : ℝ := (1820150941/20000000000000)
theorem h27 : Model (fun x => f27 ((21/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(149104545077369317/100000000000000),(4023117764911951/50000000000000),(87975939860671/50000000000000),(500324345341/25000000000000)⟩
def e28 : ℝ := (196193107/1562500000000)
theorem h28 : Model (fun x => f28 ((21/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((21/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(85882594156265253/100000000000000),(2862753138542173/50000000000000),(81792946815489/50000000000000),(519320297241/20000000000000)⟩
def e30 : ℝ := (24871298843/100000000000000)
theorem h30 : Model (fun x => f30 ((21/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(2038007591485977/10000000000000),(1358671727657317/100000000000000),(38819192218779/100000000000000),(308088827133/50000000000000)⟩
def e31 : ℝ := (1180399739/20000000000000)
theorem h31 : Model (fun x => f31 ((21/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(169484620992229087/100000000000000),(9404907257481219/100000000000000),(214771071940121/100000000000000),(261747503563/10000000000000)⟩
def e32 : ℝ := (18458357543/100000000000000)
theorem h32 : Model (fun x => f32 ((21/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((21/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(945945/64),(9009/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((21/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((21/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(46389/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((21/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1688169/64),(62717/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((21/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((21/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1834089/64),(62717/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((21/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1834089/64),(-62717/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((21/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((21/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(29/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((21/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(841/64),(29/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((21/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((21/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(88305/32),(609/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((21/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(4529754827/12500000000000),(-62479377/12500000000000),(5170707/100000000000000),(-47547/100000000000000)⟩
def e46 : ℝ := (21/5000000000000)
theorem h46 : Model (fun x => f46 ((21/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (217707/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1038496687612201/100000000000000),(119460586071/100000000000000),(-417964569/50000000000000),(5855963/100000000000000)⟩
def e47 : ℝ := (23970703/100000000000000)
theorem h47 : Model (fun x => f47 ((21/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((21/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(37/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((21/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((21/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((21/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(30833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((21/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(50833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((21/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((21/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(31770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((21/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((21/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(667187499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((21/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((21/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((21/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(72278645833329/10000000000000),(13489583333311/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (33/25000000000000)
theorem h60 : Model (fun x => f60 ((21/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(161501736111107/100000000000000),(66189236111/6250000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((21/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((21/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(31770833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((21/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1432335069444427/100000000000000),(1306423611109/25000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((21/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1532335069444427/100000000000000),(1306423611109/25000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((21/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(11075510378236333/100000000000000),(244476227936513/100000000000000),(638068305117/50000000000000),(1069697627/50000000000000)⟩
def e66 : ℝ := (635373/100000000000000)
theorem h66 : Model (fun x => f66 ((21/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(56770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((21/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(515668402777771/100000000000000),(473090277777/25000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((21/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(585498498987257/50000000000000),(6445855034711/100000000000000),(739203559/6250000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (69/100000000000000)
theorem h69 : Model (fun x => f69 ((21/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(162117367549379/125000000000),(3576720633233383/100000000000000),(4001504214163/12500000000000),(137026181611/100000000000000)⟩
def e70 : ℝ := (314353727/100000000000000)
theorem h70 : Model (fun x => f70 ((21/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((21/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3391536458333247/12500000000000),(1389973958331/781250000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((21/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(3674164496527503/50000000000000),(161236979166399/100000000000000),(102539062499/12500000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (33/2000000000000)
theorem h73 : Model (fun x => f73 ((21/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(86048711909964953/100000000000000),(2361742820029289/100000000000000),(5217010609857/25000000000000),(8670849581/10000000000000)⟩
def e74 : ℝ := (187246839/100000000000000)
theorem h74 : Model (fun x => f74 ((21/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(215742605949468153/100000000000000),(371153965828917/6250000000000),(13220019038183/25000000000000),(223734677421/100000000000000)⟩
def e75 : ℝ := (250800283/50000000000000)
theorem h75 : Model (fun x => f75 ((21/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((21/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1130512152777749/12500000000000),(463324652777/781250000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((21/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(7335069444443/100000000000000),(56423611111/25000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((21/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1986581307869/100000000000000),(18337673611/20000000000000),(1410590277/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((21/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(179668344882161/100000000000000),(1894107645911/20000000000000),(183882850607/100000000000000),(394982853/25000000000000)⟩
def e80 : ℝ := (346/6103515625)
theorem h80 : Model (fun x => f80 ((21/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(203998433251619/50000000000000),(4450926399991/20000000000000),(457027882543/100000000000000),(2176969729/50000000000000)⟩
def e81 : ℝ := (19479723/100000000000000)
theorem h81 : Model (fun x => f81 ((21/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(216150602815971391/100000000000000),(5960718085262627/100000000000000),(2133484161411/4000000000000),(228088616879/100000000000000)⟩
def e82 : ℝ := (521080289/100000000000000)
theorem h82 : Model (fun x => f82 ((21/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(538032437547/100000000000000),(2069355529/6250000000000),(764069733/100000000000000),(1959153/25000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((21/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(72858559251/50000000000000),(2241801823/20000000000000),(344892587/100000000000000),(5306039/100000000000000)⟩
def e84 : ℝ := (8189/20000000000000)
theorem h84 : Model (fun x => f84 ((21/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(39465052927/100000000000000),(1821463981/50000000000000),(140112613/100000000000000),(359263/12500000000000)⟩
def e85 : ℝ := (33371/100000000000000)
theorem h85 : Model (fun x => f85 ((21/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(5344225917/50000000000000),(1151064043/100000000000000),(3320377/6250000000000),(272441/20000000000000)⟩
def e86 : ℝ := (4231/20000000000000)
theorem h86 : Model (fun x => f86 ((21/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(16032677751/50000000000000),(3453192129/100000000000000),(9961131/6250000000000),(817323/20000000000000)⟩
def e87 : ℝ := (12693/20000000000000)
theorem h87 : Model (fun x => f87 ((21/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-16032677751/50000000000000),(-3453192129/100000000000000),(-9961131/6250000000000),(-817323/20000000000000)⟩
def e88 : ℝ := (12693/20000000000000)
theorem h88 : Model (fun x => f88 ((21/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(216150570750615889/100000000000000),(2980357316035249/50000000000000),(53336944657179/100000000000000),(28510566283/12500000000000)⟩
def e89 : ℝ := (260571877/50000000000000)
theorem h89 : Model (fun x => f89 ((21/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3391536458333247/10000000000000),(1389973958331/625000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((21/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(166196188514611/6250000000000),(156132933063/800000000000),(53715458621/100000000000000),(32853491/50000000000000)⟩
def e91 : ℝ := (30347/100000000000000)
theorem h91 : Model (fun x => f91 ((21/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(36074267685333021/4000000000000),(6266473030002921/50000000000000),(35658356745367/50000000000000),(1064500179/500000000000)⟩
def e92 : ℝ := (352634159/100000000000000)
theorem h92 : Model (fun x => f92 ((21/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(693014761/6250000000000),(-4815353/3125000000000),(316137/25000000000000),(-4003/50000000000000)⟩
def e93 : ℝ := (7/12500000000000)
theorem h93 : Model (fun x => f93 ((21/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (88925221610715899/10000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(119836428903/500000000000),(819672251/250000000000),(-134372079/25000000000000),(234809/20000000000000)⟩
def e94 : ℝ := (42327/12500000000000)
theorem h94 : Model (fun x => f94 ((21/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(30833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((21/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(19672131147541/50000000000000),(-8062348831/6250000000000),(422942889/100000000000000),(-693349/50000000000000)⟩
def e96 : ℝ := (1141/25000000000000)
theorem h96 : Model (fun x => f96 ((21/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (126666666666663/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(60655737704917/50000000000000),(64498790647/25000000000000),(-845885781/100000000000000),(554679/20000000000000)⟩
def e97 : ℝ := (9317/25000000000000)
theorem h97 : Model (fun x => f97 ((21/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1273770491803257/50000000000000),(1354474603587/25000000000000),(-17763601401/100000000000000),(11648259/20000000000000)⟩
def e98 : ℝ := (195657/25000000000000)
theorem h98 : Model (fun x => f98 ((21/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(10655737704917/50000000000000),(64498790647/25000000000000),(-845885781/100000000000000),(554679/20000000000000)⟩
def e99 : ℝ := (9317/25000000000000)
theorem h99 : Model (fun x => f99 ((21/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(108583714055349/20000000000000),(1545433318191/20000000000000),(-2839264167/25000000000000),(-2148253/25000000000000)⟩
def e100 : ℝ := (393007/25000000000000)
theorem h100 : Model (fun x => f100 ((21/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(147164740661107/100000000000000),(625955476443/100000000000000),(-346674501/25000000000000),(2364203/100000000000000)⟩
def e101 : ℝ := (112129/100000000000000)
theorem h101 : Model (fun x => f101 ((21/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(60655737704917/5000000000000),(64498790647/2500000000000),(-845885781/10000000000000),(554679/2000000000000)⟩
def e102 : ℝ := (9317/2500000000000)
theorem h102 : Model (fun x => f102 ((21/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1360279494759447/100000000000000),(3205907102323/100000000000000),(-4922777907/50000000000000),(30098153/100000000000000)⟩
def e103 : ℝ := (484809/100000000000000)
theorem h103 : Model (fun x => f103 ((21/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1460279494759447/100000000000000),(3205907102323/100000000000000),(-4922777907/50000000000000),(30098153/100000000000000)⟩
def e104 : ℝ := (484809/100000000000000)
theorem h104 : Model (fun x => f104 ((21/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1585625710998493/20000000000000),(130243694257951/100000000000000),(5685532391/20000000000000),(-1086952717/100000000000000)⟩
def e105 : ℝ := (28847183/100000000000000)
theorem h105 : Model (fun x => f105 ((21/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(110655737704917/50000000000000),(64498790647/25000000000000),(-845885781/100000000000000),(554679/20000000000000)⟩
def e106 : ℝ := (9317/25000000000000)
theorem h106 : Model (fun x => f106 ((21/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(19591507659231/4000000000000),(1141945801619/100000000000000),(-1539234783/50000000000000),(7910993/100000000000000)⟩
def e107 : ℝ := (37333/20000000000000)
theorem h107 : Model (fun x => f107 ((21/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(270989091597967/25000000000000),(758177130583/20000000000000),(-8009885929/100000000000000),(6744911/50000000000000)⟩
def e108 : ℝ := (42177/6250000000000)
theorem h108 : Model (fun x => f108 ((21/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(85937454207572433/100000000000000),(856165551834443/50000000000000),(4610498917469/100000000000000),(-20067313927/100000000000000)⟩
def e109 : ℝ := (24635687/6250000000000)
theorem h109 : Model (fun x => f109 ((21/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(3090459553883247/12500000000000),(13145065005303/12500000000000),(-7280164521/3125000000000),(49648263/12500000000000)⟩
def e110 : ℝ := (2354709/12500000000000)
theorem h110 : Model (fun x => f110 ((21/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(5268980223013549/100000000000000),(43098573787877/50000000000000),(391458003/3125000000000),(-28809823/4000000000000)⟩
def e111 : ℝ := (300599/1562500000000)
theorem h111 : Model (fun x => f111 ((21/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(1784795205352619/3125000000000),(141760060515591/12500000000000),(1490689740717/50000000000000),(-13525793697/100000000000000)⟩
def e112 : ℝ := (262143251/100000000000000)
theorem h112 : Model (fun x => f112 ((21/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(143050900778856241/100000000000000),(1423205793896807/50000000000000),(7591878398903/100000000000000),(-4199138453/12500000000000)⟩
def e113 : ℝ := (656314243/100000000000000)
theorem h113 : Model (fun x => f113 ((21/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(1030153184627749/12500000000000),(4381688335101/12500000000000),(-2426721507/3125000000000),(16549421/12500000000000)⟩
def e114 : ℝ := (784903/12500000000000)
theorem h114 : Model (fun x => f114 ((21/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(4541789841439/100000000000000),(109965151267/100000000000000),(152536779/50000000000000),(-3182587/100000000000000)⟩
def e115 : ℝ := (37593/100000000000000)
theorem h115 : Model (fun x => f115 ((21/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(120990303153/12500000000000),(35152794257/100000000000000),(77575523/25000000000000),(-3477/500000000000)⟩
def e116 : ℝ := (17623/100000000000000)
theorem h116 : Model (fun x => f116 ((21/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(79768669505369/100000000000000),(3236311788183/100000000000000),(37143341131/100000000000000),(25445833/100000000000000)⟩
def e117 : ℝ := (1960689/100000000000000)
theorem h117 : Model (fun x => f117 ((21/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(88268609698563/50000000000000),(3684064337937/50000000000000),(898772523/1000000000000),(12697937/10000000000000)⟩
def e118 : ℝ := (4534857/100000000000000)
theorem h118 : Model (fun x => f118 ((21/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(143227437998253367/100000000000000),(178361232279343/6250000000000),(7681755651203/100000000000000),(-16733064127/50000000000000)⟩
def e119 : ℝ := (6608491/1000000000000)
theorem h119 : Model (fun x => f119 ((21/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(206278549637/100000000000000),(4994386069/50000000000000),(2322421/1562500000000),(11933/3125000000000)⟩
def e120 : ℝ := (7637/100000000000000)
theorem h120 : Model (fun x => f120 ((21/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(43961002381/100000000000000),(2660943397/100000000000000),(55701967/100000000000000),(386077/100000000000000)⟩
def e121 : ℝ := (217/12500000000000)
theorem h121 : Model (fun x => f121 ((21/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2342184553/25000000000000),(680503557/100000000000000),(4591039/25000000000000),(204697/100000000000000)⟩
def e122 : ℝ := (199/20000000000000)
theorem h122 : Model (fun x => f122 ((21/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(99830817/5000000000000),(169196239/100000000000000),(559009/10000000000000),(42753/50000000000000)⟩
def e123 : ℝ := (613/100000000000000)
theorem h123 : Model (fun x => f123 ((21/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(299492451/5000000000000),(507588717/100000000000000),(1677027/10000000000000),(128259/50000000000000)⟩
def e124 : ℝ := (1839/100000000000000)
theorem h124 : Model (fun x => f124 ((21/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-299492451/5000000000000),(-507588717/100000000000000),(-1677027/10000000000000),(-128259/50000000000000)⟩
def e125 : ℝ := (1839/100000000000000)
theorem h125 : Model (fun x => f125 ((21/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(143227432008404347/100000000000000),(2853779208880771/100000000000000),(7681738880933/100000000000000),(-8366596193/25000000000000)⟩
def e126 : ℝ := (660850939/100000000000000)
theorem h126 : Model (fun x => f126 ((21/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(3090459553883247/10000000000000),(13145065005303/10000000000000),(-7280164521/2500000000000),(49648263/10000000000000)⟩
def e127 : ℝ := (2354709/10000000000000)
theorem h127 : Model (fun x => f127 ((21/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2398919827260669/100000000000000),(11186219959421/100000000000000),(-171155279/1000000000000),(3592617/50000000000000)⟩
def e128 : ℝ := (421729/20000000000000)
theorem h128 : Model (fun x => f128 ((21/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(741376469915768307/100000000000000),(6610451741728383/100000000000000),(2429061775131/100000000000000),(-20471346799/50000000000000)⟩
def e129 : ℝ := (167111277/12500000000000)
theorem h129 : Model (fun x => f129 ((21/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(1348842377/10000000000000),(-120268957/100000000000000),(1028179/100000000000000),(-8029/100000000000000)⟩
def e130 : ℝ := (89/100000000000000)
theorem h130 : Model (fun x => f130 ((21/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (734763546832680979/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(9659561492091/50000000000000),(212671694539/100000000000000),(-923430619/100000000000000),(255587/6250000000000)⟩
def e131 : ℝ := (41353/12500000000000)
theorem h131 : Model (fun x => f131 ((21/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(21643204382391/50000000000000),(540540594939/100000000000000),(-292183787/20000000000000),(5263437/100000000000000)⟩
def e132 : ℝ := (523/78125000000)
theorem h132 : Model (fun x => f132 ((21/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-449527921208539/100000000000000),(-2780892988021/50000000000000),(15455484007/100000000000000),(-29194771/50000000000000)⟩
def e133 : ℝ := (273581/1562500000000)
theorem h133 : Model (fun x => f133 ((21/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(19047619047619/50000000000000),(-45351473923/12500000000000),(1727675197/50000000000000),(-32908099/100000000000000)⟩
def e134 : ℝ := (158213/50000000000000)
theorem h134 : Model (fun x => f134 ((21/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (13/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-171248731888967/100000000000000),(-487835306213/100000000000000),(10533853967/100000000000000),(-61283027/50000000000000)⟩
def e135 : ℝ := (537883/5000000000000)
theorem h135 : Model (fun x => f135 ((21/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(972405/2048),(9261/512),(1323/5120),(21/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((21/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((21/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(83349/256),(11907/1280),(567/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((21/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(1639197/2048),(70119/2560),(8883/25600),(123/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((21/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-441/64),(-21/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((21/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(1625085/2048),(69783/2560),(8867/25600),(123/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((21/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((21/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(63/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((21/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-63/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((21/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(1592829/2048),(69399/2560),(8867/25600),(123/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((21/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(1598973/2048),(69399/2560),(8867/25600),(123/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((21/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((21/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(1598973/32),(69399/40),(8867/400),(123/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((21/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((21/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(183784545/4096),(1750329/1024),(250047/10240),(3969/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((21/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(2228696651/100000000000000),(-8490273/10000000000000),(2021493/100000000000000),(-7701/20000000000000)⟩
def e151 : ℝ := (723/100000000000000)
theorem h151 : Model (fun x => f151 ((21/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (11042660853/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(13920413164607/12500000000000),(-375678680941/100000000000000),(1555145869/50000000000000),(-3090749/12500000000000)⟩
def e152 : ℝ := (71022671/100000000000000)
theorem h152 : Model (fun x => f152 ((21/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(45/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((21/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1665/64),(41/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((21/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(87/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((21/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(183908045977/4000000000000),(-3170828379/10000000000000),(218677819/100000000000000),(-1508123/100000000000000)⟩
def e156 : ℝ := (419/4000000000000)
theorem h156 : Model (fun x => f156 ((21/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (108/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(119612068965509/100000000000000),(70650019813/20000000000000),(27334727/6250000000000),(-3016249/100000000000000)⟩
def e157 : ℝ := (525933/100000000000000)
theorem h157 : Model (fun x => f157 ((21/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(219612068965509/100000000000000),(70650019813/20000000000000),(27334727/6250000000000),(-3016249/100000000000000)⟩
def e158 : ℝ := (525933/100000000000000)
theorem h158 : Model (fun x => f158 ((21/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(54903017241377/50000000000000),(44156262383/25000000000000),(27334727/12500000000000),(-2413/160000000000)⟩
def e159 : ℝ := (32871/12500000000000)
theorem h159 : Model (fun x => f159 ((21/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(4903017241377/50000000000000),(44156262383/25000000000000),(27334727/12500000000000),(-2413/160000000000)⟩
def e160 : ℝ := (32871/12500000000000)
theorem h160 : Model (fun x => f160 ((21/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((21/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((21/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(405236555829211/100000000000000),(651830539939/100000000000000),(807025273/100000000000000),(-55657/1000000000000)⟩
def e163 : ℝ := (970479/100000000000000)
theorem h163 : Model (fun x => f163 ((21/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(345118855192937/12500000000000),(651830539939/100000000000000),(807025273/100000000000000),(-55657/1000000000000)⟩
def e164 : ℝ := (12131/1250000000000)
theorem h164 : Model (fun x => f164 ((21/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((21/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(3031690633117137/100000000000000),(1398070014721/25000000000000),(1009380683/12500000000000),(-44899247/100000000000000)⟩
def e166 : ℝ := (8347419/100000000000000)
theorem h166 : Model (fun x => f166 ((21/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8314071585498089/100000000000000),(1398070014721/25000000000000),(1009380683/12500000000000),(-44899247/100000000000000)⟩
def e167 : ℝ := (417371/5000000000000)
theorem h167 : Model (fun x => f167 ((21/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((21/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(9129352312092883/100000000000000),(10412697012921/50000000000000),(18462642397/50000000000000),(-74098523/50000000000000)⟩
def e169 : ℝ := (15602507/50000000000000)
theorem h169 : Model (fun x => f169 ((21/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(7199199965570251/50000000000000),(10412697012921/50000000000000),(18462642397/50000000000000),(-74098523/50000000000000)⟩
def e170 : ℝ := (6241003/20000000000000)
theorem h170 : Model (fun x => f170 ((21/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((21/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15810311993352967/100000000000000),(48298720355377/100000000000000),(4352606399/4000000000000),(-5382307/2000000000000)⟩
def e172 : ℝ := (36367093/50000000000000)
theorem h172 : Model (fun x => f172 ((21/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(4536506569766813/25000000000000),(48298720355377/100000000000000),(4352606399/4000000000000),(-5382307/2000000000000)⟩
def e173 : ℝ := (72734187/100000000000000)
theorem h173 : Model (fun x => f173 ((21/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((21/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(19925431873242189/100000000000000),(42542668715823/50000000000000),(244474584793/100000000000000),(-67839059/25000000000000)⟩
def e175 : ℝ := (503159/390625000000)
theorem h175 : Model (fun x => f175 ((21/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(20327812825623141/100000000000000),(42542668715823/50000000000000),(244474584793/100000000000000),(-67839059/25000000000000)⟩
def e176 : ℝ := (25761741/20000000000000)
theorem h176 : Model (fun x => f176 ((21/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((21/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(5580291290223359/25000000000000),(129332844431989/100000000000000),(46318228339/10000000000000),(3332941/25000000000000)⟩
def e178 : ℝ := (196579709/100000000000000)
theorem h178 : Model (fun x => f178 ((21/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(5575886528318597/25000000000000),(129332844431989/100000000000000),(46318228339/10000000000000),(3332941/25000000000000)⟩
def e179 : ℝ := (19657971/10000000000000)
theorem h179 : Model (fun x => f179 ((21/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((21/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(12245319768009507/50000000000000),(181408917124479/100000000000000),(785809205887/100000000000000),(779191903/100000000000000)⟩
def e181 : ℝ := (276117573/100000000000000)
theorem h181 : Model (fun x => f181 ((21/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(24493972869352347/100000000000000),(181408917124479/100000000000000),(785809205887/100000000000000),(779191903/100000000000000)⟩
def e182 : ℝ := (138058787/50000000000000)
theorem h182 : Model (fun x => f182 ((21/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(24018874257651/1000000000000),(12210302536173/20000000000000),(225516598173/50000000000000),(298329011/20000000000000)⟩
def e183 : ℝ := (92823839/100000000000000)
theorem h183 : Model (fun x => f183 ((21/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(120573652088277/100000000000000),(96972481397/25000000000000),(792206957/100000000000000),(-507909/20000000000000)⟩
def e184 : ℝ := (291649/50000000000000)
theorem h184 : Model (fun x => f184 ((21/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(104903017241377/50000000000000),(44156262383/25000000000000),(27334727/12500000000000),(-2413/160000000000)⟩
def e185 : ℝ := (32871/12500000000000)
theorem h185 : Model (fun x => f185 ((21/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(88037144210757/20000000000000),(185285006163/25000000000000),(1229562589/100000000000000),(-1111159/20000000000000)⟩
def e186 : ℝ := (554617/50000000000000)
theorem h186 : Model (fun x => f186 ((21/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(923536205702263/100000000000000),(233243474353/10000000000000),(2425661983/50000000000000),(-362563/2500000000000)⟩
def e187 : ℝ := (876759/25000000000000)
theorem h187 : Model (fun x => f187 ((21/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1937634690196407/100000000000000),(1304957024613/20000000000000),(8158801629/50000000000000),(-3835759/12500000000000)⟩
def e188 : ℝ := (9849217/100000000000000)
theorem h188 : Model (fun x => f188 ((21/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2336276910099179/100000000000000),(7691530735881/50000000000000),(60333791157/100000000000000),(14388859/50000000000000)⟩
def e189 : ℝ := (23410301/100000000000000)
theorem h189 : Model (fun x => f189 ((21/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((21/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(54903017241377/6250000000000),(44156262383/3125000000000),(27334727/1562500000000),(-2413/20000000000)⟩
def e191 : ℝ := (32871/1562500000000)
theorem h191 : Model (fun x => f191 ((21/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(999021927950309/100000000000000),(450222580461/25000000000000),(508325897/20000000000000),(-2920909/20000000000000)⟩
def e192 : ℝ := (1343521/50000000000000)
theorem h192 : Model (fun x => f192 ((21/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1099021927950309/100000000000000),(450222580461/25000000000000),(508325897/20000000000000),(-2920909/20000000000000)⟩
def e193 : ℝ := (1343521/50000000000000)
theorem h193 : Model (fun x => f193 ((21/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(1604762221226869/6250000000000),(13196062720637/6250000000000),(39979726513/4000000000000),(29051933/2000000000000)⟩
def e194 : ℝ := (321101243/100000000000000)
theorem h194 : Model (fun x => f194 ((21/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(194732899283/50000000000000),(-1601301127/50000000000000),(1117453/10000000000000),(1343/12500000000000)⟩
def e195 : ℝ := (2651/50000000000000)
theorem h195 : Model (fun x => f195 ((21/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (12732028634619497/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2338632510853/25000000000000),(160851860563/100000000000000),(69782549/100000000000000),(-777537/50000000000000)⟩
def e196 : ℝ := (100903/20000000000000)
theorem h196 : Model (fun x => f196 ((21/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(119612068965509/50000000000000),(70650019813/10000000000000),(27334727/3125000000000),(-3016249/50000000000000)⟩
def e197 : ℝ := (525933/50000000000000)
theorem h197 : Model (fun x => f197 ((21/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(45534838076547/100000000000000),(-36621817137/50000000000000),(6782873/25000000000000),(363809/50000000000000)⟩
def e198 : ℝ := (27909/25000000000000)
theorem h198 : Model (fun x => f198 ((21/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (21925837796863/10000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(13616290480863/12500000000000),(146487268547/100000000000000),(-27131493/50000000000000),(-1455237/100000000000000)⟩
def e199 : ℝ := (75739/10000000000000)
theorem h199 : Model (fun x => f199 ((21/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1116290480863/12500000000000),(146487268547/100000000000000),(-27131493/50000000000000),(-1455237/100000000000000)⟩
def e200 : ℝ := (75739/10000000000000)
theorem h200 : Model (fun x => f200 ((21/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(20100238328893/5000000000000),(27030388839/5000000000000),(-100128129/50000000000000),(-2685259/50000000000000)⟩
def e201 : ℝ := (2795131/100000000000000)
theorem h201 : Model (fun x => f201 ((21/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(551543810458429/20000000000000),(27030388839/5000000000000),(-100128129/50000000000000),(-2685259/50000000000000)⟩
def e202 : ℝ := (698783/25000000000000)
theorem h202 : Model (fun x => f202 ((21/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(600798458889921/20000000000000),(462859311589/10000000000000),(-57664933/6250000000000),(-46568171/100000000000000)⟩
def e203 : ℝ := (23955261/100000000000000)
theorem h203 : Model (fun x => f203 ((21/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8286373246830557/100000000000000),(462859311589/10000000000000),(-57664933/6250000000000),(-46568171/100000000000000)⟩
def e204 : ℝ := (11977631/50000000000000)
theorem h204 : Model (fun x => f204 ((21/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(9026373212935739/100000000000000),(3436084660317/20000000000000),(511533/40000000000),(-175176391/100000000000000)⟩
def e205 : ℝ := (89059991/100000000000000)
theorem h205 : Model (fun x => f205 ((21/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(7147710415991679/50000000000000),(3436084660317/20000000000000),(511533/40000000000),(-175176391/100000000000000)⟩
def e206 : ℝ := (11132499/12500000000000)
theorem h206 : Model (fun x => f206 ((21/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(62288192830229/400000000000),(9913915561189/25000000000000),(9401523499/50000000000000),(-101575437/25000000000000)⟩
def e207 : ℝ := (103026737/50000000000000)
theorem h207 : Model (fun x => f207 ((21/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(3581552498654307/20000000000000),(9913915561189/25000000000000),(9401523499/50000000000000),(-101575437/25000000000000)⟩
def e208 : ℝ := (8242139/4000000000000)
theorem h208 : Model (fun x => f208 ((21/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(19506983677655093/100000000000000),(17357408360281/25000000000000),(68855429779/100000000000000),(-697160473/100000000000000)⟩
def e209 : ℝ := (180935651/50000000000000)
theorem h209 : Model (fun x => f209 ((21/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(3981872926007209/20000000000000),(17357408360281/25000000000000),(68855429779/100000000000000),(-697160473/100000000000000)⟩
def e210 : ℝ := (361871303/100000000000000)
theorem h210 : Model (fun x => f210 ((21/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2710916920919903/12500000000000),(104794608984737/100000000000000),(41476650123/25000000000000),(-246489439/25000000000000)⟩
def e211 : ℝ := (109621083/20000000000000)
theorem h211 : Model (fun x => f211 ((21/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(1354357269983761/6250000000000),(104794608984737/100000000000000),(41476650123/25000000000000),(-246489439/25000000000000)⟩
def e212 : ℝ := (68513177/12500000000000)
theorem h212 : Model (fun x => f212 ((21/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(1180244608189919/5000000000000),(145896482479841/100000000000000),(20154670147/6250000000000),(-1203185343/100000000000000)⟩
def e213 : ℝ := (382918343/50000000000000)
theorem h213 : Model (fun x => f213 ((21/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(23608225497131713/100000000000000),(145896482479841/100000000000000),(20154670147/6250000000000),(-1203185343/100000000000000)⟩
def e214 : ℝ := (765836687/100000000000000)
theorem h214 : Model (fun x => f214 ((21/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(2108290991401223/100000000000000),(185984660351/390625000000),(1794588133/781250000000),(-14446839/25000000000000)⟩
def e215 : ℝ := (63373119/25000000000000)
theorem h215 : Model (fun x => f215 ((21/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(118658154533913/100000000000000),(63827622409/20000000000000),(19273501/20000000000000),(-1664683/50000000000000)⟩
def e216 : ℝ := (1656513/100000000000000)
theorem h216 : Model (fun x => f216 ((21/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(26116290480863/12500000000000),(146487268547/100000000000000),(-27131493/50000000000000),(-1455237/100000000000000)⟩
def e217 : ℝ := (75739/10000000000000)
theorem h217 : Model (fun x => f217 ((21/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(436518802227721/100000000000000),(612112649139/100000000000000),(-12158467/100000000000000),(-38999/625000000000)⟩
def e218 : ℝ := (3171293/100000000000000)
theorem h218 : Model (fun x => f218 ((21/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(912020147147003/100000000000000),(1918333410231/100000000000000),(634396239/100000000000000),(-19739263/100000000000000)⟩
def e219 : ℝ := (4979637/50000000000000)
theorem h219 : Model (fun x => f219 ((21/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1905486646983243/100000000000000),(1335993402153/25000000000000),(1820335483/50000000000000),(-54624997/100000000000000)⟩
def e220 : ℝ := (27801803/100000000000000)
theorem h220 : Model (fun x => f220 ((21/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2261015290200453/100000000000000),(1242219457321/10000000000000),(23210879403/100000000000000),(-13936127/12500000000000)⟩
def e221 : ℝ := (65079999/100000000000000)
theorem h221 : Model (fun x => f221 ((21/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(13616290480863/1562500000000),(146487268547/12500000000000),(-27131493/6250000000000),(-1455237/12500000000000)⟩
def e222 : ℝ := (75739/1250000000000)
theorem h222 : Model (fun x => f222 ((21/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(198020149061829/20000000000000),(1491036260421/100000000000000),(-337736383/100000000000000),(-7485631/50000000000000)⟩
def e223 : ℝ := (7715633/100000000000000)
theorem h223 : Model (fun x => f223 ((21/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(218020149061829/20000000000000),(1491036260421/100000000000000),(-337736383/100000000000000),(-7485631/50000000000000)⟩
def e224 : ℝ := (7715633/100000000000000)
theorem h224 : Model (fun x => f224 ((21/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(4929468906005773/20000000000000),(84563496728433/50000000000000),(430605123531/100000000000000),(-31242919/2500000000000)⟩
def e225 : ℝ := (889423657/100000000000000)
theorem h225 : Model (fun x => f225 ((21/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(10143080513/2500000000000),(-1392010981/50000000000000),(12015361/100000000000000),(-6619/50000000000000)⟩
def e226 : ℝ := (1511/10000000000000)
theorem h226 : Model (fun x => f226 ((21/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (24477784792308051/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(4276913054123/50000000000000),(13447795191/10000000000000),(-140236019/100000000000000),(-1187891/100000000000000)⟩
def e227 : ℝ := (1384303/100000000000000)
theorem h227 : Model (fun x => f227 ((21/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(8954178075829/50000000000000),(295329812473/100000000000000),(-7045347/10000000000000),(-548593/20000000000000)⟩
def e228 : ℝ := (944409/50000000000000)
theorem h228 : Model (fun x => f228 ((21/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(24929171673/125000000000),(261611164587/100000000000000),(-39434271/6250000000000),(983811/50000000000000)⟩
def e229 : ℝ := (118003/781250000000)
theorem h229 : Model (fun x => f229 ((21/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7597461843199/100000000000000),(27304616573/100000000000000),(-500405239/100000000000000),(2757667/50000000000000)⟩
def e230 : ℝ := (2994313/50000000000000)
theorem h230 : Model (fun x => f230 ((21/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-20456408755721/12500000000000),(-11513267241/2500000000000),(1254181091/12500000000000),(-731567/625000000000)⟩
def e231 : ℝ := (8373143/50000000000000)
theorem h231 : Model (fun x => f231 ((21/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((21/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2205/64),(-21/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((21/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(441/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((21/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1323/64),(-21/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((21/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((21/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2987/64),(-21/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((21/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((21/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(373375/32),(-525/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((21/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(567/64),(3/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((21/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(951/64),(3/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((21/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((21/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(179739/64),(567/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((21/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(1424287439/4000000000000),(-11232551/25000000000000),(1554367/100000000000000),(-963/25000000000000)⟩
def e244 : ℝ := (37/50000000000000)
theorem h244 : Model (fun x => f244 ((21/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (70119/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(207731766615869/50000000000000),(-211575625751/12500000000000),(-8207536143/100000000000000),(-60845961/100000000000000)⟩
def e245 : ℝ := (978441/50000000000000)
theorem h245 : Model (fun x => f245 ((21/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(189/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((21/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(3465/64),(93/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((21/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(4809/64),(93/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((21/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(1369/64),(37/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((21/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(6583521/4096),(30525/1024),(9971/51200),(13/25600)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((21/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((21/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(37845/32),(261/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((21/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(84555423437/100000000000000),(-1166281703/100000000000000),(12064983/100000000000000),(-110943/100000000000000)⟩
def e253 : ℝ := (489/50000000000000)
theorem h253 : Model (fun x => f253 ((21/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (93303/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(135906349087251/100000000000000),(322995253667/50000000000000),(546294333/50000000000000),(-2857777/100000000000000)⟩
def e254 : ℝ := (3200123/100000000000000)
theorem h254 : Model (fun x => f254 ((21/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(235906349087251/100000000000000),(322995253667/50000000000000),(546294333/50000000000000),(-2857777/100000000000000)⟩
def e255 : ℝ := (3200123/100000000000000)
theorem h255 : Model (fun x => f255 ((21/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(943625396349/800000000000),(322995253667/100000000000000),(546294333/100000000000000),(-1428889/100000000000000)⟩
def e256 : ℝ := (1600063/100000000000000)
theorem h256 : Model (fun x => f256 ((21/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(143625396349/800000000000),(322995253667/100000000000000),(546294333/100000000000000),(-1428889/100000000000000)⟩
def e257 : ℝ := (1600063/100000000000000)
theorem h257 : Model (fun x => f257 ((21/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(43530338224433/10000000000000),(596003146647/50000000000000),(504021557/25000000000000),(-5273281/100000000000000)⟩
def e258 : ℝ := (5904997/100000000000000)
theorem h258 : Model (fun x => f258 ((21/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(558203533591723/20000000000000),(596003146647/50000000000000),(504021557/25000000000000),(-5273281/100000000000000)⟩
def e259 : ℝ := (2952499/50000000000000)
theorem h259 : Model (fun x => f259 ((21/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3292093941430637/100000000000000),(10420863860213/100000000000000),(21475332811/100000000000000),(-16538411/50000000000000)⟩
def e260 : ℝ := (3230281/6250000000000)
theorem h260 : Model (fun x => f260 ((21/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8574474893811589/100000000000000),(10420863860213/100000000000000),(21475332811/100000000000000),(-16538411/50000000000000)⟩
def e261 : ℝ := (51684497/100000000000000)
theorem h261 : Model (fun x => f261 ((21/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(10113865337696887/100000000000000),(3998688667187/10000000000000),(105831602883/100000000000000),(-8810499/25000000000000)⟩
def e262 : ℝ := (198633723/100000000000000)
theorem h262 : Model (fun x => f262 ((21/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7691456478372253/50000000000000),(3998688667187/10000000000000),(105831602883/100000000000000),(-8810499/25000000000000)⟩
def e263 : ℝ := (49658431/25000000000000)
theorem h263 : Model (fun x => f263 ((21/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(283509908902543/1562500000000),(96851880956643/100000000000000),(338023463043/100000000000000),(59780669/20000000000000)⟩
def e264 : ℝ := (481824013/100000000000000)
theorem h264 : Model (fun x => f264 ((21/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(20480348455477037/100000000000000),(96851880956643/100000000000000),(338023463043/100000000000000),(59780669/20000000000000)⟩
def e265 : ℝ := (240912007/50000000000000)
theorem h265 : Model (fun x => f265 ((21/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(6039305290207859/25000000000000),(90195210819613/50000000000000),(823419366929/100000000000000),(210102577/12500000000000)⟩
def e266 : ℝ := (900570563/100000000000000)
theorem h266 : Model (fun x => f266 ((21/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(6139900528303097/25000000000000),(90195210819613/50000000000000),(823419366929/100000000000000),(210102577/12500000000000)⟩
def e267 : ℝ := (225142641/25000000000000)
theorem h267 : Model (fun x => f267 ((21/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(28968830347817221/100000000000000),(292102578041273/100000000000000),(105504343601/6250000000000),(1055343989/20000000000000)⟩
def e268 : ℝ := (1468386281/100000000000000)
theorem h268 : Model (fun x => f268 ((21/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(28951211300198173/100000000000000),(292102578041273/100000000000000),(105504343601/6250000000000),(1055343989/20000000000000)⟩
def e269 : ℝ := (734193141/50000000000000)
theorem h269 : Model (fun x => f269 ((21/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(6829774559483287/20000000000000),(87611060420439/20000000000000),(77319196263/2500000000000),(12858502199/100000000000000)⟩
def e270 : ℝ := (556698501/25000000000000)
theorem h270 : Model (fun x => f270 ((21/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(4269025766343721/12500000000000),(87611060420439/20000000000000),(77319196263/2500000000000),(12858502199/100000000000000)⟩
def e271 : ℝ := (445358801/20000000000000)
theorem h271 : Model (fun x => f271 ((21/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(6131405177152103/100000000000000),(94477418904451/50000000000000),(1078359705673/50000000000000),(14203076881/100000000000000)⟩
def e272 : ℝ := (253173859/25000000000000)
theorem h272 : Model (fun x => f272 ((21/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(34782378462297/25000000000000),(15239326213/2000000000000),(466400471/20000000000000),(158169/100000000000000)⟩
def e273 : ℝ := (3791269/100000000000000)
theorem h273 : Model (fun x => f273 ((21/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(1743625396349/800000000000),(322995253667/100000000000000),(546294333/100000000000000),(-1428889/100000000000000)⟩
def e274 : ℝ := (1600063/100000000000000)
theorem h274 : Model (fun x => f274 ((21/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(237517931468219/50000000000000),(21999325281/1562500000000),(3424591021/100000000000000),(-2699609/100000000000000)⟩
def e275 : ℝ := (1398279/20000000000000)
theorem h275 : Model (fun x => f275 ((21/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(1035355743490669/100000000000000),(9206059743/200000000000),(730336627/5000000000000),(1520309/25000000000000)⟩
def e276 : ℝ := (22894239/100000000000000)
theorem h276 : Model (fun x => f276 ((21/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(70518459711177/3125000000000),(13376599640169/100000000000000),(5235949503/10000000000000),(35392653/50000000000000)⟩
def e277 : ℝ := (66646867/100000000000000)
theorem h277 : Model (fun x => f277 ((21/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1569791842721537/50000000000000),(716105180683/2000000000000),(9095857687/4000000000000),(81295681/10000000000000)⟩
def e278 : ℝ := (90540339/50000000000000)
theorem h278 : Model (fun x => f278 ((21/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(943625396349/100000000000),(322995253667/12500000000000),(546294333/12500000000000),(-1428889/12500000000000)⟩
def e279 : ℝ := (1600063/12500000000000)
theorem h279 : Model (fun x => f279 ((21/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(270688727549547/25000000000000),(1672964169993/50000000000000),(6702357019/100000000000000),(-11272943/100000000000000)⟩
def e280 : ℝ := (16591773/100000000000000)
theorem h280 : Model (fun x => f280 ((21/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(295688727549547/25000000000000),(1672964169993/50000000000000),(6702357019/100000000000000),(-11272943/100000000000000)⟩
def e281 : ℝ := (16591773/100000000000000)
theorem h281 : Model (fun x => f281 ((21/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(37133580199359191/100000000000000),(264268339812203/50000000000000),(2048993501089/50000000000000),(19269681403/100000000000000)⟩
def e282 : ℝ := (2713137331/100000000000000)
theorem h282 : Model (fun x => f282 ((21/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(269298030147/100000000000000),(-3833023531/100000000000000),(12418863/50000000000000),(-70267/100000000000000)⟩
def e283 : ℝ := (20507/100000000000000)
theorem h283 : Model (fun x => f283 ((21/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (36600923549913873/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(16511753362401/100000000000000),(54766690573/20000000000000),(11027639/12500000000000),(-897613/50000000000000)⟩
def e284 : ℝ := (1051581/25000000000000)
theorem h284 : Model (fun x => f284 ((21/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(135906349087251/50000000000000),(322995253667/25000000000000),(546294333/25000000000000),(-2857777/50000000000000)⟩
def e285 : ℝ := (3200123/50000000000000)
theorem h285 : Model (fun x => f285 ((21/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(21194851343957/50000000000000),(-58038593813/50000000000000),(30383087/25000000000000),(718319/100000000000000)⟩
def e286 : ℝ := (29107/5000000000000)
theorem h286 : Model (fun x => f286 ((21/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (235259259933351/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(14402574328021/12500000000000),(928617501/400000000000),(-121532349/50000000000000),(-718321/50000000000000)⟩
def e287 : ℝ := (135279/3125000000000)
theorem h287 : Model (fun x => f287 ((21/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(1902574328021/12500000000000),(928617501/400000000000),(-121532349/50000000000000),(-718321/50000000000000)⟩
def e288 : ℝ := (135279/3125000000000)
theorem h288 : Model (fun x => f288 ((21/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(425218861113/100000000000),(1370816311/160000000000),(-897024481/100000000000000),(-2650947/50000000000000)⟩
def e289 : ℝ := (124811/781250000000)
theorem h289 : Model (fun x => f289 ((21/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(556186629365457/20000000000000),(1370816311/160000000000),(-897024481/100000000000000),(-2650947/50000000000000)⟩
def e290 : ℝ := (15975809/100000000000000)
theorem h290 : Model (fun x => f290 ((21/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(400525963484373/12500000000000),(7443222163599/100000000000000),(-290200871/5000000000000),(-50225891/100000000000000)⟩
def e291 : ℝ := (138888737/100000000000000)
theorem h291 : Model (fun x => f291 ((21/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(132602947816499/1562500000000),(7443222163599/100000000000000),(-290200871/5000000000000),(-50225891/100000000000000)⟩
def e292 : ℝ := (69444369/50000000000000)
theorem h292 : Model (fun x => f292 ((21/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4889148958827051/50000000000000),(28278111720351/100000000000000),(-10035558569/100000000000000),(-105679297/50000000000000)⟩
def e293 : ℝ := (66032703/12500000000000)
theorem h293 : Model (fun x => f293 ((21/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(15047345536701721/100000000000000),(28278111720351/100000000000000),(-10035558569/100000000000000),(-105679297/50000000000000)⟩
def e294 : ℝ := (4226093/800000000000)
theorem h294 : Model (fun x => f294 ((21/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8668820501270463/50000000000000),(67515279495113/100000000000000),(8755529177/50000000000000),(-55173721/10000000000000)⟩
def e295 : ℝ := (1263380423/100000000000000)
theorem h295 : Model (fun x => f295 ((21/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(19673355288255211/100000000000000),(67515279495113/100000000000000),(8755529177/50000000000000),(-55173721/10000000000000)⟩
def e296 : ℝ := (157922553/12500000000000)
theorem h296 : Model (fun x => f296 ((21/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(11333878472826427/50000000000000),(123464061556599/100000000000000),(32274259813/25000000000000),(-520901851/50000000000000)⟩
def e297 : ℝ := (289434241/12500000000000)
theorem h297 : Model (fun x => f297 ((21/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(11535068949016903/50000000000000),(123464061556599/100000000000000),(32274259813/25000000000000),(-520901851/50000000000000)⟩
def e298 : ℝ := (2315473929/100000000000000)
theorem h298 : Model (fun x => f298 ((21/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(26581550066730083/100000000000000),(48953590094789/25000000000000),(379298236023/100000000000000),(-306440167/20000000000000)⟩
def e299 : ℝ := (1840915421/50000000000000)
theorem h299 : Model (fun x => f299 ((21/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(5312786203822207/20000000000000),(48953590094789/25000000000000),(379298236023/100000000000000),(-306440167/20000000000000)⟩
def e300 : ℝ := (3681830843/100000000000000)
theorem h300 : Model (fun x => f300 ((21/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(6121423855154709/20000000000000),(17955487405477/6250000000000),(103381718653/12500000000000),(-1742437637/100000000000000)⟩
def e301 : ℝ := (338531537/6250000000000)
theorem h301 : Model (fun x => f301 ((21/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(15305226304553439/50000000000000),(17955487405477/6250000000000),(103381718653/12500000000000),(-1742437637/100000000000000)⟩
def e302 : ℝ := (5416504593/100000000000000)
theorem h302 : Model (fun x => f302 ((21/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(2329546452127607/50000000000000),(7174401014273/6250000000000),(718430488051/100000000000000),(32298391/6250000000000)⟩
def e303 : ℝ := (2184779543/100000000000000)
theorem h303 : Model (fun x => f303 ((21/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(33189463563867/25000000000000),(267489651609/50000000000000),(-10582321/50000000000000),(-2219593/50000000000000)⟩
def e304 : ℝ := (10001843/100000000000000)
theorem h304 : Model (fun x => f304 ((21/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(26902574328021/12500000000000),(928617501/400000000000),(-121532349/50000000000000),(-718321/50000000000000)⟩
def e305 : ℝ := (135279/3125000000000)
theorem h305 : Model (fun x => f305 ((21/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(115799760875951/25000000000000),(499644026859/50000000000000),(-253647019/50000000000000),(-731247/10000000000000)⟩
def e306 : ℝ := (18659699/100000000000000)
theorem h306 : Model (fun x => f306 ((21/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(199379947144469/20000000000000),(322601053683/10000000000000),(6388521/6250000000000),(-6499769/25000000000000)⟩
def e307 : ℝ := (30163921/50000000000000)
theorem h307 : Model (fun x => f307 ((21/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(214553353902839/10000000000000),(4628692706669/50000000000000),(5286203881/100000000000000),(-1947031/2500000000000)⟩
def e308 : ℝ := (173379891/100000000000000)
theorem h308 : Model (fun x => f308 ((21/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1424182144372747/50000000000000),(5942016653077/25000000000000),(56088852331/100000000000000),(-43079221/25000000000000)⟩
def e309 : ℝ := (223725659/50000000000000)
theorem h309 : Model (fun x => f309 ((21/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(14402574328021/1562500000000),(928617501/50000000000),(-121532349/6250000000000),(-718321/6250000000000)⟩
def e310 : ℝ := (135279/390625000000)
theorem h310 : Model (fun x => f310 ((21/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(263630652812203/25000000000000),(1196107152609/50000000000000),(-982841113/50000000000000),(-7966161/50000000000000)⟩
def e311 : ℝ := (44633267/100000000000000)
theorem h311 : Model (fun x => f311 ((21/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(288630652812203/25000000000000),(1196107152609/50000000000000),(-982841113/50000000000000),(-7966161/50000000000000)⟩
def e312 : ℝ := (44633267/100000000000000)
theorem h312 : Model (fun x => f312 ((21/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(4110626220537891/12500000000000),(171273340637933/50000000000000),(1160151781569/100000000000000),(-1568687071/100000000000000)⟩
def e313 : ℝ := (202112763/3125000000000)
theorem h313 : Model (fun x => f313 ((21/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(304089920351/100000000000000),(-791888111/25000000000000),(4453361/20000000000000),(-105689/100000000000000)⟩
def e314 : ℝ := (30623/50000000000000)
theorem h314 : Model (fun x => f314 ((21/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (16270647447475103/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(3541957975407/25000000000000),(100743437061/50000000000000),(-82788161/20000000000000),(-109839/20000000000000)⟩
def e315 : ℝ := (9660571/100000000000000)
theorem h315 : Model (fun x => f315 ((21/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(30679585264029/100000000000000),(475320326987/100000000000000),(-325719693/100000000000000),(-2344421/100000000000000)⟩
def e316 : ℝ := (2773379/20000000000000)
theorem h316 : Model (fun x => f316 ((21/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(63731244459389/50000000000000),(1455498428667/100000000000000),(-2979145061/25000000000000),(-61906443/100000000000000)⟩
def e317 : ℝ := (29340307/50000000000000)
theorem h317 : Model (fun x => f317 ((21/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(12139284658931/25000000000000),(23006663121/25000000000000),(-5416093927/100000000000000),(699961/2500000000000)⟩
def e318 : ℝ := (23645373/100000000000000)
theorem h318 : Model (fun x => f318 ((21/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-28773532852511/25000000000000),(-92126009289/25000000000000),(4617354801/100000000000000),(-2226307/2500000000000)⟩
def e319 : ℝ := (40391659/100000000000000)
theorem h319 : Model (fun x => f319 ((21/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((21/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-4851/64),(-231/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((21/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((21/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(2037/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((21/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(11445/64),(157/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((21/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((21/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(18357/64),(157/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((21/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2294625/32),(3925/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((21/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((21/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(4248816855859313/390625000000),(686244236656141/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (140607/100000000000000)
theorem h329 : Model (fun x => f329 ((21/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(1838747177/20000000000000),(-11600929/100000000000000),(50167/12500000000000),(-199/20000000000000)⟩
def e330 : ℝ := (21/100000000000000)
theorem h330 : Model (fun x => f330 ((21/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (543139438505377081/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(659255506409941/100000000000000),(1423470155957/100000000000000),(5065513323/50000000000000),(23521669/50000000000000)⟩
def e331 : ℝ := (2446629/100000000000000)
theorem h331 : Model (fun x => f331 ((21/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((21/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(93/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((21/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((21/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((21/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(775806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((21/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((21/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((21/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3441859793758589/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (217/20000000000000)
theorem h339 : Model (fun x => f339 ((21/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3874193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((21/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((21/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((21/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(17055782861259/781250000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (271/25000000000000)
theorem h343 : Model (fun x => f343 ((21/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4580557845717/100000000000000),(-5911627849/100000000000000),(1525899/20000000000000),(-9847/100000000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((21/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2180322664605587/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(39414094705397/25000000000000),(812610394943/100000000000000),(-524373933/50000000000000),(1353489/100000000000000)⟩
def e345 : ℝ := (143/5000000000000)
theorem h345 : Model (fun x => f345 ((21/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(64414094705397/25000000000000),(812610394943/100000000000000),(-524373933/50000000000000),(1353489/100000000000000)⟩
def e346 : ℝ := (143/5000000000000)
theorem h346 : Model (fun x => f346 ((21/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(64414094705397/50000000000000),(406305197471/100000000000000),(-524373933/100000000000000),(84593/12500000000000)⟩
def e347 : ℝ := (1431/100000000000000)
theorem h347 : Model (fun x => f347 ((21/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(14414094705397/50000000000000),(406305197471/100000000000000),(-524373933/100000000000000),(84593/12500000000000)⟩
def e348 : ℝ := (1431/100000000000000)
theorem h348 : Model (fun x => f348 ((21/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(118859341420673/25000000000000),(1499459657333/100000000000000),(-387037903/20000000000000),(2497507/100000000000000)⟩
def e349 : ℝ := (5283/100000000000000)
theorem h349 : Model (fun x => f349 ((21/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2831151651396977/100000000000000),(1499459657333/100000000000000),(-387037903/20000000000000),(2497507/100000000000000)⟩
def e350 : ℝ := (1321/25000000000000)
theorem h350 : Model (fun x => f350 ((21/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3647321411968519/100000000000000),(13434843035399/100000000000000),(-2811627089/25000000000000),(665159/10000000000000)⟩
def e351 : ℝ := (19459/25000000000000)
theorem h351 : Model (fun x => f351 ((21/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8929702364349471/100000000000000),(13434843035399/100000000000000),(-2811627089/25000000000000),(665159/10000000000000)⟩
def e352 : ℝ := (77837/100000000000000)
theorem h352 : Model (fun x => f352 ((21/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5751986937882143/50000000000000),(53589709857729/100000000000000),(-420452441/6250000000000),(-9428723/20000000000000)⟩
def e353 : ℝ := (202801/50000000000000)
theorem h353 : Model (fun x => f353 ((21/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3354604298962381/20000000000000),(53589709857729/100000000000000),(-420452441/6250000000000),(-9428723/20000000000000)⟩
def e354 : ℝ := (405603/100000000000000)
theorem h354 : Model (fun x => f354 ((21/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(337630935957023/1562500000000),(68594155513279/50000000000000),(121117843693/100000000000000),(-255567441/100000000000000)⟩
def e355 : ℝ := (60723/6250000000000)
theorem h355 : Model (fun x => f355 ((21/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(23944094186963757/100000000000000),(68594155513279/50000000000000),(121117843693/100000000000000),(-255567441/100000000000000)⟩
def e356 : ℝ := (971569/100000000000000)
theorem h356 : Model (fun x => f356 ((21/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(3855842876485073/12500000000000),(68505829086937/25000000000000),(587880574697/100000000000000),(-78894867/20000000000000)⟩
def e357 : ℝ := (2347457/100000000000000)
theorem h357 : Model (fun x => f357 ((21/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(976535123883173/3125000000000),(68505829086937/25000000000000),(587880574697/100000000000000),(-78894867/20000000000000)⟩
def e358 : ℝ := (1173729/50000000000000)
theorem h358 : Model (fun x => f358 ((21/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(4025768060989267/10000000000000),(239993045922583/50000000000000),(1706864616523/100000000000000),(163741229/25000000000000)⟩
def e359 : ℝ := (6321921/100000000000000)
theorem h359 : Model (fun x => f359 ((21/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(20120030781136811/50000000000000),(239993045922583/50000000000000),(1706864616523/100000000000000),(163741229/25000000000000)⟩
def e360 : ℝ := (3160961/50000000000000)
theorem h360 : Model (fun x => f360 ((21/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(12960135682116493/25000000000000),(156370970628161/20000000000000),(3938122826009/100000000000000),(5534259347/100000000000000)⟩
def e361 : ℝ := (11801909/100000000000000)
theorem h361 : Model (fun x => f361 ((21/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(10368775212359861/20000000000000),(156370970628161/20000000000000),(3938122826009/100000000000000),(5534259347/100000000000000)⟩
def e362 : ℝ := (1180191/10000000000000)
theorem h362 : Model (fun x => f362 ((21/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(1868206348624099/12500000000000),(43603896099043/10000000000000),(4040150640577/100000000000000),(1730903971/12500000000000)⟩
def e363 : ℝ := (17707/156250000000)
theorem h363 : Model (fun x => f363 ((21/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(82983511934317/50000000000000),(1046871258767/100000000000000),(299756247/100000000000000),(-629361/25000000000000)⟩
def e364 : ℝ := (5979/50000000000000)
theorem h364 : Model (fun x => f364 ((21/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(114414094705397/50000000000000),(406305197471/100000000000000),(-524373933/100000000000000),(84593/12500000000000)⟩
def e365 : ℝ := (1431/100000000000000)
theorem h365 : Model (fun x => f365 ((21/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(261811701345111/50000000000000),(1859481653709/100000000000000),(-748991619/100000000000000),(-290989/25000000000000)⟩
def e366 : ℝ := (741/5000000000000)
theorem h366 : Model (fun x => f366 ((21/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(47927918068289/4000000000000),(6382527300913/100000000000000),(3095522013/100000000000000),(-11913699/100000000000000)⟩
def e367 : ℝ := (26639/50000000000000)
theorem h367 : Model (fun x => f367 ((21/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1370907339224431/50000000000000),(9736681107553/50000000000000),(6683232351/25000000000000),(-10011053/25000000000000)⟩
def e368 : ℝ := (1609/1000000000000)
theorem h368 : Model (fun x => f368 ((21/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(4550508221814933/100000000000000),(30511314776453/50000000000000),(1025790561/400000000000),(101374069/50000000000000)⟩
def e369 : ℝ := (357257/25000000000000)
theorem h369 : Model (fun x => f369 ((21/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(64414094705397/6250000000000),(406305197471/12500000000000),(-524373933/12500000000000),(84593/1562500000000)⟩
def e370 : ℝ := (1431/12500000000000)
theorem h370 : Model (fun x => f370 ((21/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(598296269577493/50000000000000),(859462567707/20000000000000),(-3895235217/100000000000000),(724127/25000000000000)⟩
def e371 : ℝ := (11703/50000000000000)
theorem h371 : Model (fun x => f371 ((21/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(648296269577493/50000000000000),(859462567707/20000000000000),(-3895235217/100000000000000),(724127/25000000000000)⟩
def e372 : ℝ := (11703/50000000000000)
theorem h372 : Model (fun x => f372 ((21/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(29500775048843321/50000000000000),(61672777250863/6250000000000),(57701612657/1000000000000),(11404005477/100000000000000)⟩
def e373 : ℝ := (20161057/100000000000000)
theorem h373 : Model (fun x => f373 ((21/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(42371768129/25000000000000),(-2834566469/100000000000000),(15415541/50000000000000),(-271179/100000000000000)⟩
def e374 : ℝ := (1093/50000000000000)
theorem h374 : Model (fun x => f374 ((21/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (290045020381203/500000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(3166368248841/12500000000000),(315385264173/100000000000000),(-226093821/25000000000000),(114183/4000000000000)⟩
def e375 : ℝ := (691923/100000000000000)
theorem h375 : Model (fun x => f375 ((21/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(39414094705397/12500000000000),(812610394943/50000000000000),(-524373933/25000000000000),(1353489/50000000000000)⟩
def e376 : ℝ := (143/2500000000000)
theorem h376 : Model (fun x => f376 ((21/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(38811381444293/100000000000000),(-122405399579/100000000000000),(272011999/50000000000000),(-2417883/100000000000000)⟩
def e377 : ℝ := (2193/20000000000000)
theorem h377 : Model (fun x => f377 ((21/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (25684271832243/10000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(30594309277853/25000000000000),(244810799157/100000000000000),(-1088048001/100000000000000),(4835761/100000000000000)⟩
def e378 : ℝ := (91067/100000000000000)
theorem h378 : Model (fun x => f378 ((21/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(5594309277853/25000000000000),(244810799157/100000000000000),(-1088048001/100000000000000),(4835761/100000000000000)⟩
def e379 : ℝ := (91067/100000000000000)
theorem h379 : Model (fun x => f379 ((21/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(18065211192637/4000000000000),(45173421273/5000000000000),(-2007707621/50000000000000),(892313/5000000000000)⟩
def e380 : ℝ := (336083/100000000000000)
theorem h380 : Model (fun x => f380 ((21/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(280734456553021/10000000000000),(45173421273/5000000000000),(-2007707621/50000000000000),(892313/5000000000000)⟩
def e381 : ℝ := (84021/25000000000000)
theorem h381 : Model (fun x => f381 ((21/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(858887678873311/25000000000000),(7978322363217/100000000000000),(-16623711193/50000000000000),(137935893/100000000000000)⟩
def e382 : ℝ := (3100967/100000000000000)
theorem h382 : Model (fun x => f382 ((21/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2179482916968549/25000000000000),(7978322363217/100000000000000),(-16623711193/50000000000000),(137935893/100000000000000)⟩
def e383 : ℝ := (387621/12500000000000)
theorem h383 : Model (fun x => f383 ((21/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(10668763908405279/100000000000000),(3110608866203/10000000000000),(-116010763431/100000000000000),(422179217/100000000000000)⟩
def e384 : ℝ := (12837319/100000000000000)
theorem h384 : Model (fun x => f384 ((21/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(7968905763726449/50000000000000),(3110608866203/10000000000000),(-116010763431/100000000000000),(422179217/100000000000000)⟩
def e385 : ℝ := (320933/2500000000000)
theorem h385 : Model (fun x => f385 ((21/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(19504253403320987/100000000000000),(4817765977907/6250000000000),(-239230742527/100000000000000),(332454841/50000000000000)⟩
def e386 : ℝ := (34094281/100000000000000)
theorem h386 : Model (fun x => f386 ((21/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(2729995961129409/12500000000000),(4817765977907/6250000000000),(-239230742527/100000000000000),(332454841/50000000000000)⟩
def e387 : ℝ := (17047141/50000000000000)
theorem h387 : Model (fun x => f387 ((21/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(13363574521933231/50000000000000),(18475022717907/12500000000000),(-341682722613/100000000000000),(222725171/50000000000000)⟩
def e388 : ℝ := (1089751/1562500000000)
theorem h388 : Model (fun x => f388 ((21/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(13564764998123707/50000000000000),(18475022717907/12500000000000),(-341682722613/100000000000000),(222725171/50000000000000)⟩
def e389 : ℝ := (13948813/20000000000000)
theorem h389 : Model (fun x => f389 ((21/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(1660018462535967/5000000000000),(247289798054393/100000000000000),(-70298675669/20000000000000),(-23502563/4000000000000)⟩
def e390 : ℝ := (122340161/100000000000000)
theorem h390 : Model (fun x => f390 ((21/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(8295687550775073/25000000000000),(247289798054393/100000000000000),(-70298675669/20000000000000),(-23502563/4000000000000)⟩
def e391 : ℝ := (61170081/50000000000000)
theorem h391 : Model (fun x => f391 ((21/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(40608132896135591/100000000000000),(383861378471837/100000000000000),(-9290000223/5000000000000),(-1332765821/50000000000000)⟩
def e392 : ℝ := (9740819/5000000000000)
theorem h392 : Model (fun x => f392 ((21/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(10152866557367231/25000000000000),(383861378471837/100000000000000),(-9290000223/5000000000000),(-1332765821/50000000000000)⟩
def e393 : ℝ := (194816381/100000000000000)
theorem h393 : Model (fun x => f393 ((21/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(9087724092589271/100000000000000),(37063765173103/20000000000000),(228142477127/50000000000000),(-1632026711/50000000000000)⟩
def e394 : ℝ := (95485823/100000000000000)
theorem h394 : Model (fun x => f394 ((21/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(149761881630227/100000000000000),(599185384317/100000000000000),(-2063722891/100000000000000),(6508423/100000000000000)⟩
def e395 : ℝ := (129481/50000000000000)
theorem h395 : Model (fun x => f395 ((21/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(55594309277853/25000000000000),(244810799157/100000000000000),(-1088048001/100000000000000),(4835761/100000000000000)⟩
def e396 : ℝ := (91067/100000000000000)
theorem h396 : Model (fun x => f396 ((21/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(494516355853051/100000000000000),(1088806982631/100000000000000),(-4239818893/100000000000000),(3235989/20000000000000)⟩
def e397 : ℝ := (55137/12500000000000)
theorem h397 : Model (fun x => f397 ((21/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1099691809210053/100000000000000),(226993020511/6250000000000),(-6071725181/50000000000000),(18833933/50000000000000)⟩
def e398 : ℝ := (6141/390625000000)
theorem h398 : Model (fun x => f398 ((21/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(305683032757727/12500000000000),(269216430639/2500000000000),(-117492927/390625000000),(67698061/100000000000000)⟩
def e399 : ℝ := (1226399/25000000000000)
theorem h399 : Model (fun x => f399 ((21/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3662373293458521/100000000000000),(15390104062139/50000000000000),(-30989047859/100000000000000),(-14191231/10000000000000)⟩
def e400 : ℝ := (15467593/100000000000000)
theorem h400 : Model (fun x => f400 ((21/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(30594309277853/3125000000000),(244810799157/12500000000000),(-1088048001/12500000000000),(4835761/12500000000000)⟩
def e401 : ℝ := (91067/12500000000000)
theorem h401 : Model (fun x => f401 ((21/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1128779778521523/100000000000000),(2557671777573/100000000000000),(-10768106899/100000000000000),(45194511/100000000000000)⟩
def e402 : ℝ := (493749/50000000000000)
theorem h402 : Model (fun x => f402 ((21/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1228779778521523/100000000000000),(2557671777573/100000000000000),(-10768106899/100000000000000),(45194511/100000000000000)⟩
def e403 : ℝ := (493749/50000000000000)
theorem h403 : Model (fun x => f403 ((21/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(45002502443991021/100000000000000),(235946230667063/50000000000000),(2420254269/20000000000000),(-2097820957/50000000000000)⟩
def e404 : ℝ := (60137413/25000000000000)
theorem h404 : Model (fun x => f404 ((21/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(222209865161/100000000000000),(-466014797/20000000000000),(24373207/100000000000000),(-29279/12500000000000)⟩
def e405 : ℝ := (3473/100000000000000)
theorem h405 : Model (fun x => f405 ((21/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (173947630645289/390625000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(10096909726173/50000000000000),(200046018163/100000000000000),(-217837153/20000000000000),(5996957/100000000000000)⟩
def e406 : ℝ := (39259/5000000000000)
theorem h406 : Model (fun x => f406 ((21/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(22762382721537/50000000000000),(16107227573/3125000000000),(-1993561049/100000000000000),(2212883/25000000000000)⟩
def e407 : ℝ := (1477103/100000000000000)
theorem h407 : Model (fun x => f407 ((21/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(12004980918547/4000000000000),(4046040560211/100000000000000),(-596762197/50000000000000),(20722263/20000000000000)⟩
def e408 : ℝ := (2210419/20000000000000)
theorem h408 : Model (fun x => f408 ((21/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(114333151605209/100000000000000),(90492325339/20000000000000),(-476383431/10000000000000),(84840827/100000000000000)⟩
def e409 : ℝ := (6965923/100000000000000)
theorem h409 : Model (fun x => f409 ((21/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-152195960967/20000000000000),(83957589539/100000000000000),(-146479509/100000000000000),(-4211453/100000000000000)⟩
def e410 : ℝ := (23678791/50000000000000)
theorem h410 : Model (fun x => f410 ((21/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(8605879211425781/50000000000000),(193596954345703/25000000000000),(56889/409600),(2541/2048000)⟩
def e411 : ℝ := (69091797/12500000000000)
theorem h411 : Model (fun x => f411 ((21/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(2025/64),(9/32),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((21/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(91125/512),(1215/512),(27/2560),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((21/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(765830803848803021/25000000000000),(178668703794479279/100000000000000),(561389688849449/12500000000000),(63477551651/100000000000)⟩
def e414 : ℝ := (277116823601/50000000000000)
theorem h414 : Model (fun x => f414 ((21/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(3264428627/100000000000000),(-95199101/50000000000000),(6319041/100000000000000),(-157063/100000000000000)⟩
def e415 : ℝ := (973/20000000000000)
theorem h415 : Model (fun x => f415 ((21/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (2880099362304639011/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(345794030377/6250000000000),(-783959309/5000000000000),(-92961637/50000000000000),(231383/5000000000000)⟩
def e416 : ℝ := (628491/4000000000000)
theorem h416 : Model (fun x => f416 ((21/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(4771724681197/100000000000000),(68278403359/100000000000000),(-332402783/100000000000000),(416207/100000000000000)⟩
def e417 : ℝ := (63069857/100000000000000)
theorem h417 : Model (fun x => f417 ((21/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((21/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((14314652431237/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (13/5) (53/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (13/5) (53/20) ≤ (14315030850379/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(21/8)-(1/40)) (by norm_num : ((21/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel32


noncomputable section
namespace Hf4Quad.Panel33
open Hf4Quad.Dag

def p0 : Cubic := ⟨(107/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((107/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((107/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((107/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((107/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(29297619047619/6250000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((107/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-29297619047619/6250000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((107/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-377333333333333/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((107/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((107/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(11449/1600),(107/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((107/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(866247089947089/100000000000000),(8095767195767/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((107/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-866247089947089/100000000000000),(-8095767195767/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((107/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-621790211640211/50000000000000),(-10286243386243/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((107/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((107/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1225043/64000),(34347/64000),(321/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((107/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(9324292857349537/50000000000000),(522857543402777/100000000000000),(2443259548611/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((107/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-9324292857349537/50000000000000),(-522857543402777/100000000000000),(-2443259548611/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((107/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-2486520767247437/12500000000000),(-543430030175263/100000000000000),(-4962180472883/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((107/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((107/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(131079601/2560000),(1225043/640000),(34347/1280000),(107/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((107/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(3576080384424603/25000000000000),(133685248015873/25000000000000),(7496369047619/100000000000000),(23353174603/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((107/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1396961150070271/25000000000000),(-8689038111771/100000000000000),(158386785921/6250000000000),(31483548281/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((107/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((107/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(13696794245117187/100000000000000),(160009278564453/25000000000000),(1225043/10240000),(11449/10240000)⟩
def e22 : ℝ := (523437501/100000000000000)
theorem h22 : Model (fun x => f22 ((107/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(89232078063559747/100000000000000),(833944654799623/20000000000000),(77938752785011/100000000000000),(364199779369/50000000000000)⟩
def e23 : ℝ := (3410098389/100000000000000)
theorem h23 : Model (fun x => f23 ((107/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(83644233463278663/100000000000000),(520129279485793/12500000000000),(80472941359747/100000000000000),(759883107019/100000000000000)⟩
def e24 : ℝ := (1759612691/50000000000000)
theorem h24 : Model (fun x => f24 ((107/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((107/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(1465556984227539/4000000000000),(256814892095947/12500000000000),(9600556713867/20000000000000),(598165527343/100000000000000)⟩
def e26 : ℝ := (4208447271/100000000000000)
theorem h26 : Model (fun x => f26 ((107/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(82272802130445443/100000000000000),(4613428156847403/100000000000000),(6736898593527/6250000000000),(1343182274097/100000000000000)⟩
def e27 : ℝ := (9450079483/100000000000000)
theorem h27 : Model (fun x => f27 ((107/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(82958517796862053/50000000000000),(8774462392733747/100000000000000),(188263318856179/100000000000000),(525766345279/25000000000000)⟩
def e28 : ℝ := (2593860973/20000000000000)
theorem h28 : Model (fun x => f28 ((107/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((107/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(9800912332021667/10000000000000),(6411811805995477/100000000000000),(4494260611679/2500000000000),(22401298999/800000000000)⟩
def e30 : ℝ := (13158472909/50000000000000)
theorem h30 : Model (fun x => f30 ((107/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1453607533370277/6250000000000),(1521533119041783/100000000000000),(42659807075937/100000000000000),(33224148813/5000000000000)⟩
def e31 : ℝ := (6245053017/100000000000000)
theorem h31 : Model (fun x => f31 ((107/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(94587378063824269/50000000000000),(1029599551177553/10000000000000),(57730781483029/25000000000000),(10810735771/390625000000)⟩
def e32 : ℝ := (9607178941/50000000000000)
theorem h32 : Model (fun x => f32 ((107/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((107/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(4911621/320),(45903/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((107/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((107/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(236363/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((107/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(8693429/320),(12715/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((107/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((107/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(9423029/320),(12715/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((107/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-9423029/320),(-12715/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((107/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((107/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(147/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((107/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(21609/1600),(147/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((107/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((107/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(453789/160),(3087/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((107/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(35258677491/100000000000000),(-239854949/50000000000000),(2447499/50000000000000),(-111/250000000000)⟩
def e46 : ℝ := (97/25000000000000)
theorem h46 : Model (fun x => f46 ((107/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (223797/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1038261064060439/100000000000000),(116185742063/100000000000000),(-801772569/100000000000000),(2779747/50000000000000)⟩
def e47 : ℝ := (4543869/20000000000000)
theorem h47 : Model (fun x => f47 ((107/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((107/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(187/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((107/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((107/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((107/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(155833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((107/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(255833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((107/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((107/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(25583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((107/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((107/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(537249999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((107/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((107/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(5583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((107/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(374955729166639/50000000000000),(3408854166661/25000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (67/50000000000000)
theorem h60 : Model (fun x => f60 ((107/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(81813368055553/50000000000000),(53298611111/5000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((107/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((107/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(25583333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((107/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(360698350694439/25000000000000),(65407986111/1250000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((107/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(385698350694439/25000000000000),(65407986111/1250000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((107/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(11569584505840273/100000000000000),(62401616843789/25000000000000),(644494086367/50000000000000),(67014341/3125000000000)⟩
def e66 : ℝ := (635431/100000000000000)
theorem h66 : Model (fun x => f66 ((107/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(45583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((107/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(129865017361109/25000000000000),(59353298611/3125000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((107/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1183936074942101/100000000000000),(6493250868043/100000000000000),(11870659721/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (7/10000000000000)
theorem h69 : Model (fun x => f69 ((107/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(342441211713887/250000000000),(3706423158997499/100000000000000),(6568351219217/20000000000000),(139553112911/100000000000000)⟩
def e70 : ℝ := (79558297/25000000000000)
theorem h70 : Model (fun x => f70 ((107/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((107/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1718080729166613/6250000000000),(1119270833331/625000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((107/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(7674093923610413/100000000000000),(32906562499941/20000000000000),(413802083329/50000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1681/100000000000000)
theorem h73 : Model (fun x => f73 ((107/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(45428183193281699/50000000000000),(1223130746305061/50000000000000),(10696399069491/50000000000000),(22053196337/25000000000000)⟩
def e74 : ℝ := (37856959/20000000000000)
theorem h74 : Model (fun x => f74 ((107/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(113916425536059099/50000000000000),(6152684651607621/100000000000000),(54234554235067/100000000000000),(227765898259/100000000000000)⟩
def e75 : ℝ := (507517983/100000000000000)
theorem h75 : Model (fun x => f75 ((107/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((107/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(572693576388871/6250000000000),(373090277777/625000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((107/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(487087673611/6250000000000),(29079861111/12500000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((107/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1087829137731/50000000000000),(97417534721/100000000000000),(290798611/20000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((107/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(1993576830039/1000000000000),(255630263463/2500000000000),(1934988767/1000000000000),(203188041/12500000000000)⟩
def e80 : ℝ := (5739199/100000000000000)
theorem h80 : Model (fun x => f80 ((107/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(90873877169277/20000000000000),(12067808015779/50000000000000),(241810616861/50000000000000),(22555203/500000000000)⟩
def e81 : ℝ := (397549/2000000000000)
theorem h81 : Model (fun x => f81 ((107/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(228287220457964583/100000000000000),(6176820267639179/100000000000000),(54718175468789/100000000000000),(232276938859/100000000000000)⟩
def e82 : ℝ := (527395433/100000000000000)
theorem h82 : Model (fun x => f82 ((107/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(303685634283/50000000000000),(36260971257/100000000000000),(811812789/100000000000000),(8077739/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((107/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(84778906237/50000000000000),(6326784047/50000000000000),(7554369/2000000000000),(1409397/25000000000000)⟩
def e84 : ℝ := (42201/100000000000000)
theorem h84 : Model (fun x => f84 ((107/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(9466977863/20000000000000),(4238945311/100000000000000),(158169601/100000000000000),(3147653/100000000000000)⟩
def e85 : ℝ := (35449/100000000000000)
theorem h85 : Model (fun x => f85 ((107/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(13214323267/100000000000000),(690300469/50000000000000),(1931811/3125000000000),(1537759/100000000000000)⟩
def e86 : ℝ := (23161/100000000000000)
theorem h86 : Model (fun x => f86 ((107/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(39642969801/100000000000000),(2070901407/50000000000000),(5795433/3125000000000),(4613277/100000000000000)⟩
def e87 : ℝ := (69483/100000000000000)
theorem h87 : Model (fun x => f87 ((107/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-39642969801/100000000000000),(-2070901407/50000000000000),(-5795433/3125000000000),(-4613277/100000000000000)⟩
def e88 : ℝ := (69483/100000000000000)
theorem h88 : Model (fun x => f88 ((107/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(114143590407497391/50000000000000),(1235363225167273/20000000000000),(54717990014933/100000000000000),(116136162791/50000000000000)⟩
def e89 : ℝ := (131866229/25000000000000)
theorem h89 : Model (fun x => f89 ((107/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1718080729166613/5000000000000),(1119270833331/500000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((107/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(539677527494437/20000000000000),(3946453583133/20000000000000),(54110423897/100000000000000),(16487027/25000000000000)⟩
def e91 : ℝ := (30351/100000000000000)
theorem h91 : Model (fun x => f91 ((107/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(231802389988119289/25000000000000),(6410389504509229/50000000000000),(72602590810169/100000000000000),(107864916647/50000000000000)⟩
def e92 : ℝ := (177855629/50000000000000)
theorem h92 : Model (fun x => f92 ((107/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(539252421/5000000000000),(-149127801/100000000000000),(1217537/100000000000000),(-1917/25000000000000)⟩
def e93 : ℝ := (53/100000000000000)
theorem h93 : Model (fun x => f93 ((107/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (914315962267103977/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(492417659751/2000000000000),(325732957271/100000000000000),(-530507451/100000000000000),(287727/25000000000000)⟩
def e94 : ℝ := (337173/100000000000000)
theorem h94 : Model (fun x => f94 ((107/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(155833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((107/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(2442996742671/6250000000000),(-127322305807/100000000000000),(414730637/100000000000000),(-270183/20000000000000)⟩
def e96 : ℝ := (2209/50000000000000)
theorem h96 : Model (fun x => f96 ((107/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (31874999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(4872964169381/4000000000000),(254644611613/100000000000000),(-829461279/100000000000000),(108073/4000000000000)⟩
def e97 : ℝ := (18183/50000000000000)
theorem h97 : Model (fun x => f97 ((107/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(102332247557001/4000000000000),(5347536843873/100000000000000),(-17418686859/100000000000000),(2269533/4000000000000)⟩
def e98 : ℝ := (381843/50000000000000)
theorem h98 : Model (fun x => f98 ((107/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(872964169381/4000000000000),(254644611613/100000000000000),(-829461279/100000000000000),(108073/4000000000000)⟩
def e99 : ℝ := (18183/50000000000000)
theorem h99 : Model (fun x => f99 ((107/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(558327409309301/100000000000000),(1536328174689/20000000000000),(-2280883437/20000000000000),(-1801977/25000000000000)⟩
def e100 : ℝ := (95957/6250000000000)
theorem h100 : Model (fun x => f100 ((107/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(37102780931361/25000000000000),(310218517079/50000000000000),(-343132191/25000000000000),(2358591/100000000000000)⟩
def e101 : ℝ := (109477/100000000000000)
theorem h101 : Model (fun x => f101 ((107/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(4872964169381/400000000000),(254644611613/10000000000000),(-829461279/10000000000000),(108073/400000000000)⟩
def e102 : ℝ := (18183/5000000000000)
theorem h102 : Model (fun x => f102 ((107/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(683326083035347/50000000000000),(197930196893/6250000000000),(-4833570777/50000000000000),(29376841/100000000000000)⟩
def e103 : ℝ := (473137/100000000000000)
theorem h103 : Model (fun x => f103 ((107/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(733326083035347/50000000000000),(197930196893/6250000000000),(-4833570777/50000000000000),(29376841/100000000000000)⟩
def e104 : ℝ := (473137/100000000000000)
theorem h104 : Model (fun x => f104 ((107/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(2047180260600313/25000000000000),(8146533056813/6250000000000),(11015578911/50000000000000),(-1045455647/100000000000000)⟩
def e105 : ℝ := (14189003/50000000000000)
theorem h105 : Model (fun x => f105 ((107/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(8872964169381/4000000000000),(254644611613/100000000000000),(-829461279/100000000000000),(108073/4000000000000)⟩
def e106 : ℝ := (18183/50000000000000)
theorem h106 : Model (fun x => f106 ((107/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(246029666097247/50000000000000),(141215782173/12500000000000),(-1515725661/50000000000000),(7762241/100000000000000)⟩
def e107 : ℝ := (182209/100000000000000)
theorem h107 : Model (fun x => f107 ((107/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(545753102971411/50000000000000),(939751931529/25000000000000),(-7929144331/100000000000000),(6711517/50000000000000)⟩
def e108 : ℝ := (329793/50000000000000)
theorem h108 : Model (fun x => f108 ((107/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(8938039836515541/10000000000000),(1730533278802707/100000000000000),(1122709214203/25000000000000),(-9909545679/50000000000000)⟩
def e109 : ℝ := (48665459/12500000000000)
theorem h109 : Model (fun x => f109 ((107/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(779158399558581/3125000000000),(6514588858659/6250000000000),(-7205776011/3125000000000),(49530411/12500000000000)⟩
def e110 : ℝ := (2299017/12500000000000)
theorem h110 : Model (fun x => f110 ((107/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(5441418920695087/100000000000000),(10779840847553/12500000000000),(165831331/2000000000000),(-69162329/10000000000000)⟩
def e111 : ℝ := (9456707/50000000000000)
theorem h111 : Model (fun x => f111 ((107/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(29696712605366899/50000000000000),(286461103093417/25000000000000),(2900765406167/100000000000000),(-13345020109/100000000000000)⟩
def e112 : ℝ := (258749079/100000000000000)
theorem h112 : Model (fun x => f112 ((107/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(18596727946986151/12500000000000),(23011021529411/800000000000),(7391602262979/100000000000000),(-33164111467/100000000000000)⟩
def e113 : ℝ := (648072751/100000000000000)
theorem h113 : Model (fun x => f113 ((107/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(259719466519527/3125000000000),(2171529619553/6250000000000),(-2401925337/3125000000000),(16510137/12500000000000)⟩
def e114 : ℝ := (766339/12500000000000)
theorem h114 : Model (fun x => f114 ((107/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(2381457628197/50000000000000),(27786952733/25000000000000),(143196897/50000000000000),(-3045059/100000000000000)⟩
def e115 : ℝ := (7349/20000000000000)
theorem h115 : Model (fun x => f115 ((107/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(1039463590157/100000000000000),(2274095073/6250000000000),(306028253/100000000000000),(-728513/100000000000000)⟩
def e116 : ℝ := (2131/12500000000000)
theorem h116 : Model (fun x => f116 ((107/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(17278011462531/20000000000000),(3385165162887/100000000000000),(18638543863/50000000000000),(19187461/100000000000000)⟩
def e117 : ℝ := (1930021/100000000000000)
theorem h117 : Model (fun x => f117 ((107/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(191633970781489/100000000000000),(7729099925349/100000000000000),(4529656727/5000000000000),(55870991/50000000000000)⟩
def e118 : ℝ := (4488573/100000000000000)
theorem h118 : Model (fun x => f118 ((107/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(148965457546670697/100000000000000),(721026697775431/25000000000000),(7482195397519/100000000000000),(-6610473897/20000000000000)⟩
def e119 : ℝ := (163140331/25000000000000)
theorem h119 : Model (fun x => f119 ((107/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(45370723479/20000000000000),(10587752087/100000000000000),(30163949/20000000000000),(346573/100000000000000)⟩
def e120 : ℝ := (237/3125000000000)
theorem h120 : Model (fun x => f120 ((107/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(77357453/156250000000),(722088141/25000000000000),(11598907/20000000000000),(188999/50000000000000)⟩
def e121 : ℝ := (1847/100000000000000)
theorem h121 : Model (fun x => f121 ((107/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(675302847/6250000000000),(756428489/100000000000000),(3920233/20000000000000),(103777/50000000000000)⟩
def e122 : ℝ := (991/100000000000000)
theorem h122 : Model (fun x => f122 ((107/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(471612151/20000000000000),(96298849/50000000000000),(6114361/100000000000000),(89227/100000000000000)⟩
def e123 : ℝ := (613/100000000000000)
theorem h123 : Model (fun x => f123 ((107/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(1414836453/20000000000000),(288896547/50000000000000),(18343083/100000000000000),(267681/100000000000000)⟩
def e124 : ℝ := (1839/100000000000000)
theorem h124 : Model (fun x => f124 ((107/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-1414836453/20000000000000),(-288896547/50000000000000),(-18343083/100000000000000),(-267681/100000000000000)⟩
def e125 : ℝ := (1839/100000000000000)
theorem h125 : Model (fun x => f125 ((107/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(9310340654530527/6250000000000),(288410621330863/10000000000000),(1870544263609/25000000000000),(-16526318583/50000000000000)⟩
def e126 : ℝ := (652563163/100000000000000)
theorem h126 : Model (fun x => f126 ((107/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(779158399558581/2500000000000),(6514588858659/5000000000000),(-7205776011/2500000000000),(49530411/10000000000000)⟩
def e127 : ℝ := (2299017/10000000000000)
theorem h127 : Model (fun x => f127 ((107/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1210611931998457/50000000000000),(5558923477709/50000000000000),(-8535132049/50000000000000),(394773/5000000000000)⟩
def e128 : ℝ := (2064953/100000000000000)
theorem h128 : Model (fun x => f128 ((107/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(18865169108448789/2500000000000),(661968113787101/10000000000000),(546686446293/25000000000000),(-19916544757/50000000000000)⟩
def e129 : ℝ := (1320133473/100000000000000)
theorem h129 : Model (fun x => f129 ((107/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(3312983819/25000000000000),(-116250729/100000000000000),(98139/10000000000000),(-7573/100000000000000)⟩
def e130 : ℝ := (21/25000000000000)
theorem h130 : Model (fun x => f130 ((107/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (747984855301072391/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2467600635027/12500000000000),(104513233273/50000000000000),(-224832301/25000000000000),(246561/6250000000000)⟩
def e131 : ℝ := (161129/50000000000000)
theorem h131 : Model (fun x => f131 ((107/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(22180844033883/50000000000000),(534759423817/100000000000000),(-285967331/20000000000000),(1273971/25000000000000)⟩
def e132 : ℝ := (659431/100000000000000)
theorem h132 : Model (fun x => f132 ((107/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-460590134567561/100000000000000),(-5500656927413/100000000000000),(15111071627/100000000000000),(-11278223/20000000000000)⟩
def e133 : ℝ := (17095129/100000000000000)
theorem h133 : Model (fun x => f133 ((107/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(37383177570093/100000000000000),(-34937549131/10000000000000),(3265191507/100000000000000),(-30515809/100000000000000)⟩
def e134 : ℝ := (17993/6250000000000)
theorem h134 : Model (fun x => f134 ((107/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (53/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-86091613937861/50000000000000),(-223565650563/50000000000000),(2456948987/25000000000000),(-112929349/100000000000000)⟩
def e135 : ℝ := (10168319/100000000000000)
theorem h135 : Model (fun x => f135 ((107/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(131079601/256000),(1225043/64000),(34347/128000),(107/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((107/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((107/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(11025387/32000),(309123/32000),(2889/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((107/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(219282697/256000),(1843289/64000),(45903/128000),(1/512)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((107/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-11449/1600),(-107/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((107/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(217450857/256000),(1834729/64000),(45823/128000),(1/512)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((107/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((107/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(321/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((107/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-321/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((107/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(213342057/256000),(1825129/64000),(45823/128000),(1/512)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((107/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(214110057/256000),(1825129/64000),(45823/128000),(1/512)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((107/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((107/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(214110057/4000),(1825129/1000),(45823/2000),(1/8)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((107/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((107/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(24774044589/512000),(231533127/128000),(6491583/256000),(20223/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((107/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(516669773/25000000000000),(-9657379/12500000000000),(1805117/100000000000000),(-33741/100000000000000)⟩
def e151 : ℝ := (623/100000000000000)
theorem h151 : Model (fun x => f151 ((107/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (11917423917/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(110624194547207/100000000000000),(-363527991819/100000000000000),(2966444141/100000000000000),(-23285899/100000000000000)⟩
def e152 : ℝ := (65468249/100000000000000)
theorem h152 : Model (fun x => f152 ((107/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(227/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((107/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(42449/1600),(207/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((107/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(441/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((107/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(453514739229/10000000000000),(-6170268561/20000000000000),(5246827/2500000000000),(-1427709/100000000000000)⟩
def e156 : ℝ := (9781/100000000000000)
theorem h156 : Model (fun x => f156 ((107/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (219/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(120320294784573/100000000000000),(354963981049/100000000000000),(52468269/12500000000000),(-1427721/50000000000000)⟩
def e157 : ℝ := (62647/12500000000000)
theorem h157 : Model (fun x => f157 ((107/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(220320294784573/100000000000000),(354963981049/100000000000000),(52468269/12500000000000),(-1427721/50000000000000)⟩
def e158 : ℝ := (62647/12500000000000)
theorem h158 : Model (fun x => f158 ((107/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(55080073696143/50000000000000),(44370497631/25000000000000),(52468269/25000000000000),(-1427721/100000000000000)⟩
def e159 : ℝ := (250589/100000000000000)
theorem h159 : Model (fun x => f159 ((107/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(5080073696143/50000000000000),(44370497631/25000000000000),(52468269/25000000000000),(-1427721/100000000000000)⟩
def e160 : ℝ := (250589/100000000000000)
theorem h160 : Model (fun x => f160 ((107/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((107/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((107/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(406543401090579/100000000000000),(654993060267/100000000000000),(77453159/10000000000000),(-5268971/100000000000000)⟩
def e163 : ℝ := (462397/50000000000000)
theorem h163 : Model (fun x => f163 ((107/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(21580138178163/781250000000),(654993060267/100000000000000),(77453159/10000000000000),(-5268971/100000000000000)⟩
def e164 : ℝ := (184959/20000000000000)
theorem h164 : Model (fun x => f164 ((107/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((107/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(3042907139138987/100000000000000),(2812025623271/50000000000000),(1953238759/25000000000000),(-10623083/25000000000000)⟩
def e166 : ℝ := (7961059/100000000000000)
theorem h166 : Model (fun x => f166 ((107/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8325288091519939/100000000000000),(2812025623271/50000000000000),(1953238759/25000000000000),(-10623083/25000000000000)⟩
def e167 : ℝ := (398053/5000000000000)
theorem h167 : Model (fun x => f167 ((107/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((107/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4585574816225399/50000000000000),(4194270032859/20000000000000),(36060979087/100000000000000),(-28000309/20000000000000)⟩
def e169 : ℝ := (595999/2000000000000)
theorem h169 : Model (fun x => f169 ((107/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14440197251498417/100000000000000),(4194270032859/20000000000000),(36060979087/100000000000000),(-28000309/20000000000000)⟩
def e170 : ℝ := (29799951/100000000000000)
theorem h170 : Model (fun x => f170 ((107/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((107/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(497104455499609/3125000000000),(48730819768691/100000000000000),(13406410447/12500000000000),(-63094169/25000000000000)⟩
def e172 : ℝ := (69591831/100000000000000)
theorem h172 : Model (fun x => f172 ((107/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(18243056861701773/100000000000000),(48730819768691/100000000000000),(13406410447/12500000000000),(-63094169/25000000000000)⟩
def e173 : ℝ := (8698979/12500000000000)
theorem h173 : Model (fun x => f173 ((107/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((107/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(20096578327709217/100000000000000),(5378755208327/6250000000000),(242923865583/100000000000000),(-245853889/100000000000000)⟩
def e175 : ℝ := (123544241/100000000000000)
theorem h175 : Model (fun x => f175 ((107/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(20498959280090169/100000000000000),(5378755208327/6250000000000),(242923865583/100000000000000),(-245853889/100000000000000)⟩
def e176 : ℝ := (61772121/50000000000000)
theorem h176 : Model (fun x => f176 ((107/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((107/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(22581683756832019/100000000000000),(6559293780641/5000000000000),(28960514607/6250000000000),(48262103/100000000000000)⟩
def e178 : ℝ := (23632457/12500000000000)
theorem h178 : Model (fun x => f178 ((107/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(22564064709212971/100000000000000),(6559293780641/5000000000000),(28960514607/6250000000000),(48262103/100000000000000)⟩
def e179 : ℝ := (189059657/100000000000000)
theorem h179 : Model (fun x => f179 ((107/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((107/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(12428303470679899/50000000000000),(92280852560989/50000000000000),(31625373169/4000000000000),(82873271/10000000000000)⟩
def e181 : ℝ := (5325973/2000000000000)
theorem h181 : Model (fun x => f181 ((107/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(24859940274693131/100000000000000),(92280852560989/50000000000000),(31625373169/4000000000000),(82873271/10000000000000)⟩
def e182 : ℝ := (266298651/100000000000000)
theorem h182 : Model (fun x => f182 ((107/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(2525806573543091/100000000000000),(7859207264089/12500000000000),(18402708901/4000000000000),(1519848749/100000000000000)⟩
def e183 : ℝ := (90794997/100000000000000)
theorem h183 : Model (fun x => f183 ((107/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(121352580734901/100000000000000),(48878605589/12500000000000),(777391549/100000000000000),(-1200293/50000000000000)⟩
def e184 : ℝ := (4461/800000000000)
theorem h184 : Model (fun x => f184 ((107/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(105080073696143/50000000000000),(44370497631/25000000000000),(52468269/25000000000000),(-1427721/100000000000000)⟩
def e185 : ℝ := (250589/100000000000000)
theorem h185 : Model (fun x => f185 ((107/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(441672875519473/100000000000000),(4662455161/625000000000),(1197137701/100000000000000),(-1314007/25000000000000)⟩
def e186 : ℝ := (1058803/100000000000000)
theorem h186 : Model (fun x => f186 ((107/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(58013772886467/6250000000000),(2351669433229/100000000000000),(2383430861/50000000000000),(-13661591/100000000000000)⟩
def e187 : ℝ := (3353217/100000000000000)
theorem h187 : Model (fun x => f187 ((107/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1950749289696401/100000000000000),(1647423982351/25000000000000),(2017489747/12500000000000),(-1142711/4000000000000)⟩
def e188 : ℝ := (2358231/25000000000000)
theorem h188 : Model (fun x => f188 ((107/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(591821151678583/25000000000000),(15624758483641/100000000000000),(2420751159/4000000000000),(32842327/100000000000000)⟩
def e189 : ℝ := (112719/500000000000)
theorem h189 : Model (fun x => f189 ((107/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((107/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(55080073696143/6250000000000),(44370497631/3125000000000),(52468269/3125000000000),(-1427721/12500000000000)⟩
def e191 : ℝ := (250589/12500000000000)
theorem h191 : Model (fun x => f191 ((107/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(1002633759873189/100000000000000),(226360596113/12500000000000),(2456376157/100000000000000),(-6911177/50000000000000)⟩
def e192 : ℝ := (2562337/100000000000000)
theorem h192 : Model (fun x => f192 ((107/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1102633759873189/100000000000000),(226360596113/12500000000000),(2456376157/100000000000000),(-6911177/50000000000000)⟩
def e193 : ℝ := (2562337/100000000000000)
theorem h193 : Model (fun x => f193 ((107/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(13051239632956737/50000000000000),(107576329159437/50000000000000),(1008396274247/100000000000000),(1514644319/100000000000000)⟩
def e194 : ℝ := (155065019/50000000000000)
theorem h194 : Model (fun x => f194 ((107/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(383105370877/100000000000000),(-1578894827/50000000000000),(2807059/25000000000000),(7211/100000000000000)⟩
def e195 : ℝ := (309/6250000000000)
theorem h195 : Model (fun x => f195 ((107/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (6471579096636499/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(9676500641207/100000000000000),(161112702437/100000000000000),(30364903/50000000000000),(-1463611/100000000000000)⟩
def e196 : ℝ := (48713/10000000000000)
theorem h196 : Model (fun x => f196 ((107/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(120320294784573/50000000000000),(354963981049/50000000000000),(52468269/6250000000000),(-1427721/25000000000000)⟩
def e197 : ℝ := (62647/6250000000000)
theorem h197 : Model (fun x => f197 ((107/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(9077693010331/20000000000000),(-73126582661/100000000000000),(31343773/100000000000000),(42317/6250000000000)⟩
def e198 : ℝ := (52843/50000000000000)
theorem h198 : Model (fun x => f198 ((107/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (109982453850377/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(6826441868543/6250000000000),(146253165321/100000000000000),(-62687547/100000000000000),(-1354147/100000000000000)⟩
def e199 : ℝ := (180003/25000000000000)
theorem h199 : Model (fun x => f199 ((107/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(576441868543/6250000000000),(146253165321/100000000000000),(-62687547/100000000000000),(-1354147/100000000000000)⟩
def e200 : ℝ := (180003/25000000000000)
theorem h200 : Model (fun x => f200 ((107/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(403085138904443/100000000000000),(269871912199/50000000000000),(-2313469/1000000000000),(-624681/12500000000000)⟩
def e201 : ℝ := (265719/10000000000000)
theorem h201 : Model (fun x => f201 ((107/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(344849928077341/12500000000000),(269871912199/50000000000000),(-2313469/1000000000000),(-624681/12500000000000)⟩
def e202 : ℝ := (2657191/100000000000000)
theorem h202 : Model (fun x => f202 ((107/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(3013245423860739/100000000000000),(4624356257947/100000000000000),(-238543089/20000000000000),(-43493271/100000000000000)⟩
def e203 : ℝ := (22788211/100000000000000)
theorem h203 : Model (fun x => f203 ((107/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8295626376241691/100000000000000),(4624356257947/100000000000000),(-238543089/20000000000000),(-43493271/100000000000000)⟩
def e204 : ℝ := (5697053/25000000000000)
theorem h204 : Model (fun x => f204 ((107/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(2265184448822637/25000000000000),(8591740013173/50000000000000),(52044459/20000000000000),(-82241471/50000000000000)⟩
def e205 : ℝ := (21202917/25000000000000)
theorem h205 : Model (fun x => f205 ((107/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14329785414338167/100000000000000),(8591740013173/50000000000000),(52044459/20000000000000),(-82241471/50000000000000)⟩
def e206 : ℝ := (84811669/100000000000000)
theorem h206 : Model (fun x => f206 ((107/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(7825715769573989/50000000000000),(7945217830407/20000000000000),(16432615263/100000000000000),(-384090997/100000000000000)⟩
def e207 : ℝ := (98265711/50000000000000)
theorem h207 : Model (fun x => f207 ((107/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(17987145824862263/100000000000000),(7945217830407/20000000000000),(16432615263/100000000000000),(-384090997/100000000000000)⟩
def e208 : ℝ := (196531423/100000000000000)
theorem h208 : Model (fun x => f208 ((107/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9823056428354253/50000000000000),(8712103030189/12500000000000),(16193292301/25000000000000),(-132791693/20000000000000)⟩
def e209 : ℝ := (345850999/100000000000000)
theorem h209 : Model (fun x => f209 ((107/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(10024246904544729/50000000000000),(8712103030189/12500000000000),(16193292301/25000000000000),(-132791693/20000000000000)⟩
def e210 : ℝ := (345851/100000000000)
theorem h210 : Model (fun x => f210 ((107/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(4379516081266989/20000000000000),(13180820981507/12500000000000),(40028286619/25000000000000),(-189128063/20000000000000)⟩
def e211 : ℝ := (525064913/100000000000000)
theorem h211 : Model (fun x => f211 ((107/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(21879961358715897/100000000000000),(13180820981507/12500000000000),(40028286619/25000000000000),(-189128063/20000000000000)⟩
def e212 : ℝ := (262532457/50000000000000)
theorem h212 : Model (fun x => f212 ((107/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(23897965488198589/100000000000000),(147172114566843/100000000000000),(157691713017/50000000000000),(-232215109/20000000000000)⟩
def e213 : ℝ := (73547191/10000000000000)
theorem h213 : Model (fun x => f213 ((107/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(11950649410765961/50000000000000),(147172114566843/100000000000000),(157691713017/50000000000000),(-232215109/20000000000000)⟩
def e214 : ℝ := (735471911/100000000000000)
theorem h214 : Model (fun x => f214 ((107/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(1102216748263077/50000000000000),(24265096537127/50000000000000),(229348771917/100000000000000),(-15436469/25000000000000)⟩
def e215 : ℝ := (61488919/25000000000000)
theorem h215 : Model (fun x => f215 ((107/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(119296789976567/100000000000000),(319484393969/100000000000000),(76961357/100000000000000),(-3141447/100000000000000)⟩
def e216 : ℝ := (1578871/100000000000000)
theorem h216 : Model (fun x => f216 ((107/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(13076441868543/6250000000000),(146253165321/100000000000000),(-62687547/100000000000000),(-1354147/100000000000000)⟩
def e217 : ℝ := (180003/25000000000000)
theorem h217 : Model (fun x => f217 ((107/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(437742929769943/100000000000000),(611990724611/100000000000000),(-48413737/100000000000000),(-5849741/100000000000000)⟩
def e218 : ℝ := (603779/20000000000000)
theorem h218 : Model (fun x => f218 ((107/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(915859195920377/100000000000000),(1920638672271/100000000000000),(259676397/50000000000000),(-931057/5000000000000)⟩
def e219 : ℝ := (949367/10000000000000)
theorem h219 : Model (fun x => f219 ((107/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(383237745127147/20000000000000),(1071578451133/20000000000000),(3321471047/100000000000000),(-6475779/12500000000000)⟩
def e220 : ℝ := (13269271/50000000000000)
theorem h220 : Model (fun x => f220 ((107/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1142975819788159/50000000000000),(12513717408811/100000000000000),(22554762787/100000000000000),(-107264137/100000000000000)⟩
def e221 : ℝ := (15603663/25000000000000)
theorem h221 : Model (fun x => f221 ((107/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(6826441868543/781250000000),(146253165321/12500000000000),(-62687547/12500000000000),(-1354147/12500000000000)⟩
def e222 : ℝ := (180003/3125000000000)
theorem h222 : Model (fun x => f222 ((107/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(993081349150071/100000000000000),(1489509716537/100000000000000),(-424539019/100000000000000),(-13974623/100000000000000)⟩
def e223 : ℝ := (7338967/100000000000000)
theorem h223 : Model (fun x => f223 ((107/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1093081349150071/100000000000000),(1489509716537/100000000000000),(-424539019/100000000000000),(-13974623/100000000000000)⟩
def e224 : ℝ := (7338967/100000000000000)
theorem h224 : Model (fun x => f224 ((107/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(4997462204559797/20000000000000),(42708645716971/25000000000000),(6612971647/1562500000000),(-120910763/10000000000000)⟩
def e225 : ℝ := (85530307/10000000000000)
theorem h225 : Model (fun x => f225 ((107/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(200101563367/50000000000000),(-2736130117/100000000000000),(5963979/50000000000000),(-15841/100000000000000)⟩
def e226 : ℝ := (14119/100000000000000)
theorem h226 : Model (fun x => f226 ((107/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (24816051145334993/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(8822211779869/100000000000000),(26780636257/20000000000000),(-147044371/100000000000000),(-541467/50000000000000)⟩
def e227 : ℝ := (266123/20000000000000)
theorem h227 : Model (fun x => f227 ((107/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(4624678105269/25000000000000),(147507941861/50000000000000),(-17262913/20000000000000),(-509309/20000000000000)⟩
def e228 : ℝ := (363549/20000000000000)
theorem h228 : Model (fun x => f228 ((107/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(20464051617419/100000000000000),(259110947377/100000000000000),(-30959807/5000000000000),(485143/25000000000000)⟩
def e229 : ℝ := (14383571/100000000000000)
theorem h229 : Model (fun x => f229 ((107/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(306004510167/4000000000000),(25367524681/100000000000000),(-468554863/100000000000000),(319029/6250000000000)⟩
def e230 : ℝ := (5593747/100000000000000)
theorem h230 : Model (fun x => f230 ((107/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-164533115121547/100000000000000),(-84352755289/20000000000000),(1871848217/20000000000000),(-21564977/20000000000000)⟩
def e231 : ℝ := (7881033/50000000000000)
theorem h231 : Model (fun x => f231 ((107/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((107/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-11449/320),(-107/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((107/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2247/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((107/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6527/320),(-23/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((107/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((107/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14847/320),(-23/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((107/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((107/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(371175/32),(-575/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((107/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14231/1600),(13/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((107/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23831/1600),(13/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((107/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((107/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4504059/1600),(2457/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((107/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(17761756673/50000000000000),(-38756719/100000000000000),(1532927/100000000000000),(-3299/100000000000000)⟩
def e244 : ℝ := (71/100000000000000)
theorem h244 : Model (fun x => f244 ((107/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1124739/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(206022501034399/50000000000000),(-863086961293/50000000000000),(-2144792403/25000000000000),(-630767/1000000000000)⟩
def e245 : ℝ := (476943/25000000000000)
theorem h245 : Model (fun x => f245 ((107/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(963/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((107/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(88489/1600),(467/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((107/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(122089/1600),(467/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((107/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(34969/1600),(187/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((107/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(4269330241/2560000),(19580583/640000),(253187/1280000),(327/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((107/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((107/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(194481/160),(1323/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((107/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(82270247479/100000000000000),(-223864619/20000000000000),(356927/3125000000000),(-51799/50000000000000)⟩
def e253 : ℝ := (899/100000000000000)
theorem h253 : Model (fun x => f253 ((107/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (95913/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(68601338964189/50000000000000),(325163612859/50000000000000),(1075927637/100000000000000),(-2698963/100000000000000)⟩
def e254 : ℝ := (152823/5000000000000)
theorem h254 : Model (fun x => f254 ((107/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(118601338964189/50000000000000),(325163612859/50000000000000),(1075927637/100000000000000),(-2698963/100000000000000)⟩
def e255 : ℝ := (152823/5000000000000)
theorem h255 : Model (fun x => f255 ((107/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(118601338964189/100000000000000),(325163612859/100000000000000),(268981909/50000000000000),(-674741/50000000000000)⟩
def e256 : ℝ := (1528231/100000000000000)
theorem h256 : Model (fun x => f256 ((107/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(18601338964189/100000000000000),(325163612859/100000000000000),(268981909/50000000000000),(-674741/50000000000000)⟩
def e257 : ℝ := (1528231/100000000000000)
theorem h257 : Model (fun x => f257 ((107/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(87539083521187/20000000000000),(240001714253/20000000000000),(1985342661/100000000000000),(-622529/12500000000000)⟩
def e258 : ℝ := (5639903/100000000000000)
theorem h258 : Model (fun x => f258 ((107/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(139670485166011/5000000000000),(240001714253/20000000000000),(1985342661/100000000000000),(-622529/12500000000000)⟩
def e259 : ℝ := (176247/3125000000000)
theorem h259 : Model (fun x => f259 ((107/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(41412766386167/1250000000000),(420255125859/4000000000000),(1330260481/6250000000000),(-767299/2500000000000)⟩
def e260 : ℝ := (49437257/100000000000000)
theorem h260 : Model (fun x => f260 ((107/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(1074425282909289/12500000000000),(420255125859/4000000000000),(1330260481/6250000000000),(-767299/2500000000000)⟩
def e261 : ℝ := (24718629/50000000000000)
theorem h261 : Model (fun x => f261 ((107/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(10194262173601539/100000000000000),(40409825697387/100000000000000),(13205797603/12500000000000),(-26665601/100000000000000)⟩
def e262 : ℝ := (95220147/50000000000000)
theorem h262 : Model (fun x => f262 ((107/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7731654896324579/50000000000000),(40409825697387/100000000000000),(13205797603/12500000000000),(-26665601/100000000000000)⟩
def e263 : ℝ := (38088059/20000000000000)
theorem h263 : Model (fun x => f263 ((107/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(18339692462262459/100000000000000),(98207651139553/100000000000000),(339883083161/100000000000000),(320613487/100000000000000)⟩
def e264 : ℝ := (23174227/5000000000000)
theorem h264 : Model (fun x => f264 ((107/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(2584425843497093/12500000000000),(98207651139553/100000000000000),(339883083161/100000000000000),(320613487/100000000000000)⟩
def e265 : ℝ := (463484541/100000000000000)
theorem h265 : Model (fun x => f265 ((107/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(24521309239392703/100000000000000),(45926122192951/25000000000000),(833667641619/100000000000000),(867369369/50000000000000)⟩
def e266 : ℝ := (108778877/12500000000000)
theorem h266 : Model (fun x => f266 ((107/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(4984738038354731/20000000000000),(45926122192951/25000000000000),(833667641619/100000000000000),(867369369/50000000000000)⟩
def e267 : ℝ := (870231017/100000000000000)
theorem h267 : Model (fun x => f267 ((107/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(29559830286729799/100000000000000),(298918754906033/100000000000000),(107510098343/6250000000000),(2710065081/50000000000000)⟩
def e268 : ℝ := (1426300229/100000000000000)
theorem h268 : Model (fun x => f268 ((107/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(29542211239110751/100000000000000),(298918754906033/100000000000000),(107510098343/6250000000000),(2710065081/50000000000000)⟩
def e269 : ℝ := (142630023/10000000000000)
theorem h269 : Model (fun x => f269 ((107/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(35037458089214481/100000000000000),(450582167117167/100000000000000),(3171036088973/100000000000000),(3307773597/25000000000000)⟩
def e270 : ℝ := (135948423/6250000000000)
theorem h270 : Model (fun x => f270 ((107/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(17520395711273907/50000000000000),(450582167117167/100000000000000),(3171036088973/100000000000000),(3307773597/25000000000000)⟩
def e271 : ℝ := (2175174769/100000000000000)
theorem h271 : Model (fun x => f271 ((107/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(6518056388242583/100000000000000),(39550843916319/20000000000000),(2243491204477/100000000000000),(3680829021/25000000000000)⟩
def e272 : ℝ := (1008164883/100000000000000)
theorem h272 : Model (fun x => f272 ((107/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(17582847005123/12500000000000),(15425935947/2000000000000),(2333378333/100000000000000),(297517/100000000000000)⟩
def e273 : ℝ := (3640859/100000000000000)
theorem h273 : Model (fun x => f273 ((107/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(218601338964189/100000000000000),(325163612859/100000000000000),(268981909/50000000000000),(-674741/50000000000000)⟩
def e274 : ℝ := (1528231/100000000000000)
theorem h274 : Model (fun x => f274 ((107/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(238932726984681/50000000000000),(355406005767/25000000000000),(3409305969/100000000000000),(-2401447/100000000000000)⟩
def e275 : ℝ := (6697321/100000000000000)
theorem h275 : Model (fun x => f275 ((107/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(41784811232973/4000000000000),(932306744839/20000000000000),(14646135773/100000000000000),(7035341/100000000000000)⟩
def e276 : ℝ := (10997813/50000000000000)
theorem h276 : Model (fun x => f276 ((107/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(456710784194689/20000000000000),(13586900183143/100000000000000),(13198484881/25000000000000),(14796731/20000000000000)⟩
def e277 : ℝ := (16057243/25000000000000)
theorem h277 : Model (fun x => f277 ((107/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(642422067526797/20000000000000),(7344937846751/20000000000000),(232340699301/100000000000000),(835093173/100000000000000)⟩
def e278 : ℝ := (176325561/100000000000000)
theorem h278 : Model (fun x => f278 ((107/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(118601338964189/12500000000000),(325163612859/12500000000000),(268981909/6250000000000),(-674741/6250000000000)⟩
def e279 : ℝ := (1528231/12500000000000)
theorem h279 : Model (fun x => f279 ((107/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(4255755811541/390625000000),(1686302850111/50000000000000),(6637088877/100000000000000),(-10498339/100000000000000)⟩
def e280 : ℝ := (15866707/100000000000000)
theorem h280 : Model (fun x => f280 ((107/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(4646380811541/390625000000),(1686302850111/50000000000000),(6637088877/100000000000000),(-10498339/100000000000000)⟩
def e281 : ℝ := (15866707/100000000000000)
theorem h281 : Model (fun x => f281 ((107/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(19103600431788839/50000000000000),(545162258240209/100000000000000),(4215400599871/100000000000000),(19869379591/100000000000000)⟩
def e282 : ℝ := (664646287/25000000000000)
theorem h282 : Model (fun x => f282 ((107/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(261730767341/100000000000000),(-1867262361/50000000000000),(1525599/6250000000000),(-18093/25000000000000)⟩
def e283 : ℝ := (19037/100000000000000)
theorem h283 : Model (fun x => f283 ((107/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (37657800676772859/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(8529879500333/50000000000000),(274165209147/100000000000000),(38878487/50000000000000),(-1694551/100000000000000)⟩
def e284 : ℝ := (2051407/50000000000000)
theorem h284 : Model (fun x => f284 ((107/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(68601338964189/25000000000000),(325163612859/25000000000000),(1075927637/50000000000000),(-2698963/50000000000000)⟩
def e285 : ℝ := (152823/2500000000000)
theorem h285 : Model (fun x => f285 ((107/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(16467984401/39062500000),(-23116536017/20000000000000),(31415711/25000000000000),(329717/50000000000000)⟩
def e286 : ℝ := (549923/100000000000000)
theorem h286 : Model (fun x => f286 ((107/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (591378172549/250000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(115683919866877/100000000000000),(231165360167/100000000000000),(-251325691/100000000000000),(-1318871/100000000000000)⟩
def e287 : ℝ := (2058937/50000000000000)
theorem h287 : Model (fun x => f287 ((107/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(15683919866877/100000000000000),(231165360167/100000000000000),(-251325691/100000000000000),(-1318871/100000000000000)⟩
def e288 : ℝ := (2058937/50000000000000)
theorem h288 : Model (fun x => f288 ((107/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(85385750377933/20000000000000),(853110257759/100000000000000),(-927511479/100000000000000),(-4867263/100000000000000)⟩
def e289 : ℝ := (7598459/50000000000000)
theorem h289 : Model (fun x => f289 ((107/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(55652860752079/2000000000000),(853110257759/100000000000000),(-927511479/100000000000000),(-4867263/100000000000000)⟩
def e290 : ℝ := (15196919/100000000000000)
theorem h290 : Model (fun x => f290 ((107/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(643814108360597/20000000000000),(7419418187001/100000000000000),(-6094383079/100000000000000),(-11654571/25000000000000)⟩
def e291 : ℝ := (66128331/50000000000000)
theorem h291 : Model (fun x => f291 ((107/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8501451494183937/100000000000000),(7419418187001/100000000000000),(-6094383079/100000000000000),(-11654571/25000000000000)⟩
def e292 : ℝ := (132256663/100000000000000)
theorem h292 : Model (fun x => f292 ((107/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9834812334053163/100000000000000),(28235484755991/100000000000000),(-11265428177/100000000000000),(-49697011/25000000000000)⟩
def e293 : ℝ := (251940551/50000000000000)
theorem h293 : Model (fun x => f293 ((107/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(7551929976550391/50000000000000),(28235484755991/100000000000000),(-11265428177/100000000000000),(-49697011/25000000000000)⟩
def e294 : ℝ := (503881103/100000000000000)
theorem h294 : Model (fun x => f294 ((107/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8736368622475217/50000000000000),(67578807818849/100000000000000),(14278490731/100000000000000),(-263085513/50000000000000)⟩
def e295 : ℝ := (1208000859/100000000000000)
theorem h295 : Model (fun x => f295 ((107/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(19808451530664719/100000000000000),(67578807818849/100000000000000),(14278490731/100000000000000),(-263085513/50000000000000)⟩
def e296 : ℝ := (60400043/5000000000000)
theorem h296 : Model (fun x => f296 ((107/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(1432199574725209/6250000000000),(61984046104257/50000000000000),(6147649229/5000000000000),(-1006779173/100000000000000)⟩
def e297 : ℝ := (444174691/20000000000000)
theorem h297 : Model (fun x => f297 ((107/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(2914696768498037/12500000000000),(61984046104257/50000000000000),(6147649229/5000000000000),(-1006779173/100000000000000)⟩
def e298 : ℝ := (138804591/6250000000000)
theorem h298 : Model (fun x => f298 ((107/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(1348734189612689/5000000000000),(49328325678097/25000000000000),(370205064649/100000000000000),(-149954929/10000000000000)⟩
def e299 : ℝ := (177195179/5000000000000)
theorem h299 : Model (fun x => f299 ((107/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(6739266186158683/25000000000000),(49328325678097/25000000000000),(370205064649/100000000000000),(-149954929/10000000000000)⟩
def e300 : ℝ := (3543903581/100000000000000)
theorem h300 : Model (fun x => f300 ((107/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(15592494588822697/50000000000000),(290575158803873/100000000000000),(816637707961/100000000000000),(-1730379459/100000000000000)⟩
def e301 : ℝ := (2616563319/50000000000000)
theorem h301 : Model (fun x => f301 ((107/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(31188322510978727/100000000000000),(290575158803873/100000000000000),(816637707961/100000000000000),(-1730379459/100000000000000)⟩
def e302 : ℝ := (5233126639/100000000000000)
theorem h302 : Model (fun x => f302 ((107/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(611443938805633/12500000000000),(117670173122399/100000000000000),(360702824531/50000000000000),(118692101/25000000000000)⟩
def e303 : ℝ := (2139056259/100000000000000)
theorem h303 : Model (fun x => f303 ((107/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(6691384657883/5000000000000),(534842300031/100000000000000),(-9422517/20000000000000),(-21067/500000000000)⟩
def e304 : ℝ := (955197/10000000000000)
theorem h304 : Model (fun x => f304 ((107/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(215683919866877/100000000000000),(231165360167/100000000000000),(-251325691/100000000000000),(-1318871/100000000000000)⟩
def e305 : ℝ := (2058937/50000000000000)
theorem h305 : Model (fun x => f305 ((107/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(232597766445707/50000000000000),(199434604073/20000000000000),(-549763967/100000000000000),(-3425571/50000000000000)⟩
def e306 : ℝ := (8893859/50000000000000)
theorem h306 : Model (fun x => f306 ((107/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(62709497524113/6250000000000),(3226112787267/100000000000000),(-24894879/50000000000000),(-24689157/100000000000000)⟩
def e307 : ℝ := (28815649/50000000000000)
theorem h307 : Model (fun x => f307 ((107/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(432813767644253/20000000000000),(289925271621/3125000000000),(2414292747/50000000000000),(-74706607/100000000000000)⟩
def e308 : ℝ := (41495999/25000000000000)
theorem h308 : Model (fun x => f308 ((107/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(724030851133823/25000000000000),(23990365241123/100000000000000),(55063011523/100000000000000),(-169704609/100000000000000)⟩
def e309 : ℝ := (431411189/100000000000000)
theorem h309 : Model (fun x => f309 ((107/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(115683919866877/12500000000000),(231165360167/12500000000000),(-251325691/12500000000000),(-1318871/12500000000000)⟩
def e310 : ℝ := (2058937/6250000000000)
theorem h310 : Model (fun x => f310 ((107/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(264824763023169/25000000000000),(2384165181367/100000000000000),(-2057718113/100000000000000),(-922773/6250000000000)⟩
def e311 : ℝ := (21247481/50000000000000)
theorem h311 : Model (fun x => f311 ((107/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(289824763023169/25000000000000),(2384165181367/100000000000000),(-2057718113/100000000000000),(-922773/6250000000000)⟩
def e312 : ℝ := (21247481/50000000000000)
theorem h312 : Model (fun x => f312 ((107/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(524605174628309/1562500000000),(17358422132713/5000000000000),(1150720849731/100000000000000),(-98489949/6250000000000)⟩
def e313 : ℝ := (782661373/12500000000000)
theorem h313 : Model (fun x => f313 ((107/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(148921519989/50000000000000),(-3079747797/100000000000000),(21637017/100000000000000),(-52099/50000000000000)⟩
def e314 : ℝ := (3557/6250000000000)
theorem h314 : Model (fun x => f314 ((107/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (33226404175577617/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(14569145720799/100000000000000),(199824970893/100000000000000),(-416902217/100000000000000),(-219997/50000000000000)⟩
def e315 : ℝ := (9308143/100000000000000)
theorem h315 : Model (fun x => f315 ((107/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(6325780944293/20000000000000),(11849754501/2500000000000),(-339145243/100000000000000),(-426909/20000000000000)⟩
def e316 : ℝ := (13410957/100000000000000)
theorem h316 : Model (fun x => f316 ((107/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(65162660556949/50000000000000),(28141658837/2000000000000),(-1229282329/10000000000000),(-63555941/100000000000000)⟩
def e317 : ℝ := (56337727/100000000000000)
theorem h317 : Model (fun x => f317 ((107/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(24359873105401/50000000000000),(70687583767/100000000000000),(-164252487/3125000000000),(396297/1562500000000)⟩
def e318 : ℝ := (5562303/25000000000000)
theorem h318 : Model (fun x => f318 ((107/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-23162673782149/20000000000000),(-175538096339/50000000000000),(4103161501/100000000000000),(-82461877/100000000000000)⟩
def e319 : ℝ := (19005639/50000000000000)
theorem h319 : Model (fun x => f319 ((107/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((107/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-125939/1600),(-1177/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((107/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((107/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(10379/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((107/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(289221/1600),(763/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((107/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((107/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(462021/1600),(763/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((107/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2310105/32),(3815/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((107/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((107/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(109025909358350039/10000000000000),(594745005101989/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (140913/100000000000000)
theorem h329 : Model (fun x => f329 ((107/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(1834426341/20000000000000),(-5003471/50000000000000),(1979/500000000000),(-213/25000000000000)⟩
def e330 : ℝ := (1/5000000000000)
theorem h330 : Model (fun x => f330 ((107/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (544511926978689211/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(165535838377961/25000000000000),(1464571192507/100000000000000),(10422479617/100000000000000),(3129153/6250000000000)⟩
def e331 : ℝ := (583379/25000000000000)
theorem h331 : Model (fun x => f331 ((107/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((107/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(467/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((107/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((107/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((107/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(785806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((107/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((107/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((107/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3486224710489627/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1087/100000000000000)
theorem h339 : Model (fun x => f339 ((107/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3884193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((107/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((107/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((107/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1094387644755057/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1087/100000000000000)
theorem h343 : Model (fun x => f343 ((107/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(571095628679/12500000000000),(-5881227621/100000000000000),(7570719/100000000000000),(-4873/50000000000000)⟩
def e344 : ℝ := (17/100000000000000)
theorem h344 : Model (fun x => f344 ((107/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1092978873937273/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(159277415420267/100000000000000),(202107897467/25000000000000),(-65041787/6250000000000),(334901/25000000000000)⟩
def e345 : ℝ := (281/10000000000000)
theorem h345 : Model (fun x => f345 ((107/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(259277415420267/100000000000000),(202107897467/25000000000000),(-65041787/6250000000000),(334901/25000000000000)⟩
def e346 : ℝ := (281/10000000000000)
theorem h346 : Model (fun x => f346 ((107/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(129638707710133/100000000000000),(202107897467/50000000000000),(-65041787/12500000000000),(334901/50000000000000)⟩
def e347 : ℝ := (703/50000000000000)
theorem h347 : Model (fun x => f347 ((107/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(29638707710133/100000000000000),(202107897467/50000000000000),(-65041787/12500000000000),(334901/50000000000000)⟩
def e348 : ℝ := (703/50000000000000)
theorem h348 : Model (fun x => f348 ((107/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(478428564168347/100000000000000),(745874383509/50000000000000),(-1920281331/100000000000000),(154493/6250000000000)⟩
def e349 : ℝ := (5191/100000000000000)
theorem h349 : Model (fun x => f349 ((107/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(354267856235329/12500000000000),(745874383509/50000000000000),(-1920281331/100000000000000),(154493/6250000000000)⟩
def e350 : ℝ := (649/12500000000000)
theorem h350 : Model (fun x => f350 ((107/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1837073082623489/50000000000000),(6694968437031/50000000000000),(-11206561011/100000000000000),(1665877/25000000000000)⟩
def e351 : ℝ := (4789/6250000000000)
theorem h351 : Model (fun x => f351 ((107/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(895652711762793/10000000000000),(6694968437031/50000000000000),(-11206561011/100000000000000),(1665877/25000000000000)⟩
def e352 : ℝ := (613/800000000000)
theorem h352 : Model (fun x => f352 ((107/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1451390751375059/12500000000000),(10712447682747/20000000000000),(-7007683421/100000000000000),(-46341641/100000000000000)⟩
def e353 : ℝ := (50101/12500000000000)
theorem h353 : Model (fun x => f353 ((107/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(16880173630048091/100000000000000),(10712447682747/20000000000000),(-7007683421/100000000000000),(-46341641/100000000000000)⟩
def e354 : ℝ := (400809/100000000000000)
theorem h354 : Model (fun x => f354 ((107/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(170962804322039/781250000000),(34417430431281/25000000000000),(119589024939/100000000000000),(-7938807/3125000000000)⟩
def e355 : ℝ := (120927/12500000000000)
theorem h355 : Model (fun x => f355 ((107/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(24218953238935277/100000000000000),(34417430431281/25000000000000),(119589024939/100000000000000),(-7938807/3125000000000)⟩
def e356 : ℝ := (967417/100000000000000)
theorem h356 : Model (fun x => f356 ((107/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(7849284499969273/25000000000000),(138185041256021/50000000000000),(292748453357/50000000000000),(-80012511/20000000000000)⟩
def e357 : ℝ := (291209/12500000000000)
theorem h357 : Model (fun x => f357 ((107/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(7949879738064511/25000000000000),(138185041256021/50000000000000),(292748453357/50000000000000),(-80012511/20000000000000)⟩
def e358 : ℝ := (2329673/100000000000000)
theorem h358 : Model (fun x => f358 ((107/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(41224485427746153/100000000000000),(486821281784097/100000000000000),(1710698346461/100000000000000),(31149027/5000000000000)⟩
def e359 : ℝ := (1259823/20000000000000)
theorem h359 : Model (fun x => f359 ((107/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(8241373276025421/20000000000000),(486821281784097/100000000000000),(1710698346461/100000000000000),(31149027/5000000000000)⟩
def e360 : ℝ := (1574779/25000000000000)
theorem h360 : Model (fun x => f360 ((107/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(1335501226575951/2500000000000),(79767348106863/10000000000000),(3971122285159/100000000000000),(5465443167/100000000000000)⟩
def e361 : ℝ := (11908473/100000000000000)
theorem h361 : Model (fun x => f361 ((107/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(53423382396371373/100000000000000),(79767348106863/10000000000000),(3971122285159/100000000000000),(5465443167/100000000000000)⟩
def e362 : ℝ := (5954237/50000000000000)
theorem h362 : Model (fun x => f362 ((107/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(15834000157327157/100000000000000),(452365861369297/100000000000000),(4123331348697/100000000000000),(13879052429/100000000000000)⟩
def e363 : ℝ := (5556953/50000000000000)
theorem h363 : Model (fun x => f363 ((107/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(42015486341883/25000000000000),(41921610633/4000000000000),(142397387/50000000000000),(-1234951/50000000000000)⟩
def e364 : ℝ := (11789/100000000000000)
theorem h364 : Model (fun x => f364 ((107/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(229638707710133/100000000000000),(202107897467/50000000000000),(-65041787/12500000000000),(334901/50000000000000)⟩
def e365 : ℝ := (703/50000000000000)
theorem h365 : Model (fun x => f365 ((107/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(263669680393899/50000000000000),(1856471855693/100000000000000),(-377936909/50000000000000),(-565149/50000000000000)⟩
def e366 : ℝ := (14601/100000000000000)
theorem h366 : Model (fun x => f366 ((107/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(48439011734399/4000000000000),(799345870953/12500000000000),(3024446051/100000000000000),(-5889347/50000000000000)⟩
def e367 : ℝ := (5283/10000000000000)
theorem h367 : Model (fun x => f367 ((107/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1390434007180419/50000000000000),(3915962726807/20000000000000),(26492837191/100000000000000),(-39986181/100000000000000)⟩
def e368 : ℝ := (159249/100000000000000)
theorem h368 : Model (fun x => f368 ((107/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(4673580883038283/100000000000000),(31025416111323/50000000000000),(257648475201/100000000000000),(98765809/50000000000000)⟩
def e369 : ℝ := (1427449/100000000000000)
theorem h369 : Model (fun x => f369 ((107/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(129638707710133/12500000000000),(202107897467/6250000000000),(-65041787/1562500000000),(334901/6250000000000)⟩
def e370 : ℝ := (703/6250000000000)
theorem h370 : Model (fun x => f370 ((107/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(301292901762149/25000000000000),(4281766625297/100000000000000),(-1938939797/50000000000000),(1444257/50000000000000)⟩
def e371 : ℝ := (23037/100000000000000)
theorem h371 : Model (fun x => f371 ((107/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(326292901762149/25000000000000),(4281766625297/100000000000000),(-1938939797/50000000000000),(1444257/50000000000000)⟩
def e372 : ℝ := (23037/100000000000000)
theorem h372 : Model (fun x => f372 ((107/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(30499125358933361/50000000000000),(100998167056353/10000000000000),(1459597682443/25000000000000),(2834693373/25000000000000)⟩
def e373 : ℝ := (501049/2500000000000)
theorem h373 : Model (fun x => f373 ((107/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(163939127471/100000000000000),(-2714430527/100000000000000),(14626521/50000000000000),(-15939/6250000000000)⟩
def e374 : ℝ := (2037/100000000000000)
theorem h374 : Model (fun x => f374 ((107/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (3748901206109873/6250000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(12979060850839/50000000000000),(311801712189/100000000000000),(-887476883/100000000000000),(2778507/100000000000000)⟩
def e375 : ℝ := (136207/20000000000000)
theorem h375 : Model (fun x => f375 ((107/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(159277415420267/50000000000000),(202107897467/12500000000000),(-65041787/3125000000000),(334901/12500000000000)⟩
def e376 : ℝ := (281/5000000000000)
theorem h376 : Model (fun x => f376 ((107/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(2410545473029/6250000000000),(-30064494527/25000000000000),(529770831/100000000000000),(-233379/10000000000000)⟩
def e377 : ℝ := (10491/100000000000000)
theorem h377 : Model (fun x => f377 ((107/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (258467941819393/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(61431272431533/50000000000000),(60128989053/25000000000000),(-1059541663/100000000000000),(4667579/100000000000000)⟩
def e378 : ℝ := (21953/25000000000000)
theorem h378 : Model (fun x => f378 ((107/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(11431272431533/50000000000000),(60128989053/25000000000000),(-1059541663/100000000000000),(4667579/100000000000000)⟩
def e379 : ℝ := (21953/25000000000000)
theorem h379 : Model (fun x => f379 ((107/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(453421296518457/100000000000000),(88761840983/10000000000000),(-3910213281/100000000000000),(17225589/100000000000000)⟩
def e380 : ℝ := (32407/10000000000000)
theorem h380 : Model (fun x => f380 ((107/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1404567791116371/50000000000000),(88761840983/10000000000000),(-3910213281/100000000000000),(17225589/100000000000000)⟩
def e381 : ℝ := (324071/100000000000000)
theorem h381 : Model (fun x => f381 ((107/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(862843866246263/25000000000000),(245217808559/3125000000000),(-6486657101/20000000000000),(26694609/20000000000000)⟩
def e382 : ℝ := (1495573/50000000000000)
theorem h382 : Model (fun x => f382 ((107/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2183439104341501/25000000000000),(245217808559/3125000000000),(-6486657101/20000000000000),(26694609/20000000000000)⟩
def e383 : ℝ := (2991147/100000000000000)
theorem h383 : Model (fun x => f383 ((107/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2682628849129303/25000000000000),(30647064642151/100000000000000),(-28378233329/25000000000000),(205247109/50000000000000)⟩
def e384 : ℝ := (12392299/100000000000000)
theorem h384 : Model (fun x => f384 ((107/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(15999563015564831/100000000000000),(30647064642151/100000000000000),(-28378233329/25000000000000),(205247109/50000000000000)⟩
def e385 : ℝ := (123923/1000000000000)
theorem h385 : Model (fun x => f385 ((107/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(3931494057578571/20000000000000),(38067632760901/50000000000000),(-117637917047/50000000000000),(2613603/400000000000)⟩
def e386 : ℝ := (8240537/25000000000000)
theorem h386 : Model (fun x => f386 ((107/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(1099659228680357/5000000000000),(38067632760901/50000000000000),(-117637917047/50000000000000),(2613603/400000000000)⟩
def e387 : ℝ := (32962149/100000000000000)
theorem h387 : Model (fun x => f387 ((107/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(27021386263564983/100000000000000),(146438842937019/100000000000000),(-33897536891/10000000000000),(456773273/100000000000000)⟩
def e388 : ℝ := (33796737/50000000000000)
theorem h388 : Model (fun x => f388 ((107/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(5484753443189187/20000000000000),(146438842937019/100000000000000),(-33897536891/10000000000000),(456773273/100000000000000)⟩
def e389 : ℝ := (2703739/4000000000000)
theorem h389 : Model (fun x => f389 ((107/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(842338457470859/2500000000000),(49175405009847/20000000000000),(-88707805141/25000000000000),(-105128227/20000000000000)⟩
def e390 : ℝ := (23793327/20000000000000)
theorem h390 : Model (fun x => f390 ((107/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(2104744953200957/6250000000000),(49175405009847/20000000000000),(-88707805141/25000000000000),(-105128227/20000000000000)⟩
def e391 : ℝ := (29741659/25000000000000)
theorem h391 : Model (fun x => f391 ((107/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(10343772849518573/25000000000000),(383086729409329/100000000000000),(-50347896129/25000000000000),(-633140291/25000000000000)⟩
def e392 : ℝ := (95111707/50000000000000)
theorem h392 : Model (fun x => f392 ((107/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(331027397851261/800000000000),(383086729409329/100000000000000),(-50347896129/25000000000000),(-633140291/25000000000000)⟩
def e393 : ℝ := (38044683/20000000000000)
theorem h393 : Model (fun x => f393 ((107/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(1892032183569613/20000000000000),(187105089283867/100000000000000),(436919819477/100000000000000),(-797744917/25000000000000)⟩
def e394 : ℝ := (94562297/100000000000000)
theorem h394 : Model (fun x => f394 ((107/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(150952049302289/100000000000000),(591008049207/100000000000000),(-2025080451/100000000000000),(6372679/100000000000000)⟩
def e395 : ℝ := (12499/5000000000000)
theorem h395 : Model (fun x => f395 ((107/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(111431272431533/50000000000000),(60128989053/25000000000000),(-1059541663/100000000000000),(4667579/100000000000000)⟩
def e396 : ℝ := (21953/25000000000000)
theorem h396 : Model (fun x => f396 ((107/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(496677139028421/100000000000000),(1072039961631/100000000000000),(-4144163777/100000000000000),(15707837/100000000000000)⟩
def e397 : ℝ := (106401/25000000000000)
theorem h397 : Model (fun x => f397 ((107/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1106907311791807/100000000000000),(179188165533/5000000000000),(-11919862911/100000000000000),(36863597/100000000000000)⟩
def e398 : ℝ := (759359/50000000000000)
theorem h398 : Model (fun x => f398 ((107/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2466881804334573/100000000000000),(5324577410671/50000000000000),(-7418382843/25000000000000),(13436057/20000000000000)⟩
def e399 : ℝ := (4746663/100000000000000)
theorem h399 : Model (fun x => f399 ((107/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3723808637508321/100000000000000),(30654587464229/100000000000000),(-31811782709/100000000000000),(-33102609/25000000000000)⟩
def e400 : ℝ := (15066589/100000000000000)
theorem h400 : Model (fun x => f400 ((107/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(61431272431533/6250000000000),(60128989053/3125000000000),(-1059541663/12500000000000),(4667579/12500000000000)⟩
def e401 : ℝ := (21953/3125000000000)
theorem h401 : Model (fun x => f401 ((107/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1133852408206817/100000000000000),(2515135698903/100000000000000),(-2100282751/20000000000000),(43713311/100000000000000)⟩
def e402 : ℝ := (238119/25000000000000)
theorem h402 : Model (fun x => f402 ((107/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1233852408206817/100000000000000),(2515135698903/100000000000000),(-2100282751/20000000000000),(43713311/100000000000000)⟩
def e403 : ℝ := (238119/25000000000000)
theorem h403 : Model (fun x => f403 ((107/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(45946302550909879/100000000000000),(471891206054059/100000000000000),(-6279263427/50000000000000),(-4025223871/100000000000000)⟩
def e404 : ℝ := (58862813/25000000000000)
theorem h404 : Model (fun x => f404 ((107/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(21764536959/10000000000000),(-17882603/800000000000),(2877173/12500000000000),(-27243/12500000000000)⟩
def e405 : ℝ := (3213/100000000000000)
theorem h405 : Model (fun x => f405 ((107/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (45474394525653843/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(20589602193459/100000000000000),(195760185581/100000000000000),(-526995109/50000000000000),(1434311/25000000000000)⟩
def e406 : ℝ := (755511/100000000000000)
theorem h406 : Model (fun x => f406 ((107/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(46547723895137/100000000000000),(50756189777/10000000000000),(-1941467101/100000000000000),(8515751/100000000000000)⟩
def e407 : ℝ := (718273/50000000000000)
theorem h407 : Model (fun x => f407 ((107/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(154106329991347/50000000000000),(2021255962989/50000000000000),(-142565749/25000000000000),(52078819/50000000000000)⟩
def e408 : ℝ := (10807851/100000000000000)
theorem h408 : Model (fun x => f408 ((107/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(115219685974837/100000000000000),(217199958243/50000000000000),(-2136497367/50000000000000),(78871963/100000000000000)⟩
def e409 : ℝ := (6597117/100000000000000)
theorem h409 : Model (fun x => f409 ((107/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-148420733977/25000000000000),(2603866369/3125000000000),(-169833233/100000000000000),(-1794957/50000000000000)⟩
def e410 : ℝ := (8921679/20000000000000)
theorem h410 : Model (fun x => f410 ((107/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(18817091159179687/100000000000000),(207862520751953/25000000000000),(1499819/10240000),(13161/10240000)⟩
def e411 : ℝ := (562500001/100000000000000)
theorem h411 : Model (fun x => f411 ((107/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(51529/1600),(227/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((107/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(11697083/64000),(154587/64000),(681/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((107/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(3439141829804547043/100000000000000),(197412785973802763/100000000000000),(4885455106423521/100000000000000),(68009242541381/100000000000000)⟩
def e414 : ℝ := (146263421323/25000000000000)
theorem h414 : Model (fun x => f414 ((107/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(2907702123/100000000000000),(-166907213/100000000000000),(2725123/50000000000000),(-26651/20000000000000)⟩
def e415 : ℝ := (507/12500000000000)
theorem h415 : Model (fun x => f415 ((107/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (1618387497214047043/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5500638400103/100000000000000),(-16369433073/100000000000000),(-79856473/50000000000000),(411697/10000000000000)⟩
def e416 : ℝ := (1460571/10000000000000)
theorem h416 : Model (fun x => f416 ((107/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(981391092839/20000000000000),(13390858147/20000000000000),(-329546179/100000000000000),(32941/6250000000000)⟩
def e417 : ℝ := (11842821/20000000000000)
theorem h417 : Model (fun x => f417 ((107/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((107/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((14720359204091/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (53/20) (27/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (53/20) (27/10) ≤ (14720714488721/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(107/40)-(1/40)) (by norm_num : ((107/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel33

