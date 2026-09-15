import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel16
open Hf4Quad.Dag

def p0 : Cubic := ⟨(73/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((73/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((73/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((73/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((73/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(319809523809523/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((73/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-319809523809523/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((73/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-28547619047619/12500000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((73/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((73/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(5329/1600),(73/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((73/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(40319947089947/10000000000000),(69041005291/625000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (3/100000000000000)
theorem h9 : Model (fun x => f9 ((73/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-40319947089947/10000000000000),(-69041005291/625000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (3/100000000000000)
theorem h10 : Model (fun x => f10 ((73/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-315790211640211/50000000000000),(-1928439153439/12500000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (3/50000000000000)
theorem h11 : Model (fun x => f11 ((73/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((73/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(389017/64000),(15987/64000),(219/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((73/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(236877133912037/4000000000000),(243366918402777/100000000000000),(3333793402777/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/25000000000000)
theorem h14 : Model (fun x => f14 ((73/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-236877133912037/4000000000000),(-243366918402777/100000000000000),(-3333793402777/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/25000000000000)
theorem h15 : Model (fun x => f15 ((73/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-6553508771081347/100000000000000),(-258794431630289/100000000000000),(-1704727389219/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/10000000000000)
theorem h16 : Model (fun x => f16 ((73/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((73/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(28398241/2560000),(389017/640000),(15987/1280000),(73/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((73/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(3099014394841269/100000000000000),(169809007936507/100000000000000),(872306547619/25000000000000),(6373015873/20000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((73/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1727247188120039/50000000000000),(-44492711846891/50000000000000),(39885706019/50000000000000),(416056961/2500000000000)⟩
def e20 : ℝ := (109126997/100000000000000)
theorem h20 : Model (fun x => f20 ((73/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((73/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1012241988769531/50000000000000),(34665821533203/25000000000000),(389017/10240000),(5329/10240000)⟩
def e22 : ℝ := (89355469/25000000000000)
theorem h22 : Model (fun x => f22 ((73/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(13189138209226703/100000000000000),(903365630768949/100000000000000),(12374871654369/50000000000000),(339037579571/100000000000000)⟩
def e23 : ℝ := (291067167/12500000000000)
theorem h23 : Model (fun x => f23 ((73/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(77877150663893/800000000000),(814380207075167/100000000000000),(3103689340097/12500000000000),(355679858011/100000000000000)⟩
def e24 : ℝ := (2437664333/100000000000000)
theorem h24 : Model (fun x => f24 ((73/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((73/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(923670814752197/25000000000000),(151836298315429/50000000000000),(259993661499/2500000000000),(189949707031/100000000000000)⟩
def e26 : ℝ := (1962255863/100000000000000)
theorem h26 : Model (fun x => f26 ((73/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(8296421032398569/100000000000000),(681897619101249/100000000000000),(5838164547099/25000000000000),(8530651393/2000000000000)⟩
def e27 : ℝ := (2203125367/50000000000000)
theorem h27 : Model (fun x => f27 ((73/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(9015532432692597/50000000000000),(46758682068013/3125000000000),(12045543227293/25000000000000),(782212427661/100000000000000)⟩
def e28 : ℝ := (6843915067/100000000000000)
theorem h28 : Model (fun x => f28 ((73/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((73/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(3371398473845519/50000000000000),(129313914065307/20000000000000),(13285676102599/50000000000000),(60665187683/10000000000000)⟩
def e30 : ℝ := (1047364503/12500000000000)
theorem h30 : Model (fun x => f30 ((73/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1600076418539381/100000000000000),(149835923183/97656250000),(6305424055043/100000000000000),(143959453311/100000000000000)⟩
def e31 : ℝ := (1988330073/100000000000000)
theorem h31 : Model (fun x => f31 ((73/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(785245651356983/4000000000000),(51553431609869/3125000000000),(10897519392843/20000000000000),(231542970243/25000000000000)⟩
def e32 : ℝ := (441612257/5000000000000)
theorem h32 : Model (fun x => f32 ((73/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((73/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2286141/320),(31317/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((73/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((73/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(161257/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((73/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(4866253/320),(48989/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((73/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((73/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(5595853/320),(48989/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((73/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-5595853/320),(-48989/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((73/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((73/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(113/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((73/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(12769/1600),(113/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((73/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((73/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(268149/160),(2373/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((73/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(59668318733/100000000000000),(-528038219/50000000000000),(14018713/100000000000000),(-165413/100000000000000)⟩
def e46 : ℝ := (939/50000000000000)
theorem h46 : Model (fun x => f46 ((73/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (131691/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-52171115685471/5000000000000),(99165579671/50000000000000),(-1787839661/100000000000000),(3223851/20000000000000)⟩
def e47 : ℝ := (65492471/100000000000000)
theorem h47 : Model (fun x => f47 ((73/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((73/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(153/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((73/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((73/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((73/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(63749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((73/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(113749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((73/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((73/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(113749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((73/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((73/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2388749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((73/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((73/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(13749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((73/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(328453124999973/100000000000000),(11156249999981/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (83/100000000000000)
theorem h60 : Model (fun x => f60 ((73/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(129390624999997/100000000000000),(189583333333/20000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((73/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((73/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(113749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((73/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1266890624999987/100000000000000),(204583333333/4000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((73/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1366890624999987/100000000000000),(204583333333/4000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((73/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(4489594973144119/100000000000000),(33858548828067/20000000000000),(26866088867/2500000000000),(64324273/3125000000000)⟩
def e66 : ℝ := (634227/100000000000000)
theorem h66 : Model (fun x => f66 ((73/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(213749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((73/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(91378124999999/20000000000000),(1781249999997/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((73/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(244150927734371/25000000000000),(571113281249/10000000000000),(11132812499/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (47/100000000000000)
theorem h69 : Model (fun x => f69 ((73/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(10961387778447051/25000000000000),(954862976640773/50000000000000),(20663360484443/100000000000000),(50324158089/50000000000000)⟩
def e70 : ℝ := (7999387/3125000000000)
theorem h70 : Model (fun x => f70 ((73/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((73/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2717203124999937/12500000000000),(3981249999993/2500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((73/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(2988923437499713/100000000000000),(28117578124953/25000000000000),(43977864583/6250000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (17/2000000000000)
theorem h73 : Model (fun x => f73 ((73/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(29189937207702407/100000000000000),(1269090632755399/100000000000000),(681395574183/5000000000000),(64791917571/100000000000000)⟩
def e74 : ℝ := (2438651/1562500000000)
theorem h74 : Model (fun x => f74 ((73/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(73035488321490611/100000000000000),(635763317207389/20000000000000),(34291271968103/100000000000000),(165440233749/100000000000000)⟩
def e75 : ℝ := (12876689/3125000000000)
theorem h75 : Model (fun x => f75 ((73/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((73/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(905734374999979/12500000000000),(1327083333331/2500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((73/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(1890624999999/100000000000000),(114583333333/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((73/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(259960937499/100000000000000),(23632812499/100000000000000),(716145833/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((73/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(3767288916001/20000000000000),(37007999673/2000000000000),(8086107039/12500000000000),(927282241/100000000000000)⟩
def e80 : ℝ := (567931/12500000000000)
theorem h80 : Model (fun x => f80 ((73/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(251643126811/625000000000),(4033715150801/100000000000000),(72991215149/50000000000000),(2251602691/100000000000000)⟩
def e81 : ℝ := (13594231/100000000000000)
theorem h81 : Model (fun x => f81 ((73/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(73075751221780371/100000000000000),(1591425150593873/50000000000000),(34437254398401/100000000000000),(4192295911/2500000000000)⟩
def e82 : ℝ := (425648279/100000000000000)
theorem h82 : Model (fun x => f82 ((73/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(17872314453/50000000000000),(4332682291/100000000000000),(24617513/12500000000000),(3978587/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((73/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(2457443237/50000000000000),(93084971/12500000000000),(45132107/100000000000000),(1367639/100000000000000)⟩
def e84 : ℝ := (417/2000000000000)
theorem h84 : Model (fun x => f84 ((73/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(67579689/10000000000000),(122872161/100000000000000),(9308497/100000000000000),(3761/1000000000000)⟩
def e85 : ℝ := (1731/20000000000000)
theorem h85 : Model (fun x => f85 ((73/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(11615259/12500000000000),(9855371/50000000000000),(358377/20000000000000),(90499/100000000000000)⟩
def e86 : ℝ := (559/20000000000000)
theorem h86 : Model (fun x => f86 ((73/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(34845777/12500000000000),(29566113/50000000000000),(1075131/20000000000000),(271497/100000000000000)⟩
def e87 : ℝ := (1677/20000000000000)
theorem h87 : Model (fun x => f87 ((73/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-34845777/12500000000000),(-29566113/50000000000000),(-1075131/20000000000000),(-271497/100000000000000)⟩
def e88 : ℝ := (1677/20000000000000)
theorem h88 : Model (fun x => f88 ((73/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(14615150188602831/20000000000000),(19892814012847/625000000000),(17218624511373/50000000000000),(167691564943/100000000000000)⟩
def e89 : ℝ := (53207083/12500000000000)
theorem h89 : Model (fun x => f89 ((73/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2717203124999937/10000000000000),(3981249999993/2000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((73/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1043745216064431/50000000000000),(4069182128899/25000000000000),(9518554687/20000000000000),(61848957/100000000000000)⟩
def e91 : ℝ := (15137/50000000000000)
theorem h91 : Model (fun x => f91 ((73/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(567213552558801271/100000000000000),(8578128400184513/100000000000000),(52943428171783/100000000000000),(85443610959/50000000000000)⟩
def e92 : ℝ := (305180673/100000000000000)
theorem h92 : Model (fun x => f92 ((73/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(3526008839/20000000000000),(-53324813/20000000000000),(47733/2000000000000),(-16519/100000000000000)⟩
def e93 : ℝ := (61/50000000000000)
theorem h93 : Model (fun x => f93 ((73/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (34911394346127649/6250000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(12883287187081/100000000000000),(366300366641/100000000000000),(-670880067/100000000000000),(327643/20000000000000)⟩
def e94 : ℝ := (20123/6250000000000)
theorem h94 : Model (fun x => f94 ((73/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(63749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((73/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(10989010989011/25000000000000),(-161011150023/100000000000000),(36861527/6250000000000),(-2160383/100000000000000)⟩
def e96 : ℝ := (3973/50000000000000)
theorem h96 : Model (fun x => f96 ((73/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (11333333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(11208791208791/10000000000000),(322022300041/100000000000000),(-589784433/50000000000000),(4320763/100000000000000)⟩
def e97 : ℝ := (56409/100000000000000)
theorem h97 : Model (fun x => f97 ((73/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(235384615384611/10000000000000),(6762468300861/100000000000000),(-12385473093/50000000000000),(90736023/100000000000000)⟩
def e98 : ℝ := (1184589/100000000000000)
theorem h98 : Model (fun x => f98 ((73/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1208791208791/10000000000000),(322022300041/100000000000000),(-589784433/50000000000000),(4320763/100000000000000)⟩
def e99 : ℝ := (56409/100000000000000)
theorem h99 : Model (fun x => f99 ((73/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(8891589180049/3125000000000),(4198675373611/50000000000000),(-8982870621/100000000000000),(-46863737/100000000000000)⟩
def e100 : ℝ := (589337/25000000000000)
theorem h100 : Model (fun x => f100 ((73/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(12563700036227/10000000000000),(360948072573/50000000000000),(-160732461/10000000000000),(522289/25000000000000)⟩
def e101 : ℝ := (84333/50000000000000)
theorem h101 : Model (fun x => f101 ((73/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(11208791208791/1000000000000),(322022300041/10000000000000),(-589784433/5000000000000),(4320763/10000000000000)⟩
def e102 : ℝ := (56409/10000000000000)
theorem h102 : Model (fun x => f102 ((73/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(124651612124137/10000000000000),(985529786389/25000000000000),(-1340301327/10000000000000),(22648393/50000000000000)⟩
def e103 : ℝ := (183189/25000000000000)
theorem h103 : Model (fun x => f103 ((73/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(134651612124137/10000000000000),(985529786389/25000000000000),(-1340301327/10000000000000),(22648393/50000000000000)⟩
def e104 : ℝ := (183189/25000000000000)
theorem h104 : Model (fun x => f104 ((73/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(191562690790261/5000000000000),(4971529073187/4000000000000),(21492757797/12500000000000),(-99087897/5000000000000)⟩
def e105 : ℝ := (742887/2000000000000)
theorem h105 : Model (fun x => f105 ((73/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(21208791208791/10000000000000),(322022300041/100000000000000),(-589784433/50000000000000),(4320763/100000000000000)⟩
def e106 : ℝ := (56409/100000000000000)
theorem h106 : Model (fun x => f106 ((73/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(44981282453809/10000000000000),(341485186307/25000000000000),(-1983231171/50000000000000),(5365341/50000000000000)⟩
def e107 : ℝ := (70371/25000000000000)
theorem h107 : Model (fun x => f107 ((73/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(953998627866489/100000000000000),(4345492810369/100000000000000),(-4659802697/50000000000000),(166359/1250000000000)⟩
def e108 : ℝ := (993073/100000000000000)
theorem h108 : Model (fun x => f108 ((73/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(365501088328643/1000000000000),(338048709416873/25000000000000),(1336840627907/20000000000000),(-11253747523/50000000000000)⟩
def e109 : ℝ := (481065449/100000000000000)
theorem h109 : Model (fun x => f109 ((73/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(263837700760767/1250000000000),(7579909524033/6250000000000),(-3375381681/1250000000000),(10968069/3125000000000)⟩
def e110 : ℝ := (1770993/6250000000000)
theorem h110 : Model (fun x => f110 ((73/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(510279509163593/20000000000000),(4131467169147/5000000000000),(108931140231/100000000000000),(-672856253/50000000000000)⟩
def e111 : ℝ := (2506303/10000000000000)
theorem h111 : Model (fun x => f111 ((73/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(24340297578522661/100000000000000),(899153599005787/100000000000000),(4392073575781/100000000000000),(-15465654363/100000000000000)⟩
def e112 : ℝ := (324124297/100000000000000)
theorem h112 : Model (fun x => f112 ((73/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(60890406411386961/100000000000000),(2251348436673279/100000000000000),(2769069178829/25000000000000),(-37973149409/100000000000000)⟩
def e113 : ℝ := (402594873/50000000000000)
theorem h113 : Model (fun x => f113 ((73/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(87945900253589/1250000000000),(2526636508011/6250000000000),(-1125127227/1250000000000),(3656023/3125000000000)⟩
def e114 : ℝ := (590331/6250000000000)
theorem h114 : Model (fun x => f114 ((73/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(29223523729/2000000000000),(9731443133/12500000000000),(375906561/50000000000000),(-655237/10000000000000)⟩
def e115 : ℝ := (6981/12500000000000)
theorem h115 : Model (fun x => f115 ((73/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(176625692867/100000000000000),(14115939489/100000000000000),(64868453/20000000000000),(386891/50000000000000)⟩
def e116 : ℝ := (17259/50000000000000)
theorem h116 : Model (fun x => f116 ((73/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(12426804453681/100000000000000),(266138558211/25000000000000),(886475393/3125000000000),(173060821/100000000000000)⟩
def e117 : ℝ := (2498311/100000000000000)
theorem h117 : Model (fun x => f117 ((73/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(26355750105059/100000000000000),(459561585401/20000000000000),(63444948179/100000000000000),(223184807/50000000000000)⟩
def e118 : ℝ := (5583823/100000000000000)
theorem h118 : Model (fun x => f118 ((73/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(3045838108074601/5000000000000),(563411561150071/25000000000000),(2227944332699/20000000000000),(-7505355959/20000000000000)⟩
def e119 : ℝ := (810773569/100000000000000)
theorem h119 : Model (fun x => f119 ((73/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(10675179239/50000000000000),(1137548237/50000000000000),(82579259/100000000000000),(122389/12500000000000)⟩
def e120 : ℝ := (5123/100000000000000)
theorem h120 : Model (fun x => f120 ((73/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(2580812563/100000000000000),(343764577/100000000000000),(2132073/12500000000000),(358363/100000000000000)⟩
def e121 : ℝ := (367/12500000000000)
theorem h121 : Model (fun x => f121 ((73/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(311966353/100000000000000),(49864751/100000000000000),(3138341/100000000000000),(94301/100000000000000)⟩
def e122 : ℝ := (67/5000000000000)
theorem h122 : Model (fun x => f122 ((73/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(18855109/50000000000000),(439513/6250000000000),(107251/20000000000000),(2093/10000000000000)⟩
def e123 : ℝ := (439/100000000000000)
theorem h123 : Model (fun x => f123 ((73/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(56565327/50000000000000),(1318539/6250000000000),(321753/20000000000000),(6279/10000000000000)⟩
def e124 : ℝ := (1317/100000000000000)
theorem h124 : Model (fun x => f124 ((73/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-56565327/50000000000000),(-1318539/6250000000000),(-321753/20000000000000),(-6279/10000000000000)⟩
def e125 : ℝ := (1317/100000000000000)
theorem h125 : Model (fun x => f125 ((73/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(30458381024180683/50000000000000),(112682311175183/5000000000000),(1113972005473/10000000000000),(-7505368517/20000000000000)⟩
def e126 : ℝ := (405387443/50000000000000)
theorem h126 : Model (fun x => f126 ((73/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(263837700760767/1000000000000),(7579909524033/5000000000000),(-3375381681/1000000000000),(10968069/2500000000000)⟩
def e127 : ℝ := (1770993/5000000000000)
theorem h127 : Model (fun x => f127 ((73/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1011657885594673/50000000000000),(12288353295257/100000000000000),(-4256342849/25000000000000),(-5911541/50000000000000)⟩
def e128 : ℝ := (2921/97656250000)
theorem h128 : Model (fun x => f128 ((73/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(266913490491797591/50000000000000),(6309440976389461/100000000000000),(730752340281/10000000000000),(-30765332769/50000000000000)⟩
def e129 : ℝ := (1608214929/100000000000000)
theorem h129 : Model (fun x => f129 ((73/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(36587229/195312500000),(-221406233/100000000000000),(590107/25000000000000),(-22709/100000000000000)⟩
def e130 : ℝ := (137/50000000000000)
theorem h130 : Model (fun x => f130 ((73/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (131877542336230611/25000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(11411330677769/100000000000000),(14364720233/5000000000000),(-1465050879/100000000000000),(3834149/50000000000000)⟩
def e131 : ℝ := (495987/100000000000000)
theorem h131 : Model (fun x => f131 ((73/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(485892357297/2000000000000),(653594771301/100000000000000),(-1067965473/50000000000000),(9306513/100000000000000)⟩
def e132 : ℝ := (163591/20000000000000)
theorem h132 : Model (fun x => f132 ((73/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-6337386595807/2500000000000),(-1692892471931/25000000000000),(23148713369/100000000000000),(-54555783/50000000000000)⟩
def e133 : ℝ := (12519741/50000000000000)
theorem h133 : Model (fun x => f133 ((73/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(10958904109589/20000000000000),(-18765246763/2500000000000),(10282326993/100000000000000),(-28170759/20000000000000)⟩
def e134 : ℝ := (391261/20000000000000)
theorem h134 : Model (fun x => f134 ((73/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (9/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-17362703002211/12500000000000),(-903843640351/50000000000000),(18723532983/50000000000000),(-114552133/20000000000000)⟩
def e135 : ℝ := (15892059/50000000000000)
theorem h135 : Model (fun x => f135 ((73/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(28398241/256000),(389017/64000),(15987/128000),(73/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((73/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((73/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(3501153/32000),(143883/32000),(1971/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((73/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(11281493/51200),(676783/64000),(23871/128000),(91/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((73/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-5329/1600),(-73/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((73/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(2222193/10240),(670943/64000),(23791/128000),(91/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((73/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((73/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(219/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((73/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-219/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((73/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(422013/2048),(661343/64000),(23791/128000),(91/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((73/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(428157/2048),(661343/64000),(23791/128000),(91/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((73/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((73/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(428157/32),(661343/1000),(23791/2000),(91/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((73/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((73/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(5367267549/512000),(73524213/128000),(3021543/256000),(13797/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((73/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(2384826149/25000000000000),(-261350811/50000000000000),(895037/5000000000000),(-7663/1562500000000)⟩
def e151 : ℝ := (13583/100000000000000)
theorem h151 : Model (fun x => f151 ((73/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (2533536117/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(63817500592337/50000000000000),(-684946379651/100000000000000),(1824990507/25000000000000),(-14625103/20000000000000)⟩
def e152 : ℝ := (44578271/12500000000000)
theorem h152 : Model (fun x => f152 ((73/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(193/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((73/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(29529/1600),(173/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((73/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(339/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((73/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(5899705014749/100000000000000),(-13052444723/25000000000000),(462033441/100000000000000),(-511099/12500000000000)⟩
def e156 : ℝ := (36509/100000000000000)
theorem h156 : Model (fun x => f156 ((73/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (84/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(108882743362827/100000000000000),(2497976871/800000000000),(924066873/100000000000000),(-8177593/100000000000000)⟩
def e157 : ℝ := (1279703/100000000000000)
theorem h157 : Model (fun x => f157 ((73/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(208882743362827/100000000000000),(2497976871/800000000000),(924066873/100000000000000),(-8177593/100000000000000)⟩
def e158 : ℝ := (1279703/100000000000000)
theorem h158 : Model (fun x => f158 ((73/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(104441371681413/100000000000000),(156123554437/100000000000000),(115508359/25000000000000),(-4088797/100000000000000)⟩
def e159 : ℝ := (319927/50000000000000)
theorem h159 : Model (fun x => f159 ((73/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(4441371681413/100000000000000),(156123554437/100000000000000),(115508359/25000000000000),(-4088797/100000000000000)⟩
def e160 : ℝ := (319927/50000000000000)
theorem h160 : Model (fun x => f160 ((73/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((73/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((73/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(24089899718183/6250000000000),(288085130211/50000000000000),(852561697/50000000000000),(-1886201/12500000000000)⟩
def e163 : ℝ := (295171/12500000000000)
theorem h163 : Model (fun x => f163 ((73/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2741152681205213/100000000000000),(288085130211/50000000000000),(852561697/50000000000000),(-1886201/12500000000000)⟩
def e164 : ℝ := (2361369/100000000000000)
theorem h164 : Model (fun x => f164 ((73/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((73/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1431448730066277/50000000000000),(4881345121647/100000000000000),(1534543367/10000000000000),(-30628941/25000000000000)⟩
def e166 : ℝ := (10026199/50000000000000)
theorem h166 : Model (fun x => f166 ((73/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4072639206256753/50000000000000),(4881345121647/100000000000000),(1534543367/10000000000000),(-30628941/25000000000000)⟩
def e167 : ℝ := (20052399/100000000000000)
theorem h167 : Model (fun x => f167 ((73/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((73/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8507040501299127/100000000000000),(17814841977957/100000000000000),(15320455161/25000000000000),(-414489761/100000000000000)⟩
def e169 : ℝ := (73444787/100000000000000)
theorem h169 : Model (fun x => f169 ((73/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(6888044060173373/50000000000000),(17814841977957/100000000000000),(15320455161/25000000000000),(-414489761/100000000000000)⟩
def e170 : ℝ := (18361197/25000000000000)
theorem h170 : Model (fun x => f170 ((73/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((73/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(7193967698465163/50000000000000),(40113783760513/100000000000000),(77733435937/50000000000000),(-818189187/100000000000000)⟩
def e172 : ℝ := (41544953/25000000000000)
theorem h172 : Model (fun x => f172 ((73/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(16723649682644611/100000000000000),(40113783760513/100000000000000),(77733435937/50000000000000),(-818189187/100000000000000)⟩
def e173 : ℝ := (166179813/100000000000000)
theorem h173 : Model (fun x => f173 ((73/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((73/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(17466409123748303/100000000000000),(17001235577233/25000000000000),(151133825887/50000000000000),(-1110264597/100000000000000)⟩
def e175 : ℝ := (283294731/100000000000000)
theorem h175 : Model (fun x => f175 ((73/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(3573758015225851/20000000000000),(17001235577233/25000000000000),(151133825887/50000000000000),(-1110264597/100000000000000)⟩
def e176 : ℝ := (70823683/25000000000000)
theorem h176 : Model (fun x => f176 ((73/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((73/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(4665602364595399/25000000000000),(98922684760341/100000000000000),(504423999547/100000000000000),(-552038777/50000000000000)⟩
def e178 : ℝ := (82845337/20000000000000)
theorem h178 : Model (fun x => f178 ((73/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(4661197602690637/25000000000000),(98922684760341/100000000000000),(504423999547/100000000000000),(-552038777/50000000000000)⟩
def e179 : ℝ := (207113343/50000000000000)
theorem h179 : Model (fun x => f179 ((73/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((73/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(9736437426062481/50000000000000),(132425118374391/100000000000000),(767414121579/100000000000000),(-41930051/6250000000000)⟩
def e181 : ℝ := (556671943/100000000000000)
theorem h181 : Model (fun x => f181 ((73/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(3895241637091659/20000000000000),(132425118374391/100000000000000),(767414121579/100000000000000),(-41930051/6250000000000)⟩
def e182 : ℝ := (69583993/12500000000000)
theorem h182 : Model (fun x => f182 ((73/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(173002158992397/20000000000000),(7257688039049/20000000000000),(33081710913/10000000000000),(983823601/100000000000000)⟩
def e183 : ℝ := (77008949/50000000000000)
theorem h183 : Model (fun x => f183 ((73/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(2181600023739/2000000000000),(326115163543/100000000000000),(604426879/50000000000000),(-3549053/50000000000000)⟩
def e184 : ℝ := (674611/50000000000000)
theorem h184 : Model (fun x => f184 ((73/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(204441371681413/100000000000000),(156123554437/100000000000000),(115508359/25000000000000),(-4088797/100000000000000)⟩
def e185 : ℝ := (319927/50000000000000)
theorem h185 : Model (fun x => f185 ((73/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(26122671534361/6250000000000),(638362272417/100000000000000),(213292063/10000000000000),(-152757/1000000000000)⟩
def e186 : ℝ := (262893/10000000000000)
theorem h186 : Model (fun x => f186 ((73/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(427244384037421/50000000000000),(1957614879039/100000000000000),(1822083423/25000000000000),(-42040061/100000000000000)⟩
def e187 : ℝ := (2024361/25000000000000)
theorem h187 : Model (fun x => f187 ((73/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(873464279157907/50000000000000),(533623294793/10000000000000),(21904691119/100000000000000),(-25115487/25000000000000)⟩
def e188 : ℝ := (11079879/50000000000000)
theorem h188 : Model (fun x => f188 ((73/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(952774846073029/50000000000000),(11517761887871/100000000000000),(243803569/390625000000),(-24410241/25000000000000)⟩
def e189 : ℝ := (6041377/12500000000000)
theorem h189 : Model (fun x => f189 ((73/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((73/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(104441371681413/12500000000000),(156123554437/12500000000000),(115508359/3125000000000),(-4088797/12500000000000)⟩
def e191 : ℝ := (319927/6250000000000)
theorem h191 : Model (fun x => f191 ((73/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(472305487319127/50000000000000),(1575103599039/100000000000000),(2452560623/50000000000000),(-19904241/50000000000000)⟩
def e192 : ℝ := (3234027/50000000000000)
theorem h192 : Model (fun x => f192 ((73/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(522305487319127/50000000000000),(1575103599039/100000000000000),(2452560623/50000000000000),(-19904241/50000000000000)⟩
def e193 : ℝ := (3234027/50000000000000)
theorem h193 : Model (fun x => f193 ((73/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(3981116242268637/20000000000000),(150330186495871/100000000000000),(11585833843/1250000000000),(-230497797/100000000000000)⟩
def e194 : ℝ := (158181739/25000000000000)
theorem h194 : Model (fun x => f194 ((73/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(15699114569/3125000000000),(-3793992523/100000000000000),(5260837/100000000000000),(71373/50000000000000)⟩
def e195 : ℝ := (11/62500000000)
theorem h195 : Model (fun x => f195 ((73/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (19754323294915121/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(4345569143529/100000000000000),(29896879353/20000000000000),(330657523/100000000000000),(-2232441/50000000000000)⟩
def e196 : ℝ := (970687/100000000000000)
theorem h196 : Model (fun x => f196 ((73/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(108882743362827/50000000000000),(2497976871/400000000000),(924066873/50000000000000),(-8177593/50000000000000)⟩
def e197 : ℝ := (1279703/50000000000000)
theorem h197 : Model (fun x => f197 ((73/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(957474977493/2000000000000),(-35781892359/50000000000000),(-10480981/10000000000000),(2347481/100000000000000)⟩
def e198 : ℝ := (18753/6250000000000)
theorem h198 : Model (fun x => f198 ((73/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (208569562729783/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(52126251125349/50000000000000),(143127569431/100000000000000),(209619617/100000000000000),(-4694963/100000000000000)⟩
def e199 : ℝ := (190689/10000000000000)
theorem h199 : Model (fun x => f199 ((73/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(2126251125349/50000000000000),(143127569431/100000000000000),(209619617/100000000000000),(-4694963/100000000000000)⟩
def e200 : ℝ := (190689/10000000000000)
theorem h200 : Model (fun x => f200 ((73/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(192370688676883/50000000000000),(105641777437/20000000000000),(154719241/20000000000000),(-346533/2000000000000)⟩
def e201 : ℝ := (1407467/20000000000000)
theorem h201 : Model (fun x => f201 ((73/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2740455663068051/100000000000000),(105641777437/20000000000000),(154719241/20000000000000),(-346533/2000000000000)⟩
def e202 : ℝ := (879667/12500000000000)
theorem h202 : Model (fun x => f202 ((73/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(14284968009097/500000000000),(1118254640971/25000000000000),(7307038607/100000000000000),(-144512387/100000000000000)⟩
def e203 : ℝ := (29831151/50000000000000)
theorem h203 : Model (fun x => f203 ((73/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(254355454818761/3125000000000),(1118254640971/25000000000000),(7307038607/100000000000000),(-144512387/100000000000000)⟩
def e204 : ℝ := (59662303/100000000000000)
theorem h204 : Model (fun x => f204 ((73/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4242750820155231/50000000000000),(16312922745299/100000000000000),(6216323821/20000000000000),(-512963693/100000000000000)⟩
def e205 : ℝ := (43596301/20000000000000)
theorem h205 : Model (fun x => f205 ((73/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13754549259358081/100000000000000),(16312922745299/100000000000000),(6216323821/20000000000000),(-512963693/100000000000000)⟩
def e206 : ℝ := (108990753/50000000000000)
theorem h206 : Model (fun x => f206 ((73/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(896216361011603/6250000000000),(18346591096653/50000000000000),(84583888963/100000000000000),(-137733379/12500000000000)⟩
def e207 : ℝ := (491596919/100000000000000)
theorem h207 : Model (fun x => f207 ((73/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16675176061899933/100000000000000),(18346591096653/50000000000000),(84583888963/100000000000000),(-137733379/12500000000000)⟩
def e208 : ℝ := (12289923/2500000000000)
theorem h208 : Model (fun x => f208 ((73/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(17384288299240081/100000000000000),(31060167393833/50000000000000),(4391333019/2500000000000),(-1733638327/100000000000000)⟩
def e209 : ℝ := (835014199/100000000000000)
theorem h209 : Model (fun x => f209 ((73/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(17786669251621033/100000000000000),(31060167393833/50000000000000),(4391333019/2500000000000),(-1733638327/100000000000000)⟩
def e210 : ℝ := (4175071/500000000000)
theorem h210 : Model (fun x => f210 ((73/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(9271523880935213/50000000000000),(22554907701307/25000000000000),(61863731089/20000000000000),(-113040707/5000000000000)⟩
def e211 : ℝ := (1217121907/100000000000000)
theorem h211 : Model (fun x => f211 ((73/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(9262714357125689/50000000000000),(22554907701307/25000000000000),(61863731089/20000000000000),(-113040707/5000000000000)⟩
def e212 : ℝ := (304280477/25000000000000)
theorem h212 : Model (fun x => f212 ((73/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(19313222987276371/100000000000000),(30142804620293/25000000000000),(490434535669/100000000000000),(-2594879019/100000000000000)⟩
def e213 : ℝ := (326490639/20000000000000)
theorem h213 : Model (fun x => f213 ((73/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(2414569540076213/12500000000000),(30142804620293/25000000000000),(490434535669/100000000000000),(-2594879019/100000000000000)⟩
def e214 : ℝ := (408113299/25000000000000)
theorem h214 : Model (fun x => f214 ((73/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(410718496145637/50000000000000),(4096826417383/12500000000000),(233917685489/100000000000000),(-7820563/12500000000000)⟩
def e215 : ℝ := (112697369/25000000000000)
theorem h215 : Model (fun x => f215 ((73/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(108685842255317/100000000000000),(74607036271/25000000000000),(641922403/100000000000000),(-4594593/50000000000000)⟩
def e216 : ℝ := (79889/2000000000000)
theorem h216 : Model (fun x => f216 ((73/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(102126251125349/50000000000000),(143127569431/100000000000000),(209619617/100000000000000),(-4694963/100000000000000)⟩
def e217 : ℝ := (190689/10000000000000)
theorem h217 : Model (fun x => f217 ((73/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(417190846756713/100000000000000),(292341641973/50000000000000),(1061161637/100000000000000),(-2322389/12500000000000)⟩
def e218 : ℝ := (780823/10000000000000)
theorem h218 : Model (fun x => f218 ((73/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(852122743661461/100000000000000),(223918169569/12500000000000),(484850753/12500000000000),(-3424427/6250000000000)⟩
def e219 : ℝ := (23978149/100000000000000)
theorem h219 : Model (fun x => f219 ((73/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(348096405235167/20000000000000),(121962257157/2500000000000),(6136341931/50000000000000),(-142611841/100000000000000)⟩
def e220 : ℝ := (8181039/12500000000000)
theorem h220 : Model (fun x => f220 ((73/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1891657549451613/100000000000000),(1312039560403/12500000000000),(19535000969/50000000000000),(-246993747/100000000000000)⟩
def e221 : ℝ := (17730501/12500000000000)
theorem h221 : Model (fun x => f221 ((73/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(52126251125349/6250000000000),(143127569431/12500000000000),(209619617/12500000000000),(-4694963/12500000000000)⟩
def e222 : ℝ := (190689/1250000000000)
theorem h222 : Model (fun x => f222 ((73/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(942705860260901/100000000000000),(360862175133/25000000000000),(2318879339/100000000000000),(-4674889/10000000000000)⟩
def e223 : ℝ := (1924957/10000000000000)
theorem h223 : Model (fun x => f223 ((73/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1042705860260901/100000000000000),(360862175133/25000000000000),(2318879339/100000000000000),(-4674889/10000000000000)⟩
def e224 : ℝ := (1924957/10000000000000)
theorem h224 : Model (fun x => f224 ((73/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(493110603104993/2500000000000),(68375406699091/50000000000000),(602759399771/100000000000000),(-165774677/6250000000000)⟩
def e225 : ℝ := (1854820883/100000000000000)
theorem h225 : Model (fun x => f225 ((73/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(101397130147/20000000000000),(-878741753/25000000000000),(8876519/100000000000000),(891/781250000000)⟩
def e226 : ℝ := (49893/100000000000000)
theorem h226 : Model (fun x => f226 ((73/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (4896766511046513/25000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(832913536149/20000000000000),(137289337269/100000000000000),(106827333/100000000000000),(-2346623/50000000000000)⟩
def e227 : ℝ := (2788239/100000000000000)
theorem h227 : Model (fun x => f227 ((73/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(4255068412137/50000000000000),(143386867017/50000000000000),(54685607/12500000000000),(-572383/6250000000000)⟩
def e228 : ℝ := (1879463/50000000000000)
theorem h228 : Model (fun x => f228 ((73/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(10861913236479/100000000000000),(1230935139/400000000000),(-98078219/12500000000000),(12889/50000000000000)⟩
def e229 : ℝ := (36313459/100000000000000)
theorem h229 : Model (fun x => f229 ((73/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(2975866640131/50000000000000),(87090659037/100000000000000),(-811477323/50000000000000),(1112319/5000000000000)⟩
def e230 : ℝ := (5227027/25000000000000)
theorem h230 : Model (fun x => f230 ((73/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-66474945368713/50000000000000),(-344119324333/20000000000000),(895602783/2500000000000),(-110102857/20000000000000)⟩
def e231 : ℝ := (26346113/50000000000000)
theorem h231 : Model (fun x => f231 ((73/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((73/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-5329/320),(-73/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((73/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1533/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((73/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1387/64),(11/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((73/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((73/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3051/64),(11/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((73/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((73/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(381375/32),(275/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((73/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(12191/1600),(47/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((73/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(21791/1600),(47/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((73/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((73/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4118499/1600),(8883/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((73/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(38849104977/100000000000000),(-41895919/25000000000000),(156607/6250000000000),(-37/200000000000)⟩
def e244 : ℝ := (199/100000000000000)
theorem h244 : Model (fun x => f244 ((73/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (64071/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(92600483816271/20000000000000),(-664769010893/50000000000000),(-3368210383/100000000000000),(-185963/400000000000)⟩
def e245 : ℝ := (4665263/100000000000000)
theorem h245 : Model (fun x => f245 ((73/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(657/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((73/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(57889/1600),(433/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((73/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(91489/1600),(433/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((73/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(23409/1600),(153/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((73/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2141666001/2560000),(12066957/640000),(189947/1280000),(293/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((73/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((73/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(114921/160),(1017/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((73/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(34806519261/25000000000000),(-492835671/20000000000000),(8177583/25000000000000),(-385963/100000000000000)⟩
def e253 : ℝ := (4379/100000000000000)
theorem h253 : Model (fun x => f253 ((73/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (56439/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(23294980910761/20000000000000),(281776042299/50000000000000),(312907831/20000000000000),(-8086237/100000000000000)⟩
def e254 : ℝ := (7395707/100000000000000)
theorem h254 : Model (fun x => f254 ((73/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(43294980910761/20000000000000),(281776042299/50000000000000),(312907831/20000000000000),(-8086237/100000000000000)⟩
def e255 : ℝ := (7395707/100000000000000)
theorem h255 : Model (fun x => f255 ((73/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(54118726138451/50000000000000),(281776042299/100000000000000),(782269577/100000000000000),(-4043119/100000000000000)⟩
def e256 : ℝ := (739571/20000000000000)
theorem h256 : Model (fun x => f256 ((73/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(4118726138451/50000000000000),(281776042299/100000000000000),(782269577/100000000000000),(-4043119/100000000000000)⟩
def e257 : ℝ := (739571/20000000000000)
theorem h257 : Model (fun x => f257 ((73/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(399447740545709/100000000000000),(1039887775151/100000000000000),(180434203/6250000000000),(-2984207/20000000000000)⟩
def e258 : ℝ := (13327/97656250000)
theorem h258 : Model (fun x => f258 ((73/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1377581013129997/50000000000000),(1039887775151/100000000000000),(180434203/6250000000000),(-2984207/20000000000000)⟩
def e259 : ℝ := (13646849/100000000000000)
theorem h259 : Model (fun x => f259 ((73/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2982117183324487/100000000000000),(4444467275441/50000000000000),(5521541419/20000000000000),(-111275177/100000000000000)⟩
def e260 : ℝ := (58395881/50000000000000)
theorem h260 : Model (fun x => f260 ((73/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8264498135705439/100000000000000),(4444467275441/50000000000000),(5521541419/20000000000000),(-111275177/100000000000000)⟩
def e261 : ℝ := (116791763/100000000000000)
theorem h261 : Model (fun x => f261 ((73/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(894528222555963/10000000000000),(32908532055101/100000000000000),(119579421379/100000000000000),(-38407197/12500000000000)⟩
def e262 : ℝ := (6767817/1562500000000)
theorem h262 : Model (fun x => f262 ((73/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14214329844607249/100000000000000),(32908532055101/100000000000000),(119579421379/100000000000000),(-38407197/12500000000000)⟩
def e263 : ℝ := (433140289/100000000000000)
theorem h263 : Model (fun x => f263 ((73/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(15385228482038209/100000000000000),(18917983188407/25000000000000),(3333524563/1000000000000),(-19555653/6250000000000)⟩
def e264 : ℝ := (9981587/1000000000000)
theorem h264 : Model (fun x => f264 ((73/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(8860471383876247/50000000000000),(18917983188407/25000000000000),(3333524563/1000000000000),(-19555653/6250000000000)⟩
def e265 : ℝ := (998158701/100000000000000)
theorem h265 : Model (fun x => f265 ((73/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(9590348485631611/50000000000000),(131838743290261/100000000000000),(28506525083/4000000000000),(476122413/100000000000000)⟩
def e266 : ℝ := (435664183/25000000000000)
theorem h266 : Model (fun x => f266 ((73/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(9791538961822087/50000000000000),(131838743290261/100000000000000),(28506525083/4000000000000),(476122413/100000000000000)⟩
def e267 : ℝ := (1742656733/100000000000000)
theorem h267 : Model (fun x => f267 ((73/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(21196224621952893/100000000000000),(197879318784837/100000000000000),(1296050865959/100000000000000),(2763023959/100000000000000)⟩
def e268 : ℝ := (655449517/25000000000000)
theorem h268 : Model (fun x => f268 ((73/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(4235721114866769/20000000000000),(197879318784837/100000000000000),(1296050865959/100000000000000),(2763023959/100000000000000)⟩
def e269 : ℝ := (2621798069/100000000000000)
theorem h269 : Model (fun x => f269 ((73/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(11461591550716451/50000000000000),(27385576983707/10000000000000),(2126062738767/100000000000000),(7334261059/100000000000000)⟩
def e270 : ℝ := (227853109/6250000000000)
theorem h270 : Model (fun x => f270 ((73/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(4585303286953247/20000000000000),(27385576983707/10000000000000),(2126062738767/100000000000000),(7334261059/100000000000000)⟩
def e271 : ℝ := (729129949/20000000000000)
theorem h271 : Model (fun x => f271 ((73/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(944280425034981/50000000000000),(17432033798957/20000000000000),(140767564559/12500000000000),(3905117863/50000000000000)⟩
def e272 : ℝ := (1194859343/100000000000000)
theorem h272 : Model (fun x => f272 ((73/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(58576730376973/50000000000000),(304987209311/50000000000000),(24873947/1000000000000),(-2171921/50000000000000)⟩
def e273 : ℝ := (8042557/100000000000000)
theorem h273 : Model (fun x => f273 ((73/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(104118726138451/50000000000000),(281776042299/100000000000000),(782269577/100000000000000),(-4043119/100000000000000)⟩
def e274 : ℝ := (739571/20000000000000)
theorem h274 : Model (fun x => f274 ((73/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(1734513461231/400000000000),(58676325161/5000000000000),(2025966927/50000000000000),(-9711/78125000000)⟩
def e275 : ℝ := (15438267/100000000000000)
theorem h275 : Model (fun x => f275 ((73/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(225744165066709/25000000000000),(3665582538149/100000000000000),(756825157/5000000000000),(-11409337/50000000000000)⟩
def e276 : ℝ := (4832141/10000000000000)
theorem h276 : Model (fun x => f276 ((73/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(470083897998679/25000000000000),(2544371896183/25000000000000),(24456156803/50000000000000),(-1269967/10000000000000)⟩
def e277 : ℝ := (5375263/4000000000000)
theorem h277 : Model (fun x => f277 ((73/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2202878219810007/100000000000000),(23392845018729/100000000000000),(166153906707/100000000000000),(454949977/100000000000000)⟩
def e278 : ℝ := (311004771/100000000000000)
theorem h278 : Model (fun x => f278 ((73/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(54118726138451/6250000000000),(281776042299/12500000000000),(782269577/12500000000000),(-4043119/12500000000000)⟩
def e279 : ℝ := (739571/2500000000000)
theorem h279 : Model (fun x => f279 ((73/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(491526539484581/50000000000000),(1432091378507/50000000000000),(2186387829/25000000000000),(-18344397/50000000000000)⟩
def e280 : ℝ := (37625397/100000000000000)
theorem h280 : Model (fun x => f280 ((73/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(541526539484581/50000000000000),(1432091378507/50000000000000),(2186387829/25000000000000),(-18344397/50000000000000)⟩
def e281 : ℝ := (37625397/100000000000000)
theorem h281 : Model (fun x => f281 ((73/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(4771668077118669/20000000000000),(316451386363643/100000000000000),(2662202680961/100000000000000),(2730981273/25000000000000)⟩
def e282 : ℝ := (10584971/250000000000)
theorem h282 : Model (fun x => f282 ((73/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(83828127509/20000000000000),(-222375293/4000000000000),(5393811/20000000000000),(14143/20000000000000)⟩
def e283 : ℝ := (973/1250000000000)
theorem h283 : Model (fun x => f283 ((73/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (23539211638635249/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(494732874213/6250000000000),(130165684957/50000000000000),(15354901/4000000000000),(-314301/6250000000000)⟩
def e284 : ℝ := (3342721/50000000000000)
theorem h284 : Model (fun x => f284 ((73/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(23294980910761/10000000000000),(281776042299/25000000000000),(312907831/10000000000000),(-8086237/50000000000000)⟩
def e285 : ℝ := (7395707/50000000000000)
theorem h285 : Model (fun x => f285 ((73/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(23097365536693/50000000000000),(-120259376243/100000000000000),(-20792449/100000000000000),(52977/2000000000000)⟩
def e286 : ℝ := (1597749/100000000000000)
theorem h286 : Model (fun x => f286 ((73/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (53977443112027/25000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(53805268926613/50000000000000),(60129688121/25000000000000),(162441/390625000000),(-5297703/100000000000000)⟩
def e287 : ℝ := (10639401/100000000000000)
theorem h287 : Model (fun x => f287 ((73/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(3805268926613/50000000000000),(60129688121/25000000000000),(162441/390625000000),(-5297703/100000000000000)⟩
def e288 : ℝ := (10639401/100000000000000)
theorem h288 : Model (fun x => f288 ((73/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(397134127791667/100000000000000),(177525745881/20000000000000),(38367017/25000000000000),(-19551047/100000000000000)⟩
def e289 : ℝ := (19632229/50000000000000)
theorem h289 : Model (fun x => f289 ((73/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(86026512922061/3125000000000),(177525745881/20000000000000),(38367017/25000000000000),(-19551047/100000000000000)⟩
def e290 : ℝ := (39264459/100000000000000)
theorem h290 : Model (fun x => f290 ((73/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(2962354984057753/100000000000000),(473518669487/6250000000000),(3444830509/100000000000000),(-166138481/100000000000000)⟩
def e291 : ℝ := (335422199/100000000000000)
theorem h291 : Model (fun x => f291 ((73/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1648947187287741/20000000000000),(473518669487/6250000000000),(3444830509/100000000000000),(-166138481/100000000000000)⟩
def e292 : ℝ := (1677111/500000000000)
theorem h292 : Model (fun x => f292 ((73/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(8872204685779899/100000000000000),(3497878976631/12500000000000),(25357984649/100000000000000),(-604128077/100000000000000)⟩
def e293 : ℝ := (1240553349/100000000000000)
theorem h293 : Model (fun x => f293 ((73/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(7070626152413759/50000000000000),(3497878976631/12500000000000),(25357984649/100000000000000),(-604128077/100000000000000)⟩
def e294 : ℝ := (24811067/2000000000000)
theorem h294 : Model (fun x => f294 ((73/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1521747766440661/10000000000000),(32062527335423/50000000000000),(100472927757/100000000000000),(-663319799/50000000000000)⟩
def e295 : ℝ := (2848401721/100000000000000)
theorem h295 : Model (fun x => f295 ((73/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3510638390024179/20000000000000),(32062527335423/50000000000000),(100472927757/100000000000000),(-663319799/50000000000000)⟩
def e296 : ℝ := (1424200861/50000000000000)
theorem h296 : Model (fun x => f296 ((73/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(2361135533491783/12500000000000),(4448961381181/4000000000000),(269651716097/100000000000000),(-1044598707/50000000000000)⟩
def e297 : ℝ := (2476486481/50000000000000)
theorem h297 : Model (fun x => f297 ((73/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(1205716576269701/6250000000000),(4448961381181/4000000000000),(269651716097/100000000000000),(-1044598707/50000000000000)⟩
def e298 : ℝ := (4952972963/100000000000000)
theorem h298 : Model (fun x => f298 ((73/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(10379824741674617/50000000000000),(83044186631533/50000000000000),(565710658083/100000000000000),(-643846441/25000000000000)⟩
def e299 : ℝ := (7417015713/100000000000000)
theorem h299 : Model (fun x => f299 ((73/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(10371015217865093/50000000000000),(83044186631533/50000000000000),(565710658083/100000000000000),(-643846441/25000000000000)⟩
def e300 : ℝ := (3708507857/50000000000000)
theorem h300 : Model (fun x => f300 ((73/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(22320610513569089/100000000000000),(28577133077991/12500000000000),(508431758517/50000000000000),(-2440529747/100000000000000)⟩
def e301 : ℝ := (10238682231/100000000000000)
theorem h301 : Model (fun x => f301 ((73/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(11161971923451211/50000000000000),(28577133077991/12500000000000),(508431758517/50000000000000),(-2440529747/100000000000000)⟩
def e302 : ℝ := (1279835279/12500000000000)
theorem h302 : Model (fun x => f302 ((73/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(67958887872057/4000000000000),(1110816554499/1562500000000),(63653908351/10000000000000),(1172423931/100000000000000)⟩
def e303 : ℝ := (1610515003/50000000000000)
theorem h303 : Model (fun x => f303 ((73/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(23160055714121/20000000000000),(517647046371/100000000000000),(667992163/100000000000000),(-2240347/20000000000000)⟩
def e304 : ℝ := (11487449/50000000000000)
theorem h304 : Model (fun x => f304 ((73/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(103805268926613/50000000000000),(60129688121/25000000000000),(162441/390625000000),(-5297703/100000000000000)⟩
def e305 : ℝ := (10639401/100000000000000)
theorem h305 : Model (fun x => f305 ((73/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(431021354277057/100000000000000),(998684551339/100000000000000),(150232391/20000000000000),(-21797141/100000000000000)⟩
def e306 : ℝ := (442537/1000000000000)
theorem h306 : Model (fun x => f306 ((73/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(111855718984607/12500000000000),(1555030776369/50000000000000),(207037739/5000000000000),(-32932703/50000000000000)⟩
def e307 : ℝ := (13805131/10000000000000)
theorem h307 : Model (fun x => f307 ((73/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(464448519607071/25000000000000),(2152271839069/25000000000000),(16449045193/100000000000000),(-172897187/100000000000000)⟩
def e308 : ℝ := (76560093/20000000000000)
theorem h308 : Model (fun x => f308 ((73/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(537832679522039/25000000000000),(19586163315593/100000000000000),(76022645423/100000000000000),(-265664569/100000000000000)⟩
def e309 : ℝ := (875828797/100000000000000)
theorem h309 : Model (fun x => f309 ((73/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(53805268926613/6250000000000),(60129688121/3125000000000),(162441/48828125000),(-5297703/12500000000000)⟩
def e310 : ℝ := (10639401/12500000000000)
theorem h310 : Model (fun x => f310 ((73/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(976684581396413/100000000000000),(2441797066243/100000000000000),(1000671331/100000000000000),(-53583359/100000000000000)⟩
def e311 : ℝ := (54045053/50000000000000)
theorem h311 : Model (fun x => f311 ((73/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1076684581396413/100000000000000),(2441797066243/100000000000000),(1000671331/100000000000000),(-53583359/100000000000000)⟩
def e312 : ℝ := (54045053/50000000000000)
theorem h312 : Model (fun x => f312 ((73/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(5790761534124977/25000000000000),(263412330865571/100000000000000),(1318306212599/100000000000000),(-490203217/25000000000000)⟩
def e313 : ℝ := (2953550823/25000000000000)
theorem h313 : Model (fun x => f313 ((73/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(215861073303/50000000000000),(-4909584701/100000000000000),(31261137/100000000000000),(-19767/50000000000000)⟩
def e314 : ℝ := (113533/50000000000000)
theorem h314 : Model (fun x => f314 ((73/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (11449150862202789/50000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(733483923827/10000000000000),(223508549683/100000000000000),(-8445459/4000000000000),(-927447/20000000000000)⟩
def e315 : ℝ := (9099579/50000000000000)
theorem h315 : Model (fun x => f315 ((73/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(7625282612839/50000000000000),(483839919597/100000000000000),(3454721/2000000000000),(-9666051/100000000000000)⟩
def e316 : ℝ := (124423/500000000000)
theorem h316 : Model (fun x => f316 ((73/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(70610485918469/100000000000000),(1018714234501/50000000000000),(-6146734727/100000000000000),(-7043749/10000000000000)⟩
def e317 : ℝ := (116384557/100000000000000)
theorem h317 : Model (fun x => f317 ((73/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(38690677215599/100000000000000),(58638988417/10000000000000),(-11400811963/100000000000000),(5878981/5000000000000)⟩
def e318 : ℝ := (69054053/100000000000000)
theorem h318 : Model (fun x => f318 ((73/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-94259213521827/100000000000000),(-226841347499/20000000000000),(24423299357/100000000000000),(-86586933/20000000000000)⟩
def e319 : ℝ := (121746279/100000000000000)
theorem h319 : Model (fun x => f319 ((73/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((73/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-58619/1600),(-803/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((73/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((73/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(7081/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((73/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(224621/1600),(1137/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((73/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((73/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(397421/1600),(1137/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((73/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1987105/32),(5685/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((73/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((73/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(498464938699132579/50000000000000),(134389496345161/3125000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (129267/100000000000000)
theorem h329 : Model (fun x => f329 ((73/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(2507698943/25000000000000),(-43269919/100000000000000),(161743/25000000000000),(-4777/100000000000000)⟩
def e330 : ℝ := (53/100000000000000)
theorem h330 : Model (fun x => f330 ((73/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (496291831949656831/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(622882638516251/100000000000000),(87713361041/10000000000000),(3780133587/50000000000000),(7609893/100000000000000)⟩
def e331 : ℝ := (612759/10000000000000)
theorem h331 : Model (fun x => f331 ((73/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((73/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(433/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((73/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((73/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((73/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(615806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((73/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((73/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((73/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2732021126061989/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (209/20000000000000)
theorem h339 : Model (fun x => f339 ((73/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3714193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((73/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((73/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((73/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(261622359242219/12500000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (261/25000000000000)
theorem h343 : Model (fun x => f343 ((73/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4777879091147/100000000000000),(-160798007/2500000000000),(8658569/100000000000000),(-11657/100000000000000)⟩
def e344 : ℝ := (21/100000000000000)
theorem h344 : Model (fun x => f344 ((73/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2090161332302227/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(65266333073917/50000000000000),(884129619287/100000000000000),(-148775513/12500000000000),(1602211/100000000000000)⟩
def e345 : ℝ := (3217/100000000000000)
theorem h345 : Model (fun x => f345 ((73/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(115266333073917/50000000000000),(884129619287/100000000000000),(-148775513/12500000000000),(1602211/100000000000000)⟩
def e346 : ℝ := (3217/100000000000000)
theorem h346 : Model (fun x => f346 ((73/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(115266333073917/100000000000000),(442064809643/100000000000000),(-148775513/25000000000000),(160221/20000000000000)⟩
def e347 : ℝ := (161/10000000000000)
theorem h347 : Model (fun x => f347 ((73/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(15266333073917/100000000000000),(442064809643/100000000000000),(-148775513/25000000000000),(160221/20000000000000)⟩
def e348 : ℝ := (161/10000000000000)
theorem h348 : Model (fun x => f348 ((73/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(106346914443197/25000000000000),(815714827317/50000000000000),(-1098104977/50000000000000),(1478229/50000000000000)⟩
def e349 : ℝ := (1189/20000000000000)
theorem h349 : Model (fun x => f349 ((73/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2781101943487073/100000000000000),(815714827317/50000000000000),(-1098104977/50000000000000),(1478229/50000000000000)⟩
def e350 : ℝ := (2973/50000000000000)
theorem h350 : Model (fun x => f350 ((73/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(801418557326247/25000000000000),(1417476215203/10000000000000),(-5934954509/50000000000000),(1567501/25000000000000)⟩
def e351 : ℝ := (90929/100000000000000)
theorem h351 : Model (fun x => f351 ((73/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(424402759084297/5000000000000),(1417476215203/10000000000000),(-5934954509/50000000000000),(1567501/25000000000000)⟩
def e352 : ℝ := (9093/10000000000000)
theorem h352 : Model (fun x => f352 ((73/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(4891934978609993/50000000000000),(53861433535907/100000000000000),(-1532964101/100000000000000),(-61601553/100000000000000)⟩
def e353 : ℝ := (887/195312500000)
theorem h353 : Model (fun x => f353 ((73/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3010583515253521/20000000000000),(53861433535907/100000000000000),(-1532964101/100000000000000),(-61601553/100000000000000)⟩
def e354 : ℝ := (90829/20000000000000)
theorem h354 : Model (fun x => f354 ((73/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(17350946110802811/100000000000000),(12862775080713/10000000000000),(73377615371/50000000000000),(-277723367/100000000000000)⟩
def e355 : ℝ := (937353/100000000000000)
theorem h355 : Model (fun x => f355 ((73/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(2460832549564637/12500000000000),(12862775080713/10000000000000),(73377615371/50000000000000),(-277723367/100000000000000)⟩
def e356 : ℝ := (468677/50000000000000)
theorem h356 : Model (fun x => f356 ((73/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(4538418308756061/20000000000000),(235292289477761/100000000000000),(310310837417/50000000000000),(-139561937/50000000000000)⟩
def e357 : ℝ := (2477081/100000000000000)
theorem h357 : Model (fun x => f357 ((73/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(23094472496161257/100000000000000),(235292289477761/100000000000000),(310310837417/50000000000000),(-139561937/50000000000000)⟩
def e358 : ℝ := (1238541/50000000000000)
theorem h358 : Model (fun x => f358 ((73/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(26620151589089387/100000000000000),(373305329964891/100000000000000),(101129786169/6250000000000),(603297951/50000000000000)⟩
def e359 : ℝ := (3145383/50000000000000)
theorem h359 : Model (fun x => f359 ((73/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(26602532541470339/100000000000000),(373305329964891/100000000000000),(101129786169/6250000000000),(603297951/50000000000000)⟩
def e360 : ℝ := (6290767/100000000000000)
theorem h360 : Model (fun x => f360 ((73/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(15331881882674179/50000000000000),(136973949964921/25000000000000),(1678518408929/50000000000000),(3267656269/50000000000000)⟩
def e361 : ℝ := (1127977/12500000000000)
theorem h361 : Model (fun x => f361 ((73/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(30667097098681691/100000000000000),(136973949964921/25000000000000),(1678518408929/50000000000000),(3267656269/50000000000000)⟩
def e362 : ℝ := (9023817/100000000000000)
theorem h362 : Model (fun x => f362 ((73/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(4681741187186283/100000000000000),(109606021058451/50000000000000),(688012605649/25000000000000),(6411558749/50000000000000)⟩
def e363 : ℝ := (7616981/50000000000000)
theorem h363 : Model (fun x => f363 ((73/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(132863275403071/100000000000000),(1019103791771/100000000000000),(145577083/25000000000000),(-682933/20000000000000)⟩
def e364 : ℝ := (7181/50000000000000)
theorem h364 : Model (fun x => f364 ((73/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(215266333073917/100000000000000),(442064809643/100000000000000),(-148775513/25000000000000),(160221/20000000000000)⟩
def e365 : ℝ := (161/10000000000000)
theorem h365 : Model (fun x => f365 ((73/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(92679188310181/20000000000000),(1903233411057/100000000000000),(-151973943/25000000000000),(-362491/20000000000000)⟩
def e366 : ℝ := (8791/50000000000000)
theorem h366 : Model (fun x => f366 ((73/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(31172982843437/3125000000000),(614553116073/10000000000000),(4347251461/100000000000000),(-1775349/12500000000000)⟩
def e367 : ℝ := (28139/50000000000000)
theorem h367 : Model (fun x => f367 ((73/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2147357986458499/100000000000000),(8819506385079/50000000000000),(15294522749/50000000000000),(-39937037/100000000000000)⟩
def e368 : ℝ := (88551/50000000000000)
theorem h368 : Model (fun x => f368 ((73/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(570610031087639/20000000000000),(45319576778093/100000000000000),(232905700207/100000000000000),(144030413/50000000000000)⟩
def e369 : ℝ := (1380523/100000000000000)
theorem h369 : Model (fun x => f369 ((73/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(115266333073917/12500000000000),(442064809643/12500000000000),(-148775513/3125000000000),(160221/2500000000000)⟩
def e370 : ℝ := (161/1250000000000)
theorem h370 : Model (fun x => f370 ((73/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1054993939994407/100000000000000),(911124453783/20000000000000),(-1044627021/25000000000000),(119767/4000000000000)⟩
def e371 : ℝ := (13621/50000000000000)
theorem h371 : Model (fun x => f371 ((73/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1154993939994407/100000000000000),(911124453783/20000000000000),(-1044627021/25000000000000),(119767/4000000000000)⟩
def e372 : ℝ := (13621/50000000000000)
theorem h372 : Model (fun x => f372 ((73/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(32952556400312161/100000000000000),(653412553642543/100000000000000),(4635420523787/100000000000000),(12129132163/100000000000000)⟩
def e373 : ℝ := (1346909/6250000000000)
theorem h373 : Model (fun x => f373 ((73/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(303466592349/100000000000000),(-376087819/6250000000000),(1532599/2000000000000),(-784721/100000000000000)⟩
def e374 : ℝ := (7431/100000000000000)
theorem h374 : Model (fun x => f374 ((73/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (8073624068865781/25000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(14207520443353/100000000000000),(95878995269/25000000000000),(-1251707043/100000000000000),(4555327/100000000000000)⟩
def e375 : ℝ := (403177/50000000000000)
theorem h375 : Model (fun x => f375 ((73/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(65266333073917/25000000000000),(884129619287/50000000000000),(-148775513/6250000000000),(1602211/50000000000000)⟩
def e376 : ℝ := (3217/50000000000000)
theorem h376 : Model (fun x => f376 ((73/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(21688900248061/50000000000000),(-166360797709/100000000000000),(107746631/12500000000000),(-4466177/100000000000000)⟩
def e377 : ℝ := (2933/12500000000000)
theorem h377 : Model (fun x => f377 ((73/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (45929468943803/20000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(14155549875969/12500000000000),(166360797707/50000000000000),(-1723946097/100000000000000),(8723/97656250000)⟩
def e378 : ℝ := (169433/100000000000000)
theorem h378 : Model (fun x => f378 ((73/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1655549875969/12500000000000),(166360797707/50000000000000),(-1723946097/100000000000000),(8723/97656250000)⟩
def e379 : ℝ := (169433/100000000000000)
theorem h379 : Model (fun x => f379 ((73/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(208962879121447/50000000000000),(306975281483/25000000000000),(-254487281/4000000000000),(4120579/12500000000000)⟩
def e380 : ℝ := (625291/100000000000000)
theorem h380 : Model (fun x => f380 ((73/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2773640043957179/100000000000000),(306975281483/25000000000000),(-254487281/4000000000000),(4120579/12500000000000)⟩
def e381 : ℝ := (156323/25000000000000)
theorem h381 : Model (fun x => f381 ((73/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(628198399683531/20000000000000),(10619028655767/100000000000000),(-10187076373/20000000000000),(7585787/3125000000000)⟩
def e382 : ℝ := (358871/6250000000000)
theorem h382 : Model (fun x => f382 ((73/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8423372950798607/100000000000000),(10619028655767/100000000000000),(-10187076373/20000000000000),(7585787/3125000000000)⟩
def e383 : ℝ := (5741937/100000000000000)
theorem h383 : Model (fun x => f383 ((73/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2384749518578357/25000000000000),(10012959012813/25000000000000),(-10472754671/6250000000000),(674761301/100000000000000)⟩
def e384 : ℝ := (23454731/100000000000000)
theorem h384 : Model (fun x => f384 ((73/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(14808045693361047/100000000000000),(10012959012813/25000000000000),(-10472754671/6250000000000),(674761301/100000000000000)⟩
def e385 : ℝ := (5863683/25000000000000)
theorem h385 : Model (fun x => f385 ((73/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(838464117512001/5000000000000),(18925205381679/20000000000000),(-311778547259/100000000000000),(419421109/50000000000000)⟩
def e386 : ℝ := (60535503/100000000000000)
theorem h386 : Model (fun x => f386 ((73/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3820999327190861/20000000000000),(18925205381679/20000000000000),(-311778547259/100000000000000),(419421109/50000000000000)⟩
def e387 : ℝ := (3783469/6250000000000)
theorem h387 : Model (fun x => f387 ((73/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(21635338620837689/100000000000000),(170725125088263/100000000000000),(-36759035951/10000000000000),(-12188877/100000000000000)⟩
def e388 : ℝ := (117947179/100000000000000)
theorem h388 : Model (fun x => f388 ((73/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(22037719573218641/100000000000000),(170725125088263/100000000000000),(-36759035951/10000000000000),(-12188877/100000000000000)⟩
def e389 : ℝ := (5897359/5000000000000)
theorem h389 : Model (fun x => f389 ((73/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(12478241542852589/50000000000000),(33332611752289/12500000000000),(-114077269961/50000000000000),(-88463127/4000000000000)⟩
def e390 : ℝ := (96585507/50000000000000)
theorem h390 : Model (fun x => f390 ((73/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(2493886403808613/10000000000000),(33332611752289/12500000000000),(-114077269961/50000000000000),(-88463127/4000000000000)⟩
def e391 : ℝ := (38634203/20000000000000)
theorem h391 : Model (fun x => f391 ((73/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(28241866699291029/100000000000000),(48119439140673/12500000000000),(99466785079/50000000000000),(-5633070793/100000000000000)⟩
def e392 : ℝ := (2207189/781250000000)
theorem h392 : Model (fun x => f392 ((73/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(14122600016312181/50000000000000),(48119439140673/12500000000000),(99466785079/50000000000000),(-5633070793/100000000000000)⟩
def e393 : ℝ := (282520193/100000000000000)
theorem h393 : Model (fun x => f393 ((73/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(935226748214617/25000000000000),(2265045692767/1562500000000),(102530707143/12500000000000),(-2098818139/50000000000000)⟩
def e394 : ℝ := (99201299/100000000000000)
theorem h394 : Model (fun x => f394 ((73/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(128242939066269/100000000000000),(753577142191/100000000000000),(-2797508193/100000000000000),(4379447/50000000000000)⟩
def e395 : ℝ := (9487/2000000000000)
theorem h395 : Model (fun x => f395 ((73/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(26655549875969/12500000000000),(166360797707/50000000000000),(-1723946097/100000000000000),(8723/97656250000)⟩
def e396 : ℝ := (169433/100000000000000)
theorem h396 : Model (fun x => f396 ((73/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(454731737081773/100000000000000),(1419020333019/100000000000000),(-6245400387/100000000000000),(13311799/50000000000000)⟩
def e397 : ℝ := (25413/3125000000000)
theorem h397 : Model (fun x => f397 ((73/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(969689959837537/100000000000000),(567371508927/12500000000000),(-16435909463/100000000000000),(52148629/100000000000000)⟩
def e398 : ℝ := (2833761/100000000000000)
theorem h398 : Model (fun x => f398 ((73/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2067809527094067/100000000000000),(12905471619761/100000000000000),(-36663448281/100000000000000),(32442449/50000000000000)⟩
def e399 : ℝ := (2141919/25000000000000)
theorem h399 : Model (fun x => f399 ((73/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2651819711837749/100000000000000),(32132896045773/100000000000000),(-7612740357/100000000000000),(-372991447/100000000000000)⟩
def e400 : ℝ := (11786161/50000000000000)
theorem h400 : Model (fun x => f400 ((73/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(14155549875969/1562500000000),(166360797707/6250000000000),(-1723946097/12500000000000),(8723/12207031250)⟩
def e401 : ℝ := (169433/12500000000000)
theorem h401 : Model (fun x => f401 ((73/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(206839626225657/20000000000000),(3415349905503/100000000000000),(-16589076969/100000000000000),(8021771/10000000000000)⟩
def e402 : ℝ := (914907/50000000000000)
theorem h402 : Model (fun x => f402 ((73/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(226839626225657/20000000000000),(3415349905503/100000000000000),(-16589076969/100000000000000),(8021771/10000000000000)⟩
def e403 : ℝ := (914907/50000000000000)
theorem h403 : Model (fun x => f403 ((73/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(30076889612555221/100000000000000),(14219363389091/3125000000000),(285597431401/50000000000000),(-7693785553/100000000000000)⟩
def e404 : ℝ := (331633593/100000000000000)
theorem h404 : Model (fun x => f404 ((73/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(332481188341/100000000000000),(-2514978589/50000000000000),(3489087/5000000000000),(-437561/50000000000000)⟩
def e405 : ℝ := (913/6250000000000)
theorem h405 : Model (fun x => f405 ((73/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (29621290763822361/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(12437812024587/100000000000000),(3672605421/1250000000000),(-1953940519/100000000000000),(6602897/50000000000000)⟩
def e406 : ℝ := (698941/50000000000000)
theorem h406 : Model (fun x => f406 ((73/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(1332266623397/5000000000000),(169331103689/25000000000000),(-1602823781/50000000000000),(17761121/100000000000000)⟩
def e407 : ℝ := (551059/25000000000000)
theorem h407 : Model (fun x => f407 ((73/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(165969149917731/100000000000000),(1113162838157/25000000000000),(-12011923699/100000000000000),(135748343/100000000000000)⟩
def e408 : ℝ := (15459849/100000000000000)
theorem h408 : Model (fun x => f408 ((73/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(2273549998873/2500000000000),(1194028139043/100000000000000),(-22938425851/100000000000000),(24287979/6250000000000)⟩
def e409 : ℝ := (20479859/100000000000000)
theorem h409 : Model (fun x => f409 ((73/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3317213566907/100000000000000),(14955350387/25000000000000),(742436753/50000000000000),(-44327001/100000000000000)⟩
def e410 : ℝ := (71113069/50000000000000)
theorem h410 : Model (fun x => f410 ((73/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1566895133300781/50000000000000),(49861798095703/25000000000000),(516913/10240000),(6497/10240000)⟩
def e411 : ℝ := (49560547/12500000000000)
theorem h411 : Model (fun x => f411 ((73/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(37249/1600),(193/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((73/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(7189057/64000),(111747/64000),(579/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((73/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(352015575822559773/100000000000000),(3484431436429543/12500000000000),(471814806680999/50000000000000),(4448578823883/25000000000000)⟩
def e414 : ℝ := (20545313151/10000000000000)
theorem h414 : Model (fun x => f414 ((73/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(7101958469/25000000000000),(-449912589/20000000000000),(4079491/4000000000000),(-1740953/50000000000000)⟩
def e415 : ℝ := (75353/50000000000000)
theorem h415 : Model (fun x => f415 ((73/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (323178494949334389/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(55767820039/1000000000000),(27031942687/100000000000000),(-322249709/20000000000000),(18164387/50000000000000)⟩
def e416 : ℝ := (29281363/50000000000000)
theorem h416 : Model (fun x => f416 ((73/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2259568436993/100000000000000),(17370668847/20000000000000),(-126375039/100000000000000),(-7998227/100000000000000)⟩
def e417 : ℝ := (1568663/781250000000)
theorem h417 : Model (fun x => f417 ((73/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((73/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((564831380779/500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (9/5) (37/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (9/5) (37/20) ≤ (564931775211/500000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(73/40)-(1/40)) (by norm_num : ((73/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel16


noncomputable section
namespace Hf4Quad.Panel17
open Hf4Quad.Dag

def p0 : Cubic := ⟨(15/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((15/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((15/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((15/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((15/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(82142857142857/25000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((15/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-82142857142857/25000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((15/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-237142857142857/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((15/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((15/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(225/64),(3/32),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((15/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(212797619047619/50000000000000),(5674603174603/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/100000000000000)
theorem h9 : Model (fun x => f9 ((15/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-212797619047619/50000000000000),(-5674603174603/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/100000000000000)
theorem h10 : Model (fun x => f10 ((15/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-132547619047619/20000000000000),(-7865079365079/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (3/100000000000000)
theorem h11 : Model (fun x => f11 ((15/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((15/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(3375/512),(135/512),(9/2560),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((15/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(131525/2048),(5261/2048),(3425130208333/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((15/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-131525/2048),(-5261/2048),(-3425130208333/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((15/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1416971447172619/20000000000000),(-136307462177579/50000000000000),(-1750395791997/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/20000000000000)
theorem h16 : Model (fun x => f16 ((15/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((15/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(50625/4096),(675/1024),(27/2048),(3/25600)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((15/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(3452845982142857/100000000000000),(36830357142857/20000000000000),(736607142857/20000000000000),(16369047619/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((15/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1816005626860119/50000000000000),(-88463138640873/100000000000000),(182244130291/100000000000000),(17515294313/100000000000000)⟩
def e20 : ℝ := (109126991/100000000000000)
theorem h20 : Model (fun x => f20 ((15/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((15/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(2317428588867187/100000000000000),(38623809814453/25000000000000),(675/16384),(9/16384)⟩
def e22 : ℝ := (367187501/100000000000000)
theorem h22 : Model (fun x => f22 ((15/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(754880905151367/5000000000000),(62906742095947/6250000000000),(26840209960937/100000000000000),(71573893229/20000000000000)⟩
def e23 : ℝ := (95686343/4000000000000)
theorem h23 : Model (fun x => f23 ((15/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(5732803424653551/50000000000000),(918044734894279/100000000000000),(6755613522807/25000000000000),(187692380229/50000000000000)⟩
def e24 : ℝ := (1250642783/50000000000000)
theorem h24 : Model (fun x => f24 ((15/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((15/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(173807144165039/4000000000000),(347614288330077/100000000000000),(2317428588867/20000000000000),(205993652343/100000000000000)⟩
def e26 : ℝ := (207094727/10000000000000)
theorem h26 : Model (fun x => f26 ((15/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(9757110050746369/100000000000000),(780568804059707/100000000000000),(26018960135321/100000000000000),(115639822823/25000000000000)⟩
def e27 : ℝ := (581289697/12500000000000)
theorem h27 : Model (fun x => f27 ((15/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(21222716900053471/100000000000000),(849306769476993/50000000000000),(53041414226549/100000000000000),(3351776207/400000000000)⟩
def e28 : ℝ := (3575801571/50000000000000)
theorem h28 : Model (fun x => f28 ((15/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((15/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(8147209882736203/100000000000000),(760406255722043/100000000000000),(380203127861/1250000000000),(675916671751/100000000000000)⟩
def e30 : ℝ := (9084641123/100000000000000)
theorem h30 : Model (fun x => f30 ((15/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(1933345837252479/100000000000000),(180445611476897/100000000000000),(288712978363/4000000000000),(16039609909/10000000000000)⟩
def e31 : ℝ := (2155799761/100000000000000)
theorem h31 : Model (fun x => f31 ((15/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(463121254746119/2000000000000),(1879059150430883/100000000000000),(7532404835703/12500000000000),(24958503771/2500000000000)⟩
def e32 : ℝ := (9307402903/100000000000000)
theorem h32 : Model (fun x => f32 ((15/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((15/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(482625/64),(6435/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((15/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((15/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(33135/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((15/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1012785/64),(49847/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((15/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((15/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1158705/64),(49847/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((15/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1158705/64),(-49847/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((15/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((15/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(23/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((15/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(529/64),(23/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((15/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((15/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(55545/32),(483/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((15/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(57610946079/100000000000000),(-500964749/50000000000000),(2613729/20000000000000),(-151521/100000000000000)⟩
def e46 : ℝ := (1691/100000000000000)
theorem h46 : Model (fun x => f46 ((15/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (136437/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-130379084524351/12500000000000),(47842137891/25000000000000),(-847278153/50000000000000),(7504627/50000000000000)⟩
def e47 : ℝ := (61032649/100000000000000)
theorem h47 : Model (fun x => f47 ((15/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((15/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(31/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((15/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((15/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((15/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(25833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((15/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(45833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((15/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((15/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(28645833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((15/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((15/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(601562499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((15/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((15/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(3645833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((15/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(350911458333297/100000000000000),(2260416666663/20000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (11/10000000000000)
theorem h60 : Model (fun x => f60 ((15/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(65646701388887/50000000000000),(954861111109/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((15/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((15/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(28645833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((15/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(638563368055547/50000000000000),(5121527777769/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((15/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(688563368055547/50000000000000),(5121527777769/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((15/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(2416247756392587/50000000000000),(3472320782691/2000000000000),(1087009006069/100000000000000),(2063440393/100000000000000)⟩
def e66 : ℝ := (126933/20000000000000)
theorem h66 : Model (fun x => f66 ((15/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(53645833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((15/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(230230034722219/50000000000000),(1788194444441/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((15/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(19761411313657/2000000000000),(1151150173609/20000000000000),(11176215277/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (61/100000000000000)
theorem h69 : Model (fun x => f69 ((15/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(47748465749774811/100000000000000),(996797691209137/50000000000000),(21273412816601/100000000000000),(51353526311/50000000000000)⟩
def e70 : ℝ := (259431977/100000000000000)
theorem h70 : Model (fun x => f70 ((15/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((15/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1378580729166627/6250000000000),(20052083333289/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((15/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(25130377875431/781250000000),(115299479166463/100000000000000),(355468749997/50000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1169/100000000000000)
theorem h73 : Model (fun x => f73 ((15/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(15891575477248567/50000000000000),(165548098087011/12500000000000),(14020418967621/100000000000000),(16511600003/25000000000000)⟩
def e74 : ℝ := (157945787/100000000000000)
theorem h74 : Model (fun x => f74 ((15/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(15906323340854389/20000000000000),(1658990083557181/50000000000000),(17646915892111/50000000000000),(84376726317/50000000000000)⟩
def e75 : ℝ := (104344441/25000000000000)
theorem h75 : Model (fun x => f75 ((15/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((15/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(459526909722209/6250000000000),(6684027777763/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((15/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(212673611111/10000000000000),(121527777777/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((15/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(310149016203/100000000000000),(6646050347/25000000000000),(759548611/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((15/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(22803491035063/100000000000000),(424085703393/20000000000000),(70361981167/100000000000000),(963853099/100000000000000)⟩
def e80 : ℝ := (2306891/50000000000000)
theorem h80 : Model (fun x => f80 ((15/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(9786498235881/20000000000000),(4645100738633/100000000000000),(9988762713/6250000000000),(2361443029/100000000000000)⟩
def e81 : ℝ := (13935689/100000000000000)
theorem h81 : Model (fun x => f81 ((15/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(1591610983909027/2000000000000),(664525053570599/20000000000000),(3545365198763/10000000000000),(171114895663/100000000000000)⟩
def e82 : ℝ := (431313453/100000000000000)
theorem h82 : Model (fun x => f82 ((15/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(22615032431/50000000000000),(5169150269/100000000000000),(221535011/100000000000000),(2109857/50000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((15/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(52768409/800000000000),(942293017/100000000000000),(10769063/20000000000000),(1538437/100000000000000)⟩
def e84 : ℝ := (22107/100000000000000)
theorem h84 : Model (fun x => f84 ((15/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(480962061/50000000000000),(164901277/100000000000000),(5889331/50000000000000),(44871/10000000000000)⟩
def e85 : ℝ := (973/10000000000000)
theorem h85 : Model (fun x => f85 ((15/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(140280601/100000000000000),(701403/2500000000000),(240481/10000000000000),(57257/50000000000000)⟩
def e86 : ℝ := (3331/100000000000000)
theorem h86 : Model (fun x => f86 ((15/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(420841803/100000000000000),(2104209/2500000000000),(721443/10000000000000),(171771/50000000000000)⟩
def e87 : ℝ := (9993/100000000000000)
theorem h87 : Model (fun x => f87 ((15/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-420841803/100000000000000),(-2104209/2500000000000),(-721443/10000000000000),(-171771/50000000000000)⟩
def e88 : ℝ := (9993/100000000000000)
theorem h88 : Model (fun x => f88 ((15/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(79580548774609547/100000000000000),(664525036736927/20000000000000),(88634111933/250000000000),(171114552121/100000000000000)⟩
def e89 : ℝ := (215661723/50000000000000)
theorem h89 : Model (fun x => f89 ((15/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1378580729166627/5000000000000),(20052083333289/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((15/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2120234755527769/100000000000000),(16467842761351/100000000000000),(9592918113/20000000000000),(15522521/25000000000000)⟩
def e91 : ℝ := (15157/50000000000000)
theorem h91 : Model (fun x => f91 ((15/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(73072869381997423/12500000000000),(8791962536746769/100000000000000),(26988045064883/50000000000000),(10833577839/6250000000000)⟩
def e92 : ℝ := (61613829/20000000000000)
theorem h92 : Model (fun x => f92 ((15/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(17106212067/100000000000000),(-257272599/100000000000000),(457969/20000000000000),(-15757/100000000000000)⟩
def e93 : ℝ := (29/25000000000000)
theorem h93 : Model (fun x => f93 ((15/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (14393421069594707/2500000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(13613217437467/100000000000000),(363636363981/100000000000000),(-82644661/12500000000000),(400541/25000000000000)⟩
def e94 : ℝ := (20297/6250000000000)
theorem h94 : Model (fun x => f94 ((15/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(25833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((15/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(43636363636363/100000000000000),(-158677685951/100000000000000),(577009767/100000000000000),(-1049109/50000000000000)⟩
def e96 : ℝ := (3831/50000000000000)
theorem h96 : Model (fun x => f96 ((15/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (228333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(112727272727269/100000000000000),(317355371899/100000000000000),(-230803907/20000000000000),(262277/6250000000000)⟩
def e97 : ℝ := (54899/100000000000000)
theorem h97 : Model (fun x => f97 ((15/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2367272727272649/100000000000000),(6664462809879/100000000000000),(-4846882047/20000000000000),(5507817/6250000000000)⟩
def e98 : ℝ := (1152879/100000000000000)
theorem h98 : Model (fun x => f98 ((15/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(12727272727269/100000000000000),(317355371899/100000000000000),(-230803907/20000000000000),(262277/6250000000000)⟩
def e99 : ℝ := (54899/100000000000000)
theorem h99 : Model (fun x => f99 ((15/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(37661157024781/12500000000000),(6531930879/78125000000),(-9253138469/100000000000000),(-43261497/100000000000000)⟩
def e100 : ℝ := (573683/25000000000000)
theorem h100 : Model (fun x => f100 ((15/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(794214876033/625000000000),(71549211119/10000000000000),(-1594645177/100000000000000),(53409/2500000000000)⟩
def e101 : ℝ := (6567/4000000000000)
theorem h101 : Model (fun x => f101 ((15/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(112727272727269/10000000000000),(317355371899/10000000000000),(-230803907/2000000000000),(262277/625000000000)⟩
def e102 : ℝ := (54899/10000000000000)
theorem h102 : Model (fun x => f102 ((15/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(125434710743797/10000000000000),(194452291509/5000000000000),(-13134840527/100000000000000),(1102517/2500000000000)⟩
def e103 : ℝ := (142633/20000000000000)
theorem h103 : Model (fun x => f103 ((15/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(135434710743797/10000000000000),(194452291509/5000000000000),(-13134840527/100000000000000),(1102517/2500000000000)⟩
def e104 : ℝ := (142633/20000000000000)
theorem h104 : Model (fun x => f104 ((15/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(2040251163171173/50000000000000),(4998099956481/4000000000000),(32052929777/20000000000000),(-23888577/1250000000000)⟩
def e105 : ℝ := (7319663/20000000000000)
theorem h105 : Model (fun x => f105 ((15/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(212727272727269/100000000000000),(317355371899/100000000000000),(-230803907/20000000000000),(262277/6250000000000)⟩
def e106 : ℝ := (54899/100000000000000)
theorem h106 : Model (fun x => f106 ((15/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(226264462809909/50000000000000),(337550713747/25000000000000),(-3902684247/100000000000000),(1316153/12500000000000)⟩
def e107 : ℝ := (273973/100000000000000)
theorem h107 : Model (fun x => f107 ((15/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(19253048835461/2000000000000),(4308374564553/100000000000000),(-4619702337/50000000000000),(838851/6250000000000)⟩
def e108 : ℝ := (968267/100000000000000)
theorem h108 : Model (fun x => f108 ((15/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(39281055281140703/100000000000000),(1378661606167179/100000000000000),(3274599557013/50000000000000),(-22489513887/100000000000000)⟩
def e109 : ℝ := (4751883/1000000000000)
theorem h109 : Model (fun x => f109 ((15/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(16678512396693/78125000000),(1502533433499/1250000000000),(-33487548717/12500000000000),(1121589/312500000000)⟩
def e110 : ℝ := (137907/500000000000)
theorem h110 : Model (fun x => f110 ((15/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(2717081292260463/100000000000000),(4152456034399/5000000000000),(101007419281/100000000000000),(-1295804253/100000000000000)⟩
def e111 : ℝ := (12337361/50000000000000)
theorem h111 : Model (fun x => f111 ((15/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(3269506175613011/12500000000000),(114567053433483/12500000000000),(1074843860993/25000000000000),(-15430881443/100000000000000)⟩
def e112 : ℝ := (63971683/20000000000000)
theorem h112 : Model (fun x => f112 ((15/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(65437104686044791/100000000000000),(2295198033635043/100000000000000),(5424287278999/50000000000000),(-3792039533/10000000000000)⟩
def e113 : ℝ := (159009343/20000000000000)
theorem h113 : Model (fun x => f113 ((15/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(5559504132231/78125000000),(500844477833/1250000000000),(-11162516239/12500000000000),(373863/312500000000)⟩
def e114 : ℝ := (45969/500000000000)
theorem h114 : Model (fun x => f114 ((15/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(809917355371/50000000000000),(2524417731/3125000000000),(713393893/100000000000000),(-782063/12500000000000)⟩
def e115 : ℝ := (54377/100000000000000)
theorem h115 : Model (fun x => f115 ((15/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(206160781367/100000000000000),(15421897411/100000000000000),(164233193/50000000000000),(301727/50000000000000)⟩
def e116 : ℝ := (3283/10000000000000)
theorem h116 : Model (fun x => f116 ((15/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(916921372731/6250000000000),(59002565081/5000000000000),(14684643413/50000000000000),(2516033/1562500000000)⟩
def e117 : ℝ := (480611/20000000000000)
theorem h117 : Model (fun x => f117 ((15/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(1248346770729/4000000000000),(1278424669219/50000000000000),(66052135853/100000000000000),(422749091/100000000000000)⟩
def e118 : ℝ := (5350577/100000000000000)
theorem h118 : Model (fun x => f118 ((15/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(8183539169414127/12500000000000),(2297754882973481/100000000000000),(10914626693851/100000000000000),(-37497646239/100000000000000)⟩
def e119 : ℝ := (200099323/25000000000000)
theorem h119 : Model (fun x => f119 ((15/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(26238644901/100000000000000),(2617049257/100000000000000),(11045987/12500000000000),(7421/781250000000)⟩
def e120 : ℝ := (5643/100000000000000)
theorem h120 : Model (fun x => f120 ((15/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(417432987/12500000000000),(83269749/20000000000000),(1924937/10000000000000),(186117/50000000000000)⟩
def e121 : ℝ := (2867/100000000000000)
theorem h121 : Model (fun x => f121 ((15/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(425022677/100000000000000),(1987119/3125000000000),(1866343/50000000000000),(103799/100000000000000)⟩
def e122 : ℝ := (1359/100000000000000)
theorem h122 : Model (fun x => f122 ((15/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(10818759/20000000000000),(4720913/50000000000000),(671963/100000000000000),(1217/5000000000000)⟩
def e123 : ℝ := (47/10000000000000)
theorem h123 : Model (fun x => f123 ((15/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(32456277/20000000000000),(14162739/50000000000000),(2015889/100000000000000),(3651/5000000000000)⟩
def e124 : ℝ := (141/10000000000000)
theorem h124 : Model (fun x => f124 ((15/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-32456277/20000000000000),(-14162739/50000000000000),(-2015889/100000000000000),(-3651/5000000000000)⟩
def e125 : ℝ := (141/10000000000000)
theorem h125 : Model (fun x => f125 ((15/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(65468313193031631/100000000000000),(2297754854648003/100000000000000),(5457312338981/50000000000000),(-37497719259/100000000000000)⟩
def e126 : ℝ := (400199351/50000000000000)
theorem h126 : Model (fun x => f126 ((15/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(16678512396693/62500000000),(1502533433499/1000000000000),(-33487548717/10000000000000),(1121589/250000000000)⟩
def e127 : ℝ := (137907/400000000000)
theorem h127 : Model (fun x => f127 ((15/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(204782428522627/10000000000000),(3055029236683/25000000000000),(-1709107269/10000000000000),(-10092739/100000000000000)⟩
def e128 : ℝ := (182767/6250000000000)
theorem h128 : Model (fun x => f128 ((15/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(546474603638325217/100000000000000),(1584484601561347/25000000000000),(1735653509617/25000000000000),(-60108125481/100000000000000)⟩
def e129 : ℝ := (1591941843/100000000000000)
theorem h129 : Model (fun x => f129 ((15/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(18299112041/100000000000000),(-106115311/50000000000000),(2228943/100000000000000),(-10571/50000000000000)⟩
def e130 : ℝ := (253/100000000000000)
theorem h130 : Model (fun x => f130 ((15/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (540129660917974037/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2396023996509/20000000000000),(281524926977/100000000000000),(-710004319/50000000000000),(7348409/100000000000000)⟩
def e131 : ℝ := (485741/100000000000000)
theorem h131 : Model (fun x => f131 ((15/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(6398334355003/25000000000000),(322580645479/50000000000000),(-1040582963/50000000000000),(8950573/100000000000000)⟩
def e132 : ℝ := (810493/100000000000000)
theorem h132 : Model (fun x => f132 ((15/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-266946872219519/100000000000000),(-1336053095947/20000000000000),(11254091479/50000000000000),(-104431351/100000000000000)⟩
def e133 : ℝ := (3077537/12500000000000)
theorem h133 : Model (fun x => f133 ((15/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(53333333333333/100000000000000),(-88888888889/12500000000000),(9481481481/100000000000000),(-63209877/50000000000000)⟩
def e134 : ℝ := (854189/50000000000000)
theorem h134 : Model (fun x => f134 ((15/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (37/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-142371665183743/100000000000000),(-83225969337/5000000000000),(8549489017/25000000000000),(-255834733/50000000000000)⟩
def e135 : ℝ := (14671819/50000000000000)
theorem h135 : Model (fun x => f135 ((15/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(253125/2048),(3375/512),(135/1024),(3/2560)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((15/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((15/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(30375/256),(1215/256),(81/1280),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((15/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(496125/2048),(5805/512),(999/5120),(93/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((15/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-225/64),(-3/32),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((15/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(488925/2048),(5757/512),(4979/25600),(93/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((15/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((15/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(45/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((15/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-45/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((15/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(465885/2048),(28401/2560),(4979/25600),(93/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((15/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(472029/2048),(28401/2560),(4979/25600),(93/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((15/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((15/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(472029/32),(28401/40),(4979/400),(93/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((15/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((15/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(47840625/4096),(637875/1024),(25515/2048),(567/5120)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((15/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1712352211/20000000000000),(-456627257/100000000000000),(3805227/25000000000000),(-405891/100000000000000)⟩
def e151 : ℝ := (2729/25000000000000)
theorem h151 : Model (fun x => f151 ((15/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (2827352493/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(63146867328603/50000000000000),(-328300733063/50000000000000),(859742441/12500000000000),(-6765889/10000000000000)⟩
def e152 : ℝ := (158019149/50000000000000)
theorem h152 : Model (fun x => f152 ((15/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(39/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((15/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1209/64),(7/32),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((15/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(69/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((15/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(231884057971/4000000000000),(-2520478891/5000000000000),(219172077/50000000000000),(-3811689/100000000000000)⟩
def e156 : ℝ := (33439/100000000000000)
theorem h156 : Model (fun x => f156 ((15/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (171/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(10951086956521/10000000000000),(157923755511/50000000000000),(876688291/100000000000000),(-762339/10000000000000)⟩
def e157 : ℝ := (600623/50000000000000)
theorem h157 : Model (fun x => f157 ((15/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(20951086956521/10000000000000),(157923755511/50000000000000),(876688291/100000000000000),(-762339/10000000000000)⟩
def e158 : ℝ := (600623/50000000000000)
theorem h158 : Model (fun x => f158 ((15/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(20951086956521/20000000000000),(157923755511/100000000000000),(87668829/20000000000000),(-762339/20000000000000)⟩
def e159 : ℝ := (37539/6250000000000)
theorem h159 : Model (fun x => f159 ((15/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(951086956521/20000000000000),(157923755511/100000000000000),(87668829/20000000000000),(-762339/20000000000000)⟩
def e160 : ℝ := (37539/6250000000000)
theorem h160 : Model (fun x => f160 ((15/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((15/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((15/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(77319487577637/20000000000000),(582813859623/100000000000000),(161769863/10000000000000),(-1406697/10000000000000)⟩
def e163 : ℝ := (2216591/100000000000000)
theorem h163 : Model (fun x => f163 ((15/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(274231172360247/10000000000000),(582813859623/100000000000000),(161769863/10000000000000),(-1406697/10000000000000)⟩
def e164 : ℝ := (138537/6250000000000)
theorem h164 : Model (fun x => f164 ((15/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((15/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(718180142288529/25000000000000),(308830678397/6250000000000),(7317895823/50000000000000),(-57077507/50000000000000)⟩
def e166 : ℝ := (18837469/100000000000000)
theorem h166 : Model (fun x => f166 ((15/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(2038775380383767/25000000000000),(308830678397/6250000000000),(7317895823/50000000000000),(-57077507/50000000000000)⟩
def e167 : ℝ := (1883747/10000000000000)
theorem h167 : Model (fun x => f167 ((15/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((15/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(533932003490431/6250000000000),(4513778326723/25000000000000),(58882669299/100000000000000),(-48207241/12500000000000)⟩
def e169 : ℝ := (2158747/3125000000000)
theorem h169 : Model (fun x => f169 ((15/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(2762391934978903/20000000000000),(4513778326723/25000000000000),(58882669299/100000000000000),(-48207241/12500000000000)⟩
def e170 : ℝ := (13815981/20000000000000)
theorem h170 : Model (fun x => f170 ((15/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((15/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(578751136377353/4000000000000),(8145215574677/20000000000000),(9421251611/6250000000000),(-758334161/100000000000000)⟩
def e172 : ℝ := (611657/390625000000)
theorem h172 : Model (fun x => f172 ((15/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(1680449269514811/10000000000000),(8145215574677/20000000000000),(9421251611/6250000000000),(-758334161/100000000000000)⟩
def e173 : ℝ := (156584193/100000000000000)
theorem h173 : Model (fun x => f173 ((15/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((15/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(17603619385813499/100000000000000),(17300266476229/25000000000000),(295886030869/100000000000000),(-15911837/1562500000000)⟩
def e175 : ℝ := (5351081/2000000000000)
theorem h175 : Model (fun x => f175 ((15/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(18006000338194451/100000000000000),(17300266476229/25000000000000),(295886030869/100000000000000),(-15911837/1562500000000)⟩
def e176 : ℝ := (267554051/100000000000000)
theorem h176 : Model (fun x => f176 ((15/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((15/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(18862263941232923/100000000000000),(100927629414291/100000000000000),(498169868459/100000000000000),(-24562639/2500000000000)⟩
def e178 : ℝ := (392231653/100000000000000)
theorem h178 : Model (fun x => f178 ((15/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(150757159148911/800000000000),(100927629414291/100000000000000),(498169868459/100000000000000),(-24562639/2500000000000)⟩
def e179 : ℝ := (196115827/50000000000000)
theorem h179 : Model (fun x => f179 ((15/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((15/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(9870394845771593/50000000000000),(135487347937423/100000000000000),(190963277979/25000000000000),(-518389439/100000000000000)⟩
def e181 : ℝ := (528538091/100000000000000)
theorem h181 : Model (fun x => f181 ((15/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(19744123024876519/100000000000000),(135487347937423/100000000000000),(190963277979/25000000000000),(-518389439/100000000000000)⟩
def e182 : ℝ := (132134523/25000000000000)
theorem h182 : Model (fun x => f182 ((15/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(9389188938453/1000000000000),(18811836521721/50000000000000),(168419225969/50000000000000),(255742239/25000000000000)⟩
def e183 : ℝ := (74021871/50000000000000)
theorem h183 : Model (fun x => f183 ((15/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(54868505582463/50000000000000),(330867433421/100000000000000),(233555551/20000000000000),(-6601417/100000000000000)⟩
def e184 : ℝ := (317607/25000000000000)
theorem h184 : Model (fun x => f184 ((15/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(40951086956521/20000000000000),(157923755511/100000000000000),(87668829/20000000000000),(-762339/20000000000000)⟩
def e185 : ℝ := (37539/6250000000000)
theorem h185 : Model (fun x => f185 ((15/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(52405985091267/12500000000000),(646714944443/100000000000000),(408893209/20000000000000),(-14224807/100000000000000)⟩
def e186 : ℝ := (617919/25000000000000)
theorem h186 : Model (fun x => f186 ((15/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(858432821005847/100000000000000),(1986275994447/100000000000000),(1409044081/20000000000000),(-19521491/50000000000000)⟩
def e187 : ℝ := (3812551/50000000000000)
theorem h187 : Model (fun x => f187 ((15/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1757687854967103/100000000000000),(5422677397883/100000000000000),(10662581663/50000000000000),(-23207667/25000000000000)⟩
def e188 : ℝ := (20899743/100000000000000)
theorem h188 : Model (fun x => f188 ((15/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(964417058824899/50000000000000),(2353260158967/20000000000000),(61869358161/100000000000000),(-16803813/20000000000000)⟩
def e189 : ℝ := (45822061/100000000000000)
theorem h189 : Model (fun x => f189 ((15/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((15/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(20951086956521/2500000000000),(157923755511/12500000000000),(87668829/2500000000000),(-762339/2500000000000)⟩
def e191 : ℝ := (37539/781250000000)
theorem h191 : Model (fun x => f191 ((15/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(473890244712883/50000000000000),(1594257477509/100000000000000),(934906183/20000000000000),(-37094977/100000000000000)⟩
def e192 : ℝ := (303771/5000000000000)
theorem h192 : Model (fun x => f192 ((15/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(523890244712883/50000000000000),(1594257477509/100000000000000),(934906183/20000000000000),(-37094977/100000000000000)⟩
def e193 : ℝ := (303771/5000000000000)
theorem h193 : Model (fun x => f193 ((15/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(631560861191319/3125000000000),(77017793102403/50000000000000),(2893762941/312500000000),(-29729853/50000000000000)⟩
def e194 : ℝ := (150397421/25000000000000)
theorem h194 : Model (fun x => f194 ((15/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(494805836147/100000000000000),(-1885648313/50000000000000),(3036169/50000000000000),(127971/100000000000000)⟩
def e195 : ℝ := (16239/100000000000000)
theorem h195 : Model (fun x => f195 ((15/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (5013746326681723/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(4645825483433/100000000000000),(150754713427/100000000000000),(60962067/20000000000000),(-4155287/100000000000000)⟩
def e196 : ℝ := (231819/25000000000000)
theorem h196 : Model (fun x => f196 ((15/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(10951086956521/5000000000000),(157923755511/25000000000000),(876688291/50000000000000),(-762339/5000000000000)⟩
def e197 : ℝ := (600623/25000000000000)
theorem h197 : Model (fun x => f197 ((15/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(11932555123217/25000000000000),(-575644457/800000000000),(-91248449/100000000000000),(543849/25000000000000)⟩
def e198 : ℝ := (8751/3125000000000)
theorem h198 : Model (fun x => f198 ((15/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (209194136541261/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(104539559014263/100000000000000),(143911114247/100000000000000),(1425757/781250000000),(-1087699/25000000000000)⟩
def e199 : ℝ := (1786719/100000000000000)
theorem h199 : Model (fun x => f199 ((15/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(4539559014263/100000000000000),(143911114247/100000000000000),(1425757/781250000000),(-1087699/25000000000000)⟩
def e200 : ℝ := (1786719/100000000000000)
theorem h200 : Model (fun x => f200 ((15/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(192900376752509/50000000000000),(531100540673/100000000000000),(673500449/100000000000000),(-1605651/10000000000000)⟩
def e201 : ℝ := (6593847/100000000000000)
theorem h201 : Model (fun x => f201 ((15/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2741515039219303/100000000000000),(531100540673/100000000000000),(673500449/100000000000000),(-1605651/10000000000000)⟩
def e202 : ℝ := (824231/12500000000000)
theorem h202 : Model (fun x => f202 ((15/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1432983866154779/50000000000000),(4500555003331/100000000000000),(1294313391/20000000000000),(-16765581/12500000000000)⟩
def e203 : ℝ := (139851/250000000000)
theorem h203 : Model (fun x => f203 ((15/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(814834868469051/10000000000000),(4500555003331/100000000000000),(1294313391/20000000000000),(-16765581/12500000000000)⟩
def e204 : ℝ := (55940401/100000000000000)
theorem h204 : Model (fun x => f204 ((15/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4259123890959979/50000000000000),(3286247947709/20000000000000),(28112629833/100000000000000),(-477204667/100000000000000)⟩
def e205 : ℝ := (204606637/100000000000000)
theorem h205 : Model (fun x => f205 ((15/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13787295400967577/100000000000000),(3286247947709/20000000000000),(28112629833/100000000000000),(-477204667/100000000000000)⟩
def e206 : ℝ := (102303319/50000000000000)
theorem h206 : Model (fun x => f206 ((15/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3603294453041317/25000000000000),(37018595999309/100000000000000),(19549146399/25000000000000),(-20565621/2000000000000)⟩
def e207 : ℝ := (115544121/25000000000000)
theorem h207 : Model (fun x => f207 ((15/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16748892097879553/100000000000000),(37018595999309/100000000000000),(19549146399/25000000000000),(-20565621/2000000000000)⟩
def e208 : ℝ := (92435297/20000000000000)
theorem h208 : Model (fun x => f208 ((15/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(17509217938898027/100000000000000),(12560518850607/20000000000000),(2069830599/1250000000000),(-1623579237/100000000000000)⟩
def e209 : ℝ := (19667369/2500000000000)
theorem h209 : Model (fun x => f209 ((15/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(17911598891278979/100000000000000),(12560518850607/20000000000000),(2069830599/1250000000000),(-1623579237/100000000000000)⟩
def e210 : ℝ := (786694761/100000000000000)
theorem h210 : Model (fun x => f210 ((15/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(3744941298669333/20000000000000),(22857584156383/25000000000000),(296171367609/100000000000000),(-132729351/6250000000000)⟩
def e211 : ℝ := (1149472867/100000000000000)
theorem h211 : Model (fun x => f211 ((15/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(18707087445727617/100000000000000),(22857584156383/25000000000000),(296171367609/100000000000000),(-132729351/6250000000000)⟩
def e212 : ℝ := (287368217/25000000000000)
theorem h212 : Model (fun x => f212 ((15/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(19556306720176207/100000000000000),(61251224349947/50000000000000),(475334511743/100000000000000),(-2440901023/100000000000000)⟩
def e213 : ℝ := (154570277/10000000000000)
theorem h213 : Model (fun x => f213 ((15/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(977982002675477/5000000000000),(61251224349947/50000000000000),(475334511743/100000000000000),(-2440901023/100000000000000)⟩
def e214 : ℝ := (1545702771/100000000000000)
theorem h214 : Model (fun x => f214 ((15/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(110990175400811/12500000000000),(33709566896357/100000000000000),(116784232773/50000000000000),(-54183821/100000000000000)⟩
def e215 : ℝ := (432068891/100000000000000)
theorem h215 : Model (fun x => f215 ((15/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(21857038797793/20000000000000),(75222022103/25000000000000),(147166747/25000000000000),(-428567/5000000000000)⟩
def e216 : ℝ := (1876507/50000000000000)
theorem h216 : Model (fun x => f216 ((15/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(204539559014263/100000000000000),(143911114247/100000000000000),(1425757/781250000000),(-1087699/25000000000000)⟩
def e217 : ℝ := (1786719/100000000000000)
theorem h217 : Model (fun x => f217 ((15/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(418364312017491/100000000000000),(294355158453/50000000000000),(47683039/5000000000000),(-4318233/25000000000000)⟩
def e218 : ℝ := (1831613/25000000000000)
theorem h218 : Model (fun x => f218 ((15/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(855720518873631/100000000000000),(1806218229107/100000000000000),(1780667507/50000000000000),(-10217071/20000000000000)⟩
def e219 : ℝ := (22530387/100000000000000)
theorem h219 : Model (fun x => f219 ((15/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(6837058498823/390625000000),(4925907734201/100000000000000),(11445351097/100000000000000),(-26659793/20000000000000)⟩
def e220 : ℝ := (61583533/100000000000000)
theorem h220 : Model (fun x => f220 ((15/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1912804516755899/100000000000000),(5324846422971/50000000000000),(9408226347/25000000000000),(-23226419/10000000000000)⟩
def e221 : ℝ := (67059437/50000000000000)
theorem h221 : Model (fun x => f221 ((15/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(104539559014263/12500000000000),(143911114247/12500000000000),(1425757/97656250000),(-1087699/3125000000000)⟩
def e222 : ℝ := (1786719/12500000000000)
theorem h222 : Model (fun x => f222 ((15/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(945601666103069/100000000000000),(363044250597/25000000000000),(512160539/25000000000000),(-10844427/25000000000000)⟩
def e223 : ℝ := (9023383/50000000000000)
theorem h223 : Model (fun x => f223 ((15/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1045601666103069/100000000000000),(363044250597/25000000000000),(512160539/25000000000000),(-10844427/25000000000000)⟩
def e224 : ℝ := (9023383/50000000000000)
theorem h224 : Model (fun x => f224 ((15/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(20000315896494437/100000000000000),(34782668281249/25000000000000),(117465839153/20000000000000),(-311702313/12500000000000)⟩
def e225 : ℝ := (1758670471/100000000000000)
theorem h225 : Model (fun x => f225 ((15/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(62499012839/12500000000000),(-1739078477/50000000000000),(9512767/100000000000000),(98303/100000000000000)⟩
def e226 : ℝ := (22997/50000000000000)
theorem h226 : Model (fun x => f226 ((15/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (19860593641884701/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(2219768447161/50000000000000),(34415468077/25000000000000),(79818131/100000000000000),(-4315227/100000000000000)⟩
def e227 : ℝ := (2656849/100000000000000)
theorem h227 : Model (fun x => f227 ((15/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(1817072475551/20000000000000),(57683317147/20000000000000),(192314233/50000000000000),(-4235257/50000000000000)⟩
def e228 : ℝ := (28673/800000000000)
theorem h228 : Model (fun x => f228 ((15/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(11474243454007/100000000000000),(7614936373/2500000000000),(-391550073/50000000000000),(233429/50000000000000)⟩
def e229 : ℝ := (34290211/100000000000000)
theorem h229 : Model (fun x => f229 ((15/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(6119596508803/100000000000000),(80857355839/100000000000000),(-149575149/10000000000000),(2524043/12500000000000)⟩
def e230 : ℝ := (2400021/12500000000000)
theorem h230 : Model (fun x => f230 ((15/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-6812603433747/5000000000000),(-1583662030901/100000000000000),(16351102289/50000000000000),(-245738561/50000000000000)⟩
def e231 : ℝ := (24271903/50000000000000)
theorem h231 : Model (fun x => f231 ((15/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((15/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-1125/64),(-15/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((15/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(315/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((15/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1395/64),(9/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((15/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((15/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(3059/64),(9/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((15/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((15/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(382375/32),(225/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((15/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(495/64),(9/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((15/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(879/64),(9/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((15/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((15/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(166131/64),(1701/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((15/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(38523815543/100000000000000),(-157776719/100000000000000),(2399259/100000000000000),(-17007/100000000000000)⟩
def e244 : ℝ := (91/50000000000000)
theorem h244 : Model (fun x => f244 ((15/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1034019/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(460329499007957/100000000000000),(-268713474583/20000000000000),(-29169563/800000000000),(-23108861/50000000000000)⟩
def e245 : ℝ := (4304329/100000000000000)
theorem h245 : Model (fun x => f245 ((15/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(135/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((15/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(2385/64),(87/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((15/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(3729/64),(87/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((15/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(961/64),(31/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((15/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3583569/4096),(99603/5120),(7739/51200),(59/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((15/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((15/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(23805/32),(207/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((15/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(33606385213/25000000000000),(-1168917747/50000000000000),(15246753/50000000000000),(-88387/25000000000000)⟩
def e253 : ℝ := (3941/100000000000000)
theorem h253 : Model (fun x => f253 ((15/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (58473/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(117608203370473/100000000000000),(35607222183/6250000000000),(758884361/50000000000000),(-7512989/100000000000000)⟩
def e254 : ℝ := (3482231/50000000000000)
theorem h254 : Model (fun x => f254 ((15/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(217608203370473/100000000000000),(35607222183/6250000000000),(758884361/50000000000000),(-7512989/100000000000000)⟩
def e255 : ℝ := (3482231/50000000000000)
theorem h255 : Model (fun x => f255 ((15/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(27201025421309/25000000000000),(35607222183/12500000000000),(758884361/100000000000000),(-751299/20000000000000)⟩
def e256 : ℝ := (435279/12500000000000)
theorem h256 : Model (fun x => f256 ((15/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(2201025421309/25000000000000),(35607222183/12500000000000),(758884361/100000000000000),(-751299/20000000000000)⟩
def e257 : ℝ := (435279/12500000000000)
theorem h257 : Model (fun x => f257 ((15/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(401538946695513/100000000000000),(525630422701/50000000000000),(560128933/20000000000000),(-1732907/12500000000000)⟩
def e258 : ℝ := (6425549/50000000000000)
theorem h258 : Model (fun x => f258 ((15/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1378626616204899/50000000000000),(525630422701/50000000000000),(560128933/20000000000000),(-1732907/12500000000000)⟩
def e259 : ℝ := (12851099/100000000000000)
theorem h259 : Model (fun x => f259 ((15/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3000004610710613/100000000000000),(1799613039221/20000000000000),(13483089061/50000000000000),(-102704163/100000000000000)⟩
def e260 : ℝ := (27531957/25000000000000)
theorem h260 : Model (fun x => f260 ((15/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(1656477112618313/20000000000000),(1799613039221/20000000000000),(13483089061/50000000000000),(-102704163/100000000000000)⟩
def e261 : ℝ := (110127829/100000000000000)
theorem h261 : Model (fun x => f261 ((15/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2252893802507363/25000000000000),(6676656688339/20000000000000),(3682053911/3125000000000),(-277773577/100000000000000)⟩
def e262 : ℝ := (409292033/100000000000000)
theorem h262 : Model (fun x => f262 ((15/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14280622829077071/100000000000000),(6676656688339/20000000000000),(3682053911/3125000000000),(-277773577/100000000000000)⟩
def e263 : ℝ := (204646017/50000000000000)
theorem h263 : Model (fun x => f263 ((15/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(7768951692117021/50000000000000),(77001846460697/100000000000000),(66333502873/20000000000000),(-249703669/100000000000000)⟩
def e264 : ℝ := (473052129/50000000000000)
theorem h264 : Model (fun x => f264 ((15/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(17873617669948327/100000000000000),(77001846460697/100000000000000),(66333502873/20000000000000),(-249703669/100000000000000)⟩
def e265 : ℝ := (946104259/100000000000000)
theorem h265 : Model (fun x => f265 ((15/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(19447229144440887/100000000000000),(134695557369633/100000000000000),(357926848631/50000000000000),(146506573/25000000000000)⟩
def e266 : ℝ := (1658297579/100000000000000)
theorem h266 : Model (fun x => f266 ((15/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(19849610096821839/100000000000000),(134695557369633/100000000000000),(357926848631/50000000000000),(146506573/25000000000000)⟩
def e267 : ℝ := (82914879/5000000000000)
theorem h267 : Model (fun x => f267 ((15/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(4319437990773781/20000000000000),(203097449363027/100000000000000),(41037641953/3125000000000),(2953319483/100000000000000)⟩
def e268 : ℝ := (1253510797/50000000000000)
theorem h268 : Model (fun x => f268 ((15/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(21579570906249857/100000000000000),(203097449363027/100000000000000),(41037641953/3125000000000),(2953319483/100000000000000)⟩
def e269 : ℝ := (501404319/20000000000000)
theorem h269 : Model (fun x => f269 ((15/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(11739729136036849/50000000000000),(282449441394879/100000000000000),(271390409359/12500000000000),(1536947457/20000000000000)⟩
def e270 : ℝ := (438031001/12500000000000)
theorem h270 : Model (fun x => f270 ((15/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(23482791605407031/100000000000000),(282449441394879/100000000000000),(271390409359/12500000000000),(1536947457/20000000000000)⟩
def e271 : ℝ := (3504248009/100000000000000)
theorem h271 : Model (fun x => f271 ((15/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1033724425736049/50000000000000),(91759694283451/100000000000000),(293483583767/25000000000000),(8122520337/100000000000000)⟩
def e272 : ℝ := (586971723/50000000000000)
theorem h272 : Model (fun x => f272 ((15/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(118383325435311/100000000000000),(6198738917/1000000000000),(2462834157/100000000000000),(-48137/1250000000000)⟩
def e273 : ℝ := (7613217/100000000000000)
theorem h273 : Model (fun x => f273 ((15/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(52201025421309/25000000000000),(35607222183/12500000000000),(758884361/100000000000000),(-751299/20000000000000)⟩
def e274 : ℝ := (435279/12500000000000)
theorem h274 : Model (fun x => f274 ((15/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(435991528805783/100000000000000),(297397361657/25000000000000),(3980602879/100000000000000),(-227279/2000000000000)⟩
def e275 : ℝ := (14577681/100000000000000)
theorem h275 : Model (fun x => f275 ((15/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(455184097573321/50000000000000),(3725867336661/100000000000000),(15008971669/100000000000000),(-19739729/100000000000000)⟩
def e276 : ℝ := (45751321/100000000000000)
theorem h276 : Model (fun x => f276 ((15/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(950443065952021/50000000000000),(2593254607433/25000000000000),(12215353303/25000000000000),(-1096513/25000000000000)⟩
def e277 : ℝ := (63787859/50000000000000)
theorem h277 : Model (fun x => f277 ((15/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2250332215686657/100000000000000),(24063021007753/100000000000000),(21119883973/12500000000000),(95990933/20000000000000)⟩
def e278 : ℝ := (4658017/1562500000000)
theorem h278 : Model (fun x => f278 ((15/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(27201025421309/3125000000000),(35607222183/1562500000000),(758884361/12500000000000),(-751299/2500000000000)⟩
def e279 : ℝ := (435279/1562500000000)
theorem h279 : Model (fun x => f279 ((15/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(988816138917199/100000000000000),(724684027853/25000000000000),(1706781809/20000000000000),(-847573/2500000000000)⟩
def e280 : ℝ := (35471073/100000000000000)
theorem h280 : Model (fun x => f280 ((15/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1088816138917199/100000000000000),(724684027853/25000000000000),(1706781809/20000000000000),(-847573/2500000000000)⟩
def e281 : ℝ := (35471073/100000000000000)
theorem h281 : Model (fun x => f281 ((15/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(24501980343649313/100000000000000),(327233248806297/100000000000000),(1364609212847/50000000000000),(5707044737/50000000000000)⟩
def e282 : ℝ := (163262917/4000000000000)
theorem h282 : Model (fun x => f282 ((15/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(408130275991/100000000000000),(-5450734769/100000000000000),(1708497/6250000000000),(51937/100000000000000)⟩
def e283 : ℝ := (35539/50000000000000)
theorem h283 : Model (fun x => f283 ((15/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (24172002380754923/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1687576940697/20000000000000),(261807940149/100000000000000),(354760707/100000000000000),(-2340213/50000000000000)⟩
def e284 : ℝ := (3234051/50000000000000)
theorem h284 : Model (fun x => f284 ((15/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(117608203370473/50000000000000),(35607222183/3125000000000),(758884361/25000000000000),(-7512989/50000000000000)⟩
def e285 : ℝ := (3482231/25000000000000)
theorem h285 : Model (fun x => f285 ((15/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(45954149913067/100000000000000),(-3007790333/2500000000000),(-2767299/50000000000000),(2440217/100000000000000)⟩
def e286 : ℝ := (372257/25000000000000)
theorem h286 : Model (fun x => f286 ((15/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (54259238892343/25000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(108091700173863/100000000000000),(48124645327/20000000000000),(5534597/50000000000000),(-4880437/100000000000000)⟩
def e287 : ℝ := (9982921/100000000000000)
theorem h287 : Model (fun x => f287 ((15/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(8091700173863/100000000000000),(48124645327/20000000000000),(5534597/50000000000000),(-4880437/100000000000000)⟩
def e288 : ℝ := (9982921/100000000000000)
theorem h288 : Model (fun x => f288 ((15/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(99727461469933/25000000000000),(222003572193/25000000000000),(10212649/25000000000000),(-18011137/100000000000000)⟩
def e289 : ℝ := (7368347/20000000000000)
theorem h289 : Model (fun x => f289 ((15/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2754624131594017/100000000000000),(222003572193/25000000000000),(10212649/25000000000000),(-18011137/100000000000000)⟩
def e290 : ℝ := (4605217/12500000000000)
theorem h290 : Model (fun x => f290 ((15/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1488760028619741/50000000000000),(1897033802407/25000000000000),(2485839427/100000000000000),(-9606853/6250000000000)⟩
def e291 : ℝ := (63015761/20000000000000)
theorem h291 : Model (fun x => f291 ((15/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4129950504810217/50000000000000),(1897033802407/25000000000000),(2485839427/100000000000000),(-9606853/6250000000000)⟩
def e292 : ℝ := (157539403/50000000000000)
theorem h292 : Model (fun x => f292 ((15/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4464133716988401/50000000000000),(3509673085723/12500000000000),(437202127/2000000000000),(-112489037/20000000000000)⟩
def e293 : ℝ := (583704757/50000000000000)
theorem h293 : Model (fun x => f293 ((15/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14197315053024421/100000000000000),(3509673085723/12500000000000),(437202127/2000000000000),(-112489037/20000000000000)⟩
def e294 : ℝ := (233481903/20000000000000)
theorem h294 : Model (fun x => f294 ((15/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(122768953758831/800000000000),(64511360047343/100000000000000),(18552239589/20000000000000),(-1245139147/100000000000000)⟩
def e295 : ℝ := (1343758247/50000000000000)
theorem h295 : Model (fun x => f295 ((15/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(110511459409801/625000000000),(64511360047343/100000000000000),(18552239589/20000000000000),(-1245139147/100000000000000)⟩
def e296 : ℝ := (537503299/20000000000000)
theorem h296 : Model (fun x => f296 ((15/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(149317144203753/781250000000),(112278024189781/100000000000000),(51490741701/20000000000000),(-123656059/6250000000000)⟩
def e297 : ℝ := (4689201723/100000000000000)
theorem h297 : Model (fun x => f297 ((15/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(2439371926307667/12500000000000),(112278024189781/100000000000000),(51490741701/20000000000000),(-123656059/6250000000000)⟩
def e298 : ℝ := (1172300431/25000000000000)
theorem h298 : Model (fun x => f298 ((15/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(21094068709678957/100000000000000),(84160394389017/50000000000000),(275306622889/50000000000000),(-2459085373/100000000000000)⟩
def e299 : ℝ := (7049546263/100000000000000)
theorem h299 : Model (fun x => f299 ((15/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(21076449662059909/100000000000000),(84160394389017/50000000000000),(275306622889/50000000000000),(-2459085373/100000000000000)⟩
def e300 : ℝ := (881193283/12500000000000)
theorem h300 : Model (fun x => f300 ((15/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(11390946388004479/50000000000000),(232655635573183/100000000000000),(10025191249/1000000000000),(-585788731/25000000000000)⟩
def e301 : ℝ := (2442985297/25000000000000)
theorem h301 : Model (fun x => f301 ((15/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(22785226109342291/100000000000000),(232655635573183/100000000000000),(10025191249/1000000000000),(-585788731/25000000000000)⟩
def e302 : ℝ := (9771941189/100000000000000)
theorem h302 : Model (fun x => f302 ((15/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(1843712180704727/100000000000000),(73652342728557/100000000000000),(321733239959/50000000000000),(284106823/25000000000000)⟩
def e303 : ℝ := (3129120661/100000000000000)
theorem h303 : Model (fun x => f303 ((15/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(58419078232381/50000000000000),(104037494673/20000000000000),(602925131/100000000000000),(-419897/4000000000000)⟩
def e304 : ℝ := (5413239/25000000000000)
theorem h304 : Model (fun x => f304 ((15/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(208091700173863/100000000000000),(48124645327/20000000000000),(5534597/50000000000000),(-4880437/100000000000000)⟩
def e305 : ℝ := (9982921/100000000000000)
theorem h305 : Model (fun x => f305 ((15/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(54127694601561/12500000000000),(200286785327/20000000000000),(625063519/100000000000000),(-20258299/100000000000000)⟩
def e306 : ℝ := (20809399/50000000000000)
theorem h306 : Model (fun x => f306 ((15/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(225270479922609/25000000000000),(3125851326079/100000000000000),(1879159963/50000000000000),(-12334857/20000000000000)⟩
def e307 : ℝ := (26026249/20000000000000)
theorem h307 : Model (fun x => f307 ((15/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1875076686643111/100000000000000),(1084106194891/12500000000000),(7721009329/50000000000000),(-162926407/100000000000000)⟩
def e308 : ℝ := (180836473/50000000000000)
theorem h308 : Model (fun x => f308 ((15/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2190805032974353/100000000000000),(2485888947219/12500000000000),(1861563887/2500000000000),(-254576743/100000000000000)⟩
def e309 : ℝ := (834013981/100000000000000)
theorem h309 : Model (fun x => f309 ((15/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(108091700173863/12500000000000),(48124645327/2500000000000),(5534597/6250000000000),(-4880437/12500000000000)⟩
def e310 : ℝ := (9982921/12500000000000)
theorem h310 : Model (fun x => f310 ((15/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(490785878927833/50000000000000),(489034657289/20000000000000),(691478683/100000000000000),(-49540921/100000000000000)⟩
def e311 : ℝ := (25379081/25000000000000)
theorem h311 : Model (fun x => f311 ((15/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(540785878927833/50000000000000),(489034657289/20000000000000),(691478683/100000000000000),(-49540921/100000000000000)⟩
def e312 : ℝ := (25379081/25000000000000)
theorem h312 : Model (fun x => f312 ((15/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(2961891063291389/12500000000000),(268662361702591/100000000000000),(1306789259783/100000000000000),(-1880521493/100000000000000)⟩
def e313 : ℝ := (452030001/4000000000000)
theorem h313 : Model (fun x => f313 ((15/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(211013837661/50000000000000),(-1196268591/25000000000000),(30979707/100000000000000),(-53867/100000000000000)⟩
def e314 : ℝ := (207421/100000000000000)
theorem h314 : Model (fun x => f314 ((15/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (1171257308704861/5000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(486310978491/6250000000000),(55652567733/25000000000000),(-237536113/100000000000000),(-834037/20000000000000)⟩
def e315 : ℝ := (17440117/100000000000000)
theorem h315 : Model (fun x => f315 ((15/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(16218860359341/100000000000000),(484418211081/100000000000000),(58612297/50000000000000),(-8850611/100000000000000)⟩
def e316 : ℝ := (23908219/100000000000000)
theorem h316 : Model (fun x => f316 ((15/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(37330099318477/50000000000000),(3219213773/160000000000),(-6560236983/100000000000000),(-67475787/100000000000000)⟩
def e317 : ℝ := (111207183/100000000000000)
theorem h317 : Model (fun x => f317 ((15/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(318550180851/800000000000),(27107714479/5000000000000),(-268187923/2500000000000),(107046471/100000000000000)⟩
def e318 : ℝ := (500857/781250000000)
theorem h318 : Model (fun x => f318 ((15/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-19286659213713/20000000000000),(-1041507741321/100000000000000),(10987343829/50000000000000),(-384430651/100000000000000)⟩
def e319 : ℝ := (56326751/50000000000000)
theorem h319 : Model (fun x => f319 ((15/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((15/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-2475/64),(-33/32),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((15/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((15/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(1455/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((15/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(9165/64),(223/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((15/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((15/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(16077/64),(223/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((15/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2009625/32),(5575/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((15/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((15/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(25133695167531179/2500000000000),(257341588746053/6250000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (130329/100000000000000)
theorem h329 : Model (fun x => f329 ((15/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4973403201/50000000000000),(-20368887/50000000000000),(309743/50000000000000),(-4391/100000000000000)⟩
def e330 : ℝ := (3/6250000000000)
theorem h330 : Model (fun x => f330 ((15/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (500592295832701453/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(624667212988101/100000000000000),(90747632211/10000000000000),(7613563141/100000000000000),(10111971/100000000000000)⟩
def e331 : ℝ := (2816763/50000000000000)
theorem h331 : Model (fun x => f331 ((15/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((15/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(87/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((15/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((15/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((15/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(625806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((15/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((15/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((15/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2776386042793027/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1047/100000000000000)
theorem h339 : Model (fun x => f339 ((15/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3724193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((15/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((15/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((15/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1049306978603357/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1047/100000000000000)
theorem h343 : Model (fun x => f343 ((15/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(1191262447967/25000000000000),(-3198712687/50000000000000),(536813/6250000000000),(-2883/25000000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((15/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1047898207785593/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(132296177353561/100000000000000),(175877592199/20000000000000),(-1180642201/100000000000000),(39627/2500000000000)⟩
def e345 : ℝ := (317/10000000000000)
theorem h345 : Model (fun x => f345 ((15/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(232296177353561/100000000000000),(175877592199/20000000000000),(-1180642201/100000000000000),(39627/2500000000000)⟩
def e346 : ℝ := (317/10000000000000)
theorem h346 : Model (fun x => f346 ((15/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(5807404433839/5000000000000),(439693980497/100000000000000),(-590321101/100000000000000),(39627/5000000000000)⟩
def e347 : ℝ := (1587/100000000000000)
theorem h347 : Model (fun x => f347 ((15/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(807404433839/5000000000000),(439693980497/100000000000000),(-590321101/100000000000000),(39627/5000000000000)⟩
def e348 : ℝ := (1587/100000000000000)
theorem h348 : Model (fun x => f348 ((15/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(428641755830973/100000000000000),(1622680166119/100000000000000),(-136160373/6250000000000),(58497/2000000000000)⟩
def e349 : ℝ := (5859/100000000000000)
theorem h349 : Model (fun x => f349 ((15/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(1392178020772629/50000000000000),(1622680166119/100000000000000),(-136160373/6250000000000),(58497/2000000000000)⟩
def e350 : ℝ := (293/5000000000000)
theorem h350 : Model (fun x => f350 ((15/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3233976324211267/100000000000000),(14127357908563/100000000000000),(-36975553/312500000000),(1261249/20000000000000)⟩
def e351 : ℝ := (17933/20000000000000)
theorem h351 : Model (fun x => f351 ((15/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8516357276592219/100000000000000),(14127357908563/100000000000000),(-36975553/312500000000),(1261249/20000000000000)⟩
def e352 : ℝ := (44833/50000000000000)
theorem h352 : Model (fun x => f352 ((15/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1236448275205967/12500000000000),(26927283247059/50000000000000),(-1899559101/100000000000000),(-7575253/12500000000000)⟩
def e353 : ℝ := (449593/100000000000000)
theorem h353 : Model (fun x => f353 ((15/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3032126764139071/20000000000000),(26927283247059/50000000000000),(-1899559101/100000000000000),(-7575253/12500000000000)⟩
def e354 : ℝ := (224797/50000000000000)
theorem h354 : Model (fun x => f354 ((15/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(880439320701157/5000000000000),(129211443962873/100000000000000),(145092565019/100000000000000),(-276501123/100000000000000)⟩
def e355 : ℝ := (937543/100000000000000)
theorem h355 : Model (fun x => f355 ((15/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(797780027989497/4000000000000),(129211443962873/100000000000000),(145092565019/100000000000000),(-276501123/100000000000000)⟩
def e356 : ℝ := (117193/12500000000000)
theorem h356 : Model (fun x => f356 ((15/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(23165156358872031/100000000000000),(237771391531473/100000000000000),(30946029309/5000000000000),(-35985221/12500000000000)⟩
def e357 : ℝ := (615661/25000000000000)
theorem h357 : Model (fun x => f357 ((15/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(23567537311252983/100000000000000),(237771391531473/100000000000000),(30946029309/5000000000000),(-35985221/12500000000000)⟩
def e358 : ℝ := (492529/20000000000000)
theorem h358 : Model (fun x => f358 ((15/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(27373244135207327/100000000000000),(47473996199119/12500000000000),(203150847681/12500000000000),(585077427/50000000000000)⟩
def e359 : ℝ := (786319/12500000000000)
theorem h359 : Model (fun x => f359 ((15/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(27355625087588279/100000000000000),(47473996199119/12500000000000),(203150847681/12500000000000),(585077427/50000000000000)⟩
def e360 : ℝ := (6290553/100000000000000)
theorem h360 : Model (fun x => f360 ((15/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(3177303568481951/10000000000000),(140350537616891/25000000000000),(679216603041/20000000000000),(323993051/5000000000000)⟩
def e361 : ℝ := (460953/5000000000000)
theorem h361 : Model (fun x => f361 ((15/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(31776369018152843/100000000000000),(140350537616891/25000000000000),(679216603041/20000000000000),(323993051/5000000000000)⟩
def e362 : ℝ := (9219061/100000000000000)
theorem h362 : Model (fun x => f362 ((15/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(5131276247312167/100000000000000),(230374498884183/100000000000000),(2829271347373/100000000000000),(12916511373/100000000000000)⟩
def e363 : ℝ := (7473519/50000000000000)
theorem h363 : Model (fun x => f363 ((15/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(134903785032691/100000000000000),(255348077187/25000000000000),(562014613/100000000000000),(-3350173/100000000000000)⟩
def e364 : ℝ := (7083/50000000000000)
theorem h364 : Model (fun x => f364 ((15/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(10807404433839/5000000000000),(439693980497/100000000000000),(-590321101/100000000000000),(39627/5000000000000)⟩
def e365 : ℝ := (1587/100000000000000)
theorem h365 : Model (fun x => f365 ((15/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(467199962386251/100000000000000),(950390134871/50000000000000),(-618627589/100000000000000),(-1765093/100000000000000)⟩
def e366 : ℝ := (867/5000000000000)
theorem h366 : Model (fun x => f366 ((15/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(252460947249129/25000000000000),(6162750334489/100000000000000),(4262484757/100000000000000),(-3513311/25000000000000)⟩
def e367 : ℝ := (13991/25000000000000)
theorem h367 : Model (fun x => f367 ((15/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(272844756067143/12500000000000),(3468923713/19531250000),(7587300153/25000000000000),(-4001053/10000000000000)⟩
def e368 : ℝ := (175567/100000000000000)
theorem h368 : Model (fun x => f368 ((15/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2944623225582309/100000000000000),(11563658724163/25000000000000),(58654499489/25000000000000),(35337663/12500000000000)⟩
def e369 : ℝ := (692367/50000000000000)
theorem h369 : Model (fun x => f369 ((15/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(5807404433839/625000000000),(439693980497/12500000000000),(-590321101/12500000000000),(39627/625000000000)⟩
def e370 : ℝ := (1587/12500000000000)
theorem h370 : Model (fun x => f370 ((15/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1064088494446931/100000000000000),(1134736038181/25000000000000),(-832110839/20000000000000),(2990147/100000000000000)⟩
def e371 : ℝ := (13431/50000000000000)
theorem h371 : Model (fun x => f371 ((15/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1164088494446931/100000000000000),(1134736038181/25000000000000),(-832110839/20000000000000),(2990147/100000000000000)⟩
def e372 : ℝ := (13431/50000000000000)
theorem h372 : Model (fun x => f372 ((15/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(34278020173815757/100000000000000),(336049843348841/50000000000000),(2354060260487/50000000000000),(12103672663/100000000000000)⟩
def e373 : ℝ := (4288799/20000000000000)
theorem h373 : Model (fun x => f373 ((15/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(14586606737/5000000000000),(-2860040857/50000000000000),(72085699/100000000000000),(-18269/2500000000000)⟩
def e374 : ℝ := (107/1562500000000)
theorem h374 : Model (fun x => f374 ((15/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (33601200241480443/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(1496958173569/10000000000000),(189281624587/50000000000000),(-244959907/20000000000000),(2207367/50000000000000)⟩
def e375 : ℝ := (25191/3125000000000)
theorem h375 : Model (fun x => f375 ((15/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(132296177353561/50000000000000),(175877592199/10000000000000),(-1180642201/50000000000000),(39627/1250000000000)⟩
def e376 : ℝ := (317/5000000000000)
theorem h376 : Model (fun x => f376 ((15/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(8609698285977/20000000000000),(-81482884337/50000000000000),(835721891/100000000000000),(-17143/400000000000)⟩
def e377 : ℝ := (22287/100000000000000)
theorem h377 : Model (fun x => f377 ((15/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (46283121432423/20000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(56951508570113/50000000000000),(325931537347/100000000000000),(-208930473/12500000000000),(8571499/100000000000000)⟩
def e378 : ℝ := (162509/100000000000000)
theorem h378 : Model (fun x => f378 ((15/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(6951508570113/50000000000000),(325931537347/100000000000000),(-208930473/12500000000000),(8571499/100000000000000)⟩
def e379 : ℝ := (162509/100000000000000)
theorem h379 : Model (fun x => f379 ((15/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(84071274555881/20000000000000),(9397207643/781250000000),(-6168423489/100000000000000),(1977057/6250000000000)⟩
def e380 : ℝ := (299869/50000000000000)
theorem h380 : Model (fun x => f380 ((15/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(277607065849369/10000000000000),(9397207643/781250000000),(-6168423489/100000000000000),(1977057/6250000000000)⟩
def e381 : ℝ := (599739/100000000000000)
theorem h381 : Model (fun x => f381 ((15/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(790507059492213/25000000000000),(10418163763203/100000000000000),(-24753018809/50000000000000),(116886017/50000000000000)⟩
def e382 : ℝ := (5508783/100000000000000)
theorem h382 : Model (fun x => f382 ((15/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2111102297587451/25000000000000),(10418163763203/100000000000000),(-24753018809/50000000000000),(116886017/50000000000000)⟩
def e383 : ℝ := (344299/6250000000000)
theorem h383 : Model (fun x => f383 ((15/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2404609211868739/25000000000000),(9847398887719/25000000000000),(-32715268341/20000000000000),(654596309/100000000000000)⟩
def e384 : ℝ := (22523223/100000000000000)
theorem h384 : Model (fun x => f384 ((15/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(595499378660903/4000000000000),(9847398887719/25000000000000),(-32715268341/20000000000000),(654596309/100000000000000)⟩
def e385 : ℝ := (2815403/12500000000000)
theorem h385 : Model (fun x => f385 ((15/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(16957293983651691/100000000000000),(23347236191453/25000000000000),(-153385603953/50000000000000),(51885231/6250000000000)⟩
def e386 : ℝ := (14563781/25000000000000)
theorem h386 : Model (fun x => f386 ((15/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(2411626033670747/12500000000000),(23347236191453/25000000000000),(-153385603953/50000000000000),(51885231/6250000000000)⟩
def e387 : ℝ := (466041/800000000000)
theorem h387 : Model (fun x => f387 ((15/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(21975318515921147/100000000000000),(169254824216507/100000000000000),(-367509425601/100000000000000),(38473681/100000000000000)⟩
def e388 : ℝ := (56964343/50000000000000)
theorem h388 : Model (fun x => f388 ((15/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(22377699468302099/100000000000000),(169254824216507/100000000000000),(-367509425601/100000000000000),(38473681/100000000000000)⟩
def e389 : ℝ := (113928687/100000000000000)
theorem h389 : Model (fun x => f389 ((15/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(12744437430484201/50000000000000),(53144466267583/20000000000000),(-240980140197/100000000000000),(-206490139/10000000000000)⟩
def e390 : ℝ := (9379541/5000000000000)
theorem h390 : Model (fun x => f390 ((15/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(12735627906674677/50000000000000),(53144466267583/20000000000000),(-240980140197/100000000000000),(-206490139/10000000000000)⟩
def e391 : ℝ := (187590821/100000000000000)
theorem h391 : Model (fun x => f391 ((15/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(14506264437455063/50000000000000),(38568460826327/10000000000000),(165851507211/100000000000000),(-5395546213/100000000000000)⟩
def e392 : ℝ := (138099791/50000000000000)
theorem h392 : Model (fun x => f392 ((15/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(29015862208243459/100000000000000),(38568460826327/10000000000000),(165851507211/100000000000000),(-5395546213/100000000000000)⟩
def e393 : ℝ := (276199583/100000000000000)
theorem h393 : Model (fun x => f393 ((15/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(2017040148098223/50000000000000),(148193642963871/100000000000000),(198785577811/25000000000000),(-208449421/5000000000000)⟩
def e394 : ℝ := (99891291/100000000000000)
theorem h394 : Model (fun x => f394 ((15/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(64869486568233/50000000000000),(742491709699/100000000000000),(-274533613/10000000000000),(8630867/100000000000000)⟩
def e395 : ℝ := (455371/100000000000000)
theorem h395 : Model (fun x => f395 ((15/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(106951508570113/50000000000000),(325931537347/100000000000000),(-208930473/12500000000000),(8571499/100000000000000)⟩
def e396 : ℝ := (162509/100000000000000)
theorem h396 : Model (fun x => f396 ((15/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(228772503708459/50000000000000),(1394354784393/100000000000000),(-3044111849/50000000000000),(5154773/20000000000000)⟩
def e397 : ℝ := (780389/100000000000000)
theorem h397 : Model (fun x => f397 ((15/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(489351287819629/50000000000000),(559231303773/12500000000000),(-16125859781/100000000000000),(51200243/100000000000000)⟩
def e398 : ℝ := (27239/1000000000000)
theorem h398 : Model (fun x => f398 ((15/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(83738973524859/4000000000000),(637980070167/5000000000000),(-36270474491/100000000000000),(16517797/25000000000000)⟩
def e399 : ℝ := (4127669/50000000000000)
theorem h399 : Model (fun x => f399 ((15/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2716052109154229/100000000000000),(32098049242227/100000000000000),(-9790865923/100000000000000),(-353194147/100000000000000)⟩
def e400 : ℝ := (22955793/100000000000000)
theorem h400 : Model (fun x => f400 ((15/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(56951508570113/6250000000000),(325931537347/12500000000000),(-208930473/1562500000000),(8571499/12500000000000)⟩
def e401 : ℝ := (162509/12500000000000)
theorem h401 : Model (fun x => f401 ((15/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(520481555129137/50000000000000),(133997760339/4000000000000),(-8058443201/50000000000000),(77202859/100000000000000)⟩
def e402 : ℝ := (1755443/100000000000000)
theorem h402 : Model (fun x => f402 ((15/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(570481555129137/50000000000000),(133997760339/4000000000000),(-8058443201/50000000000000),(77202859/100000000000000)⟩
def e403 : ℝ := (1755443/100000000000000)
theorem h403 : Model (fun x => f403 ((15/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(15494576310420771/50000000000000),(28575820366501/6250000000000),(525813476019/100000000000000),(-1486827941/20000000000000)⟩
def e404 : ℝ := (32550867/10000000000000)
theorem h404 : Model (fun x => f404 ((15/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(516309697/160000000000),(-4761012131/100000000000000),(64768489/100000000000000),(-797397/100000000000000)⟩
def e405 : ℝ := (13191/100000000000000)
theorem h405 : Model (fun x => f405 ((15/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (7632851480463283/25000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(13017717346267/100000000000000),(286148290823/100000000000000),(-187683143/10000000000000),(12505269/100000000000000)⟩
def e406 : ℝ := (678117/50000000000000)
theorem h406 : Model (fun x => f406 ((15/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(27987299081957/100000000000000),(664711539997/100000000000000),(-620326193/20000000000000),(16920003/100000000000000)⟩
def e407 : ℝ := (1081173/50000000000000)
theorem h407 : Model (fun x => f407 ((15/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(34965496233181/20000000000000),(1101553290919/25000000000000),(-175186581/1562500000000),(32746361/25000000000000)⟩
def e408 : ℝ := (1894739/12500000000000)
theorem h408 : Model (fun x => f408 ((15/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(46620661644241/50000000000000),(34586334691/3125000000000),(-20736538101/100000000000000),(86586519/25000000000000)⟩
def e409 : ℝ := (4711811/25000000000000)
theorem h409 : Model (fun x => f409 ((15/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3191972780083/100000000000000),(65254968791/100000000000000),(1238149557/100000000000000),(-1523383/4000000000000)⟩
def e410 : ℝ := (65750373/50000000000000)
theorem h410 : Model (fun x => f410 ((15/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(3553390502929687/100000000000000),(55103302001953/25000000000000),(891/16384),(273/409600)⟩
def e411 : ℝ := (406250001/100000000000000)
theorem h411 : Model (fun x => f411 ((15/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1521/64),(39/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((15/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(59319/512),(4563/2560),(117/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((15/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(41168666258454317/10000000000000),(3983768373727791/12500000000000),(211081824302673/20000000000000),(19485403060913/100000000000000)⟩
def e414 : ℝ := (3444407191/1562500000000)
theorem h414 : Model (fun x => f414 ((15/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(607257953/2500000000000),(-1880400993/100000000000000),(83297409/100000000000000),(-173587/6250000000000)⟩
def e415 : ℝ := (117217/100000000000000)
theorem h415 : Model (fun x => f415 ((15/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (18937070031404317/5000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2812340651479/50000000000000),(420052233/2000000000000),(-176035733/12500000000000),(31457627/100000000000000)⟩
def e416 : ℝ := (26749043/50000000000000)
theorem h416 : Model (fun x => f416 ((15/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(19461668183/800000000000),(86257580441/100000000000000),(-170136307/100000000000000),(-1656737/25000000000000)⟩
def e417 : ℝ := (11562427/6250000000000)
theorem h417 : Model (fun x => f417 ((15/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((15/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((3648700217911/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (37/20) (19/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (37/20) (19/10) ≤ (3649255214407/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(15/8)-(1/40)) (by norm_num : ((15/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel17


noncomputable section
namespace Hf4Quad.Panel18
open Hf4Quad.Dag

def p0 : Cubic := ⟨(77/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((77/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((77/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((77/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((77/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(337333333333333/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((77/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-337333333333333/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((77/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-122952380952381/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((77/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((77/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(5929/1600),(77/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((77/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(56074537037037/12500000000000),(11651851851851/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((77/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-56074537037037/12500000000000),(-11651851851851/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((77/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-347250529100529/50000000000000),(-16032804232803/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((77/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((77/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(456533/64000),(17787/64000),(231/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((77/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(347485548755787/5000000000000),(67691990017361/25000000000000),(13736199273/390625000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((77/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-347485548755787/5000000000000),(-67691990017361/25000000000000),(-13736199273/390625000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((77/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-3822106016658399/50000000000000),(-286800764302247/100000000000000),(-3592128389549/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((77/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((77/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(35153041/2560000),(456533/640000),(17787/1280000),(77/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((77/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(1918072673611111/50000000000000),(199280277777777/100000000000000),(3882083333333/100000000000000),(33611111111/100000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((77/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-238004167880911/6250000000000),(-8752048652447/10000000000000),(36244367973/12500000000000),(9194155093/50000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((77/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((77/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(330417987915039/12500000000000),(42911427001953/25000000000000),(456533/10240000),(5929/10240000)⟩
def e22 : ℝ := (188476563/50000000000000)
theorem h22 : Model (fun x => f22 ((77/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(4305224005500397/25000000000000),(1118240001428671/100000000000000),(29045194842303/100000000000000),(377210322627/100000000000000)⟩
def e23 : ℝ := (2455779811/100000000000000)
theorem h23 : Model (fun x => f23 ((77/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(3353207333976753/25000000000000),(1030719514904201/100000000000000),(29335149786087/100000000000000),(395598632813/100000000000000)⟩
def e24 : ℝ := (641226701/25000000000000)
theorem h24 : Model (fun x => f24 ((77/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((77/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(12721092534729/250000000000),(79300317099609/20000000000000),(2574685620117/20000000000000),(111458251953/50000000000000)⟩
def e26 : ℝ := (545642091/25000000000000)
theorem h26 : Model (fun x => f26 ((77/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(11426098776167169/100000000000000),(890345359181853/100000000000000),(28907316856551/100000000000000),(500559599247/100000000000000)⟩
def e27 : ℝ := (2450481519/50000000000000)
theorem h27 : Model (fun x => f27 ((77/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(24838928112074181/100000000000000),(960532437043027/50000000000000),(29121233321319/50000000000000),(44807911603/5000000000000)⟩
def e28 : ℝ := (3732934921/50000000000000)
theorem h28 : Model (fun x => f28 ((77/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((77/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(979524125174133/10000000000000),(445238238715513/50000000000000),(34693888731077/100000000000000),(750949972533/100000000000000)⟩
def e30 : ℝ := (9828920909/100000000000000)
theorem h30 : Model (fun x => f30 ((77/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(581106574260051/25000000000000),(52827870387277/25000000000000),(8232914865549/100000000000000),(89100810233/50000000000000)⟩
def e31 : ℝ := (466483707/20000000000000)
theorem h31 : Model (fun x => f31 ((77/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(5432670881822877/20000000000000),(1066188177817581/50000000000000),(66475381508187/100000000000000),(537179926263/50000000000000)⟩
def e32 : ℝ := (9798288377/100000000000000)
theorem h32 : Model (fun x => f32 ((77/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((77/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2543541/320),(33033/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((77/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((77/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(170093/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((77/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(5265029/320),(10141/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((77/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((77/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(5994629/320),(10141/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((77/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-5994629/320),(-10141/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((77/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((77/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(117/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((77/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(13689/1600),(117/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((77/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((77/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(287469/160),(2457/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((77/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(13914543829/25000000000000),(-951421801/100000000000000),(2439543/20000000000000),(-69503/50000000000000)⟩
def e46 : ℝ := (381/25000000000000)
theorem h46 : Model (fun x => f46 ((77/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (141267/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1042656599488681/100000000000000),(92383063611/50000000000000),(-401912847/25000000000000),(13997103/100000000000000)⟩
def e47 : ℝ := (1778753/3125000000000)
theorem h47 : Model (fun x => f47 ((77/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((77/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(157/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((77/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((77/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((77/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(32708333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((77/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(57708333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((77/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((77/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(57708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((77/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((77/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1211874999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((77/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((77/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(7708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((77/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(74732291666663/20000000000000),(1430989583331/12500000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (21/25000000000000)
theorem h60 : Model (fun x => f60 ((77/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(66605034722221/50000000000000),(480902777777/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((77/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((77/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(57708333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((77/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(643688368055551/50000000000000),(2564236111107/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((77/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(693688368055551/50000000000000),(2564236111107/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((77/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(5184092144729891/100000000000000),(177988856698203/100000000000000),(549702419701/50000000000000),(41370081/2000000000000)⟩
def e66 : ℝ := (158569/25000000000000)
theorem h66 : Model (fun x => f66 ((77/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(107708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((77/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(232021701388887/50000000000000),(897569444443/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((77/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(999626830150451/100000000000000),(725067816839/12500000000000),(2243923611/20000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (47/100000000000000)
theorem h69 : Model (fun x => f69 ((77/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(51821575978441939/100000000000000),(519982459031749/25000000000000),(21895900424719/100000000000000),(26198360839/25000000000000)⟩
def e70 : ℝ := (16431273/6250000000000)
theorem h70 : Model (fun x => f70 ((77/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((77/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1398705729166641/6250000000000),(10098958333317/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((77/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1725070399305449/50000000000000),(118157812499807/100000000000000),(718229166661/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (223/25000000000000)
theorem h73 : Model (fun x => f73 ((77/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(1379541324035263/4000000000000),(1381264080197811/100000000000000),(14420498244009/100000000000000),(1682896561/2500000000000)⟩
def e74 : ℝ := (15982161/10000000000000)
theorem h74 : Model (fun x => f74 ((77/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(43155054539661757/50000000000000),(3461193916324807/100000000000000),(4539549833591/12500000000000),(43027326449/25000000000000)⟩
def e75 : ℝ := (211360989/50000000000000)
theorem h75 : Model (fun x => f75 ((77/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((77/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(466235243055547/6250000000000),(3366319444439/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((77/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(237673611111/10000000000000),(64236111111/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((77/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(91603370949/25000000000000),(7427300347/25000000000000),(200737847/25000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((77/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(27333580748233/100000000000000),(603397662613/25000000000000),(19064054747/25000000000000),(500493293/50000000000000)⟩
def e80 : ℝ := (4684113/100000000000000)
theorem h80 : Model (fun x => f80 ((77/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(11776217705697/20000000000000),(2656583222983/50000000000000),(8716261639/5000000000000),(2474026183/100000000000000)⟩
def e81 : ℝ := (14280657/100000000000000)
theorem h81 : Model (fun x => f81 ((77/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(86368990167851999/100000000000000),(3466507082770773/100000000000000),(9122680975377/25000000000000),(174583331979/100000000000000)⟩
def e82 : ℝ := (87400527/20000000000000)
theorem h82 : Model (fun x => f82 ((77/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(28244372709/50000000000000),(1526722849/25000000000000),(123788339/50000000000000),(111521/2500000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((77/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(1741736317/20000000000000),(588424431/50000000000000),(15903363/25000000000000),(859641/50000000000000)⟩
def e84 : ℝ := (11681/50000000000000)
theorem h84 : Model (fun x => f84 ((77/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(1342588411/100000000000000),(217717039/100000000000000),(1471061/10000000000000),(8283/1562500000000)⟩
def e85 : ℝ := (679/6250000000000)
theorem h85 : Model (fun x => f85 ((77/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(10349119/5000000000000),(9789707/25000000000000),(4961/156250000000),(143019/100000000000000)⟩
def e86 : ℝ := (3931/100000000000000)
theorem h86 : Model (fun x => f86 ((77/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(31047357/5000000000000),(29369121/25000000000000),(14883/156250000000),(429057/100000000000000)⟩
def e87 : ℝ := (11793/100000000000000)
theorem h87 : Model (fun x => f87 ((77/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-31047357/5000000000000),(-29369121/25000000000000),(-14883/156250000000),(-429057/100000000000000)⟩
def e88 : ℝ := (11793/100000000000000)
theorem h88 : Model (fun x => f88 ((77/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(86368989546904859/100000000000000),(3466506965294289/100000000000000),(9122678594097/25000000000000),(87291451461/50000000000000)⟩
def e89 : ℝ := (109253607/25000000000000)
theorem h89 : Model (fun x => f89 ((77/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1398705729166641/5000000000000),(10098958333317/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((77/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(538340699153939/25000000000000),(3332089433829/20000000000000),(24168927227/50000000000000),(6233121/10000000000000)⟩
def e91 : ℝ := (7569/25000000000000)
theorem h91 : Model (fun x => f91 ((77/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(602384176120151651/100000000000000),(9009956813099749/100000000000000),(5502352100937/10000000000000),(3516204267/2000000000000)⟩
def e92 : ℝ := (310922233/100000000000000)
theorem h92 : Model (fun x => f92 ((77/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(2075087709/12500000000000),(-1551871/625000000000),(2197497/100000000000000),(-15033/100000000000000)⟩
def e93 : ℝ := (109/100000000000000)
theorem h93 : Model (fun x => f93 ((77/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (593319019664906949/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(7168929145901/50000000000000),(45126353933/12500000000000),(-81455503/12500000000000),(196039/12500000000000)⟩
def e94 : ℝ := (326007/100000000000000)
theorem h94 : Model (fun x => f94 ((77/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(32708333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((77/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(43321299638989/100000000000000),(-31278916707/20000000000000),(70575173/12500000000000),(-2038273/100000000000000)⟩
def e96 : ℝ := (7389/100000000000000)
theorem h96 : Model (fun x => f96 ((77/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (114999999999997/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(5667870036101/5000000000000),(156394583533/50000000000000),(-1129202771/100000000000000),(2038271/50000000000000)⟩
def e97 : ℝ := (26717/50000000000000)
theorem h97 : Model (fun x => f97 ((77/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(119025270758121/5000000000000),(3284286254193/50000000000000),(-23713258191/100000000000000),(42803691/50000000000000)⟩
def e98 : ℝ := (561057/50000000000000)
theorem h98 : Model (fun x => f98 ((77/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(667870036101/5000000000000),(156394583533/50000000000000),(-1129202771/100000000000000),(2038271/50000000000000)⟩
def e99 : ℝ := (26717/50000000000000)
theorem h99 : Model (fun x => f99 ((77/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(31797364751263/10000000000000),(8323353611709/100000000000000),(-2375606199/25000000000000),(-19933891/50000000000000)⟩
def e100 : ℝ := (111709/5000000000000)
theorem h100 : Model (fun x => f100 ((77/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(64249501492263/50000000000000),(177284834763/25000000000000),(-158169919/10000000000000),(544519/25000000000000)⟩
def e101 : ℝ := (6393/4000000000000)
theorem h101 : Model (fun x => f101 ((77/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(5667870036101/500000000000),(156394583533/5000000000000),(-1129202771/10000000000000),(2038271/5000000000000)⟩
def e102 : ℝ := (26717/5000000000000)
theorem h102 : Model (fun x => f102 ((77/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(631036505102363/50000000000000),(239814438107/6250000000000),(-128737269/1000000000000),(5367937/12500000000000)⟩
def e103 : ℝ := (138833/20000000000000)
theorem h103 : Model (fun x => f103 ((77/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(681036505102363/50000000000000),(239814438107/6250000000000),(-128737269/1000000000000),(5367937/12500000000000)⟩
def e104 : ℝ := (138833/20000000000000)
theorem h104 : Model (fun x => f104 ((77/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1082758308083261/25000000000000),(3139272513669/2500000000000),(149004636673/100000000000000),(-1842616097/100000000000000)⟩
def e105 : ℝ := (3605127/10000000000000)
theorem h105 : Model (fun x => f105 ((77/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(10667870036101/5000000000000),(156394583533/50000000000000),(-1129202771/100000000000000),(2038271/50000000000000)⟩
def e106 : ℝ := (26717/50000000000000)
theorem h106 : Model (fun x => f106 ((77/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(227606902214283/50000000000000),(41709927287/3125000000000),(-960026183/25000000000000),(258279/2500000000000)⟩
def e107 : ℝ := (266693/100000000000000)
theorem h107 : Model (fun x => f107 ((77/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(971232340856607/100000000000000),(1067894600431/25000000000000),(-9158582243/100000000000000),(540647/4000000000000)⟩
def e108 : ℝ := (188833/20000000000000)
theorem h108 : Model (fun x => f108 ((77/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(42064395445665793/100000000000000),(702294338469423/50000000000000),(3207189723397/50000000000000),(-1402897359/6250000000000)⟩
def e109 : ℝ := (375469/80000000000)
theorem h109 : Model (fun x => f109 ((77/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1349239531337523/6250000000000),(3722981530023/3125000000000),(-3321568299/1250000000000),(11434899/3125000000000)⟩
def e110 : ℝ := (134253/500000000000)
theorem h110 : Model (fun x => f110 ((77/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(72089332360263/2500000000000),(20859448861359/25000000000000),(11672279441/12500000000000),(-1247526777/100000000000000)⟩
def e111 : ℝ := (24286589/100000000000000)
theorem h111 : Model (fun x => f111 ((77/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(28006196407619273/100000000000000),(58346809244111/6250000000000),(841387208037/20000000000000),(-3844907321/25000000000000)⟩
def e112 : ℝ := (63124777/20000000000000)
theorem h112 : Model (fun x => f112 ((77/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(35035295926642533/50000000000000),(1169068812422311/50000000000000),(10621315486979/100000000000000),(-9456496757/25000000000000)⟩
def e113 : ℝ := (156992027/20000000000000)
theorem h113 : Model (fun x => f113 ((77/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(449746510445841/6250000000000),(1240993843341/3125000000000),(-1107189433/1250000000000),(3811633/3125000000000)⟩
def e114 : ℝ := (44751/500000000000)
theorem h114 : Model (fun x => f114 ((77/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(892100770243/50000000000000),(2089025123/2500000000000),(42294147/6250000000000),(-186719/3125000000000)⟩
def e115 : ℝ := (52957/100000000000000)
theorem h115 : Model (fun x => f115 ((77/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(238322949451/100000000000000),(16742367411/100000000000000),(331612897/100000000000000),(223859/50000000000000)⟩
def e116 : ℝ := (1563/5000000000000)
theorem h116 : Model (fun x => f116 ((77/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(17149586379959/100000000000000),(129941375131/10000000000000),(30300279959/100000000000000),(149368107/100000000000000)⟩
def e117 : ℝ := (2380273/100000000000000)
theorem h117 : Model (fun x => f117 ((77/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(18294955867429/50000000000000),(706509363203/25000000000000),(8564832697/12500000000000),(399489997/100000000000000)⟩
def e118 : ℝ := (2637161/50000000000000)
theorem h118 : Model (fun x => f118 ((77/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(17526795441254981/25000000000000),(1170481831148717/50000000000000),(2137966829711/20000000000000),(-37426497031/100000000000000)⟩
def e119 : ℝ := (790234457/100000000000000)
theorem h119 : Model (fun x => f119 ((77/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(3183375137/10000000000000),(2981793473/100000000000000),(3758881/4000000000000),(57357/6250000000000)⟩
def e120 : ℝ := (1521/25000000000000)
theorem h120 : Model (fun x => f120 ((77/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(850432347/20000000000000),(124465657/25000000000000),(21519479/100000000000000),(24009/6250000000000)⟩
def e121 : ℝ := (279/10000000000000)
theorem h121 : Model (fun x => f121 ((77/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(283989141/50000000000000),(79801807/100000000000000),(4383687/100000000000000),(113173/100000000000000)⟩
def e122 : ℝ := (1369/100000000000000)
theorem h122 : Model (fun x => f122 ((77/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(15173427/20000000000000),(12436021/100000000000000),(103593/12500000000000),(559/2000000000000)⟩
def e123 : ℝ := (499/100000000000000)
theorem h123 : Model (fun x => f123 ((77/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(45520281/20000000000000),(37308063/100000000000000),(310779/12500000000000),(1677/2000000000000)⟩
def e124 : ℝ := (1497/100000000000000)
theorem h124 : Model (fun x => f124 ((77/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-45520281/20000000000000),(-37308063/100000000000000),(-310779/12500000000000),(-1677/2000000000000)⟩
def e125 : ℝ := (1497/100000000000000)
theorem h125 : Model (fun x => f125 ((77/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(70107181537418519/100000000000000),(2340963624989371/100000000000000),(10689831662323/100000000000000),(-37426580881/100000000000000)⟩
def e126 : ℝ := (395117977/50000000000000)
theorem h126 : Model (fun x => f126 ((77/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1349239531337523/5000000000000),(3722981530023/2500000000000),(-3321568299/1000000000000),(11434899/2500000000000)⟩
def e127 : ℝ := (134253/400000000000)
theorem h127 : Model (fun x => f127 ((77/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1036098038711643/50000000000000),(6075819098481/50000000000000),(-857333051/5000000000000),(-8451381/100000000000000)⟩
def e128 : ℝ := (2859023/100000000000000)
theorem h128 : Model (fun x => f128 ((77/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(111835554573681917/20000000000000),(397812075893977/6250000000000),(6586198450917/100000000000000),(-11739924691/20000000000000)⟩
def e129 : ℝ := (1575348681/100000000000000)
theorem h129 : Model (fun x => f129 ((77/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(17883400387/100000000000000),(-203562673/100000000000000),(210647/10000000000000),(-19703/100000000000000)⟩
def e130 : ℝ := (117/50000000000000)
theorem h130 : Model (fun x => f130 ((77/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (5528061331806829/1000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(12537547974377/100000000000000),(68982961317/25000000000000),(-688417993/50000000000000),(3522413/50000000000000)⟩
def e131 : ℝ := (5941/1250000000000)
theorem h131 : Model (fun x => f131 ((77/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(26875406266179/100000000000000),(159235669183/25000000000000),(-202848001/10000000000000),(4306569/50000000000000)⟩
def e132 : ℝ := (801287/100000000000000)
theorem h132 : Model (fun x => f132 ((77/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-28021819707371/10000000000000),(-6591468206573/100000000000000),(2736859021/12500000000000),(-25007859/25000000000000)⟩
def e133 : ℝ := (4831097/20000000000000)
theorem h133 : Model (fun x => f133 ((77/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(51948051948051/100000000000000),(-6746500253/1000000000000),(27380277/312500000000),(-22757633/20000000000000)⟩
def e134 : ℝ := (11697/781250000000)
theorem h134 : Model (fun x => f134 ((77/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (19/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-145567894583743/100000000000000),(-1533647190637/100000000000000),(625829111/2000000000000),(-11458673/2500000000000)⟩
def e135 : ℝ := (2713523/10000000000000)
theorem h135 : Model (fun x => f135 ((77/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(35153041/256000),(456533/64000),(17787/128000),(77/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((77/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((77/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(4108797/32000),(160083/32000),(2079/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((77/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(68023417/256000),(776699/64000),(26103/128000),(19/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((77/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-5929/1600),(-77/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((77/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(67074777/256000),(770539/64000),(26023/128000),(19/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((77/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((77/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(231/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((77/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-231/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((77/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(64117977/256000),(760939/64000),(26023/128000),(19/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((77/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(64885977/256000),(760939/64000),(26023/128000),(19/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((77/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((77/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(64885977/4000),(760939/1000),(26023/2000),(19/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((77/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((77/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(6643924749/512000),(86284737/128000),(3361743/256000),(14553/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((77/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(3853144183/50000000000000),(-400326669/100000000000000),(12997619/100000000000000),(-337601/100000000000000)⟩
def e151 : ℝ := (8823/100000000000000)
theorem h151 : Model (fun x => f151 ((77/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (3146001957/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(12500751241791/10000000000000),(-62988139637/10000000000000),(1621749441/25000000000000),(-12550107/20000000000000)⟩
def e152 : ℝ := (140488957/50000000000000)
theorem h152 : Model (fun x => f152 ((77/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(197/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((77/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(30929/1600),(177/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((77/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(351/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((77/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1139601139601/20000000000000),(-24350451701/50000000000000),(416247037/100000000000000),(-3557667/100000000000000)⟩
def e156 : ℝ := (1917/6250000000000)
theorem h156 : Model (fun x => f156 ((77/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (87/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(110146011395997/100000000000000),(159632429929/50000000000000),(832494063/100000000000000),(-1423067/20000000000000)⟩
def e157 : ℝ := (28223/2500000000000)
theorem h157 : Model (fun x => f157 ((77/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(210146011395997/100000000000000),(159632429929/50000000000000),(832494063/100000000000000),(-1423067/20000000000000)⟩
def e158 : ℝ := (28223/2500000000000)
theorem h158 : Model (fun x => f158 ((77/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(52536502848999/50000000000000),(159632429929/100000000000000),(416247031/100000000000000),(-889417/25000000000000)⟩
def e159 : ℝ := (282231/50000000000000)
theorem h159 : Model (fun x => f159 ((77/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(2536502848999/50000000000000),(159632429929/100000000000000),(416247031/100000000000000),(-889417/25000000000000)⟩
def e160 : ℝ := (282231/50000000000000)
theorem h160 : Model (fun x => f160 ((77/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((77/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((77/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(38776942579023/10000000000000),(14727992047/2500000000000),(1536149757/100000000000000),(-1312949/10000000000000)⟩
def e163 : ℝ := (2083137/100000000000000)
theorem h163 : Model (fun x => f163 ((77/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(548696742300903/20000000000000),(14727992047/2500000000000),(1536149757/100000000000000),(-1312949/10000000000000)⟩
def e164 : ℝ := (1041569/50000000000000)
theorem h164 : Model (fun x => f164 ((77/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((77/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1441330398256393/50000000000000),(499849547029/10000000000000),(349354357/2500000000000),(-53247603/50000000000000)⟩
def e166 : ℝ := (8858521/50000000000000)
theorem h166 : Model (fun x => f166 ((77/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4082520874446869/50000000000000),(499849547029/10000000000000),(349354357/2500000000000),(-53247603/50000000000000)⟩
def e167 : ℝ := (17717043/100000000000000)
theorem h167 : Model (fun x => f167 ((77/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((77/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1072406847757379/12500000000000),(4571530994697/25000000000000),(110642673/195312500000),(-359269389/100000000000000)⟩
def e169 : ℝ := (65051649/100000000000000)
theorem h169 : Model (fun x => f169 ((77/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13848302401106651/100000000000000),(4571530994697/25000000000000),(110642673/195312500000),(-359269389/100000000000000)⟩
def e170 : ℝ := (1301033/2000000000000)
theorem h170 : Model (fun x => f170 ((77/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((77/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(2910165514198157/20000000000000),(41320161716977/100000000000000),(146356589673/100000000000000),(-175906517/25000000000000)⟩
def e172 : ℝ := (73859791/50000000000000)
theorem h172 : Model (fun x => f172 ((77/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(1688654185670507/10000000000000),(41320161716977/100000000000000),(146356589673/100000000000000),(-175906517/25000000000000)⟩
def e173 : ℝ := (147719583/100000000000000)
theorem h173 : Model (fun x => f173 ((77/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((77/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(3548639417458107/20000000000000),(70372732972137/100000000000000),(290031375123/100000000000000),(-233615407/25000000000000)⟩
def e175 : ℝ := (252994221/100000000000000)
theorem h175 : Model (fun x => f175 ((77/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(18145578039671487/100000000000000),(70372732972137/100000000000000),(290031375123/100000000000000),(-233615407/25000000000000)⟩
def e176 : ℝ := (126497111/50000000000000)
theorem h176 : Model (fun x => f176 ((77/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((77/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(3813220849511739/20000000000000),(102908972875041/100000000000000),(492612816807/100000000000000),(-4357589/500000000000)⟩
def e178 : ℝ := (5810307/1562500000000)
theorem h178 : Model (fun x => f178 ((77/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(19048485199939647/100000000000000),(102908972875041/100000000000000),(492612816807/100000000000000),(-4357589/500000000000)⟩
def e179 : ℝ := (371859649/100000000000000)
theorem h179 : Model (fun x => f179 ((77/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((77/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(20014815939514891/100000000000000),(17317138840259/12500000000000),(761167941183/100000000000000),(-378686457/100000000000000)⟩
def e181 : ℝ := (100489499/20000000000000)
theorem h181 : Model (fun x => f181 ((77/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(625567164776507/3125000000000),(17317138840259/12500000000000),(761167941183/100000000000000),(-378686457/100000000000000)⟩
def e182 : ℝ := (62805937/12500000000000)
theorem h182 : Model (fun x => f182 ((77/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(203104370649067/20000000000000),(19491726815917/50000000000000),(68617840247/20000000000000),(530168707/50000000000000)⟩
def e183 : ℝ := (28493607/20000000000000)
theorem h183 : Model (fun x => f183 ((77/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(22080673052823/20000000000000),(33546118439/10000000000000),(56477583/5000000000000),(-6147367/100000000000000)⟩
def e184 : ℝ := (598829/50000000000000)
theorem h184 : Model (fun x => f184 ((77/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(102536502848999/50000000000000),(159632429929/100000000000000),(416247031/100000000000000),(-889417/25000000000000)⟩
def e185 : ℝ := (282231/50000000000000)
theorem h185 : Model (fun x => f185 ((77/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(420549376660111/100000000000000),(81840755531/12500000000000),(981022861/50000000000000),(-13262703/100000000000000)⟩
def e186 : ℝ := (1163291/50000000000000)
theorem h186 : Model (fun x => f186 ((77/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(215608311790271/25000000000000),(6293748647/312500000000),(6819305523/100000000000000),(-9075659/25000000000000)⟩
def e187 : ℝ := (718889/10000000000000)
theorem h187 : Model (fun x => f187 ((77/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(884308891046039/50000000000000),(688361574479/12500000000000),(20789404037/100000000000000),(-42930191/50000000000000)⟩
def e188 : ℝ := (4933777/25000000000000)
theorem h188 : Model (fun x => f188 ((77/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(976306775044603/50000000000000),(12012820906417/100000000000000),(15350785079/25000000000000),(-357863/500000000000)⟩
def e189 : ℝ := (43496833/100000000000000)
theorem h189 : Model (fun x => f189 ((77/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((77/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(52536502848999/6250000000000),(159632429929/12500000000000),(416247031/12500000000000),(-889417/3125000000000)⟩
def e191 : ℝ := (282231/6250000000000)
theorem h191 : Model (fun x => f191 ((77/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(950987410848099/100000000000000),(806260311911/50000000000000),(1114881977/25000000000000),(-34608711/100000000000000)⟩
def e192 : ℝ := (2856677/50000000000000)
theorem h192 : Model (fun x => f192 ((77/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1050987410848099/100000000000000),(806260311911/50000000000000),(1114881977/25000000000000),(-34608711/100000000000000)⟩
def e193 : ℝ := (2856677/50000000000000)
theorem h193 : Model (fun x => f193 ((77/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(10260861296975847/50000000000000),(78869765806451/50000000000000),(463062917703/50000000000000),(48930003/50000000000000)⟩
def e194 : ℝ := (572696949/100000000000000)
theorem h194 : Model (fun x => f194 ((77/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(487288528251/100000000000000),(-374552691/10000000000000),(3399499/50000000000000),(7153/6250000000000)⟩
def e195 : ℝ := (3749/25000000000000)
theorem h195 : Model (fun x => f195 ((77/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (20363056265946431/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2474260746373/50000000000000),(151925253173/100000000000000),(280743883/100000000000000),(-967717/25000000000000)⟩
def e196 : ℝ := (443229/50000000000000)
theorem h196 : Model (fun x => f196 ((77/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(110146011395997/50000000000000),(159632429929/25000000000000),(832494063/50000000000000),(-1423067/10000000000000)⟩
def e197 : ℝ := (28223/1250000000000)
theorem h197 : Model (fun x => f197 ((77/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(11896490365877/25000000000000),(-72295092431/100000000000000),(-78677429/100000000000000),(2017141/100000000000000)⟩
def e198 : ℝ := (65409/25000000000000)
theorem h198 : Model (fun x => f198 ((77/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (209825905797821/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(5241403853649/5000000000000),(144590184861/100000000000000),(157354857/100000000000000),(-1008571/25000000000000)⟩
def e199 : ℝ := (209499/12500000000000)
theorem h199 : Model (fun x => f199 ((77/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(241403853649/5000000000000),(144590184861/100000000000000),(157354857/100000000000000),(-1008571/25000000000000)⟩
def e200 : ℝ := (209499/12500000000000)
theorem h200 : Model (fun x => f200 ((77/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(77373104506247/20000000000000),(266803317303/50000000000000),(580714353/100000000000000),(-1488843/10000000000000)⟩
def e201 : ℝ := (6185211/100000000000000)
theorem h201 : Model (fun x => f201 ((77/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(34282247603069/1250000000000),(266803317303/50000000000000),(580714353/100000000000000),(-1488843/10000000000000)⟩
def e202 : ℝ := (1546303/25000000000000)
theorem h202 : Model (fun x => f202 ((77/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(7187484187939/250000000000),(4524870788893/100000000000000),(1423969261/25000000000000),(-62285701/50000000000000)⟩
def e203 : ℝ := (10501871/20000000000000)
theorem h203 : Model (fun x => f203 ((77/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1019671828444569/12500000000000),(4524870788893/100000000000000),(1423969261/25000000000000),(-62285701/50000000000000)⟩
def e204 : ℝ := (13127339/25000000000000)
theorem h204 : Model (fun x => f204 ((77/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8551218961706697/100000000000000),(16538098091821/100000000000000),(6337355649/25000000000000),(-222160841/50000000000000)⟩
def e205 : ℝ := (48066893/25000000000000)
theorem h205 : Model (fun x => f205 ((77/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(3455066645188579/25000000000000),(16538098091821/100000000000000),(6337355649/25000000000000),(-222160841/50000000000000)⟩
def e206 : ℝ := (192267573/100000000000000)
theorem h206 : Model (fun x => f206 ((77/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(905469981435277/6250000000000),(18659659605747/50000000000000),(2889305583/4000000000000),(-480323201/50000000000000)⟩
def e207 : ℝ := (217502189/50000000000000)
theorem h207 : Model (fun x => f207 ((77/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16823233988678717/100000000000000),(18659659605747/50000000000000),(2889305583/4000000000000),(-480323201/50000000000000)⟩
def e208 : ℝ := (435004379/100000000000000)
theorem h208 : Model (fun x => f208 ((77/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(4408868172954973/25000000000000),(12689173965993/20000000000000),(156152335507/100000000000000),(-19031989/1250000000000)⟩
def e209 : ℝ := (371002267/50000000000000)
theorem h209 : Model (fun x => f209 ((77/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(4509463411050211/25000000000000),(12689173965993/20000000000000),(156152335507/100000000000000),(-19031989/1250000000000)⟩
def e210 : ℝ := (148400907/20000000000000)
theorem h210 : Model (fun x => f210 ((77/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(1181795945028387/6250000000000),(23147512813521/25000000000000),(141905714949/50000000000000),(-1998151583/100000000000000)⟩
def e211 : ℝ := (1086806239/100000000000000)
theorem h211 : Model (fun x => f211 ((77/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(2361389509104393/12500000000000),(23147512813521/25000000000000),(141905714949/50000000000000),(-1998151583/100000000000000)⟩
def e212 : ℝ := (6792539/625000000000)
theorem h212 : Model (fun x => f212 ((77/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(19803193716777737/100000000000000),(124375069942561/100000000000000),(115279069857/25000000000000),(-2300686741/100000000000000)⟩
def e213 : ℝ := (1465214019/100000000000000)
theorem h213 : Model (fun x => f213 ((77/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(1980652705011107/10000000000000),(124375069942561/100000000000000),(115279069857/25000000000000),(-2300686741/100000000000000)⟩
def e214 : ℝ := (73260701/5000000000000)
theorem h214 : Model (fun x => f214 ((77/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(478137195729997/50000000000000),(34643218312699/100000000000000),(116631862617/50000000000000),(-47691387/100000000000000)⟩
def e215 : ℝ := (414551639/100000000000000)
theorem h215 : Model (fun x => f215 ((77/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(54944628714093/50000000000000),(75785555213/25000000000000),(538967357/100000000000000),(-4001543/50000000000000)⟩
def e216 : ℝ := (1765053/50000000000000)
theorem h216 : Model (fun x => f216 ((77/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(10241403853649/5000000000000),(144590184861/100000000000000),(157354857/100000000000000),(-1008571/25000000000000)⟩
def e217 : ℝ := (209499/12500000000000)
theorem h217 : Model (fun x => f217 ((77/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(209772705787073/50000000000000),(296161295287/50000000000000),(853677071/100000000000000),(-8035827/50000000000000)⟩
def e218 : ℝ := (688209/10000000000000)
theorem h218 : Model (fun x => f218 ((77/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(429673399487621/50000000000000),(113741528657/6250000000000),(163259287/5000000000000),(-11919633/25000000000000)⟩
def e219 : ℝ := (21193757/100000000000000)
theorem h219 : Model (fun x => f219 ((77/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(352036704745839/20000000000000),(248506225047/5000000000000),(426863459/4000000000000),(-15592841/12500000000000)⟩
def e220 : ℝ := (58012013/100000000000000)
theorem h220 : Model (fun x => f220 ((77/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(193425260359929/10000000000000),(5398746166121/50000000000000),(1814014377/5000000000000),(-109405213/50000000000000)⟩
def e221 : ℝ := (126957259/100000000000000)
theorem h221 : Model (fun x => f221 ((77/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(5241403853649/625000000000),(144590184861/12500000000000),(157354857/12500000000000),(-1008571/3125000000000)⟩
def e222 : ℝ := (209499/1562500000000)
theorem h222 : Model (fun x => f222 ((77/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(474256937006013/50000000000000),(72993184987/5000000000000),(1797806213/100000000000000),(-20138679/50000000000000)⟩
def e223 : ℝ := (8469021/50000000000000)
theorem h223 : Model (fun x => f223 ((77/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(524256937006013/50000000000000),(72993184987/5000000000000),(1797806213/100000000000000),(-20138679/50000000000000)⟩
def e224 : ℝ := (8469021/50000000000000)
theorem h224 : Model (fun x => f224 ((77/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(1267556681698587/6250000000000),(141450656770163/100000000000000),(572806632911/100000000000000),(-469912557/20000000000000)⟩
def e225 : ℝ := (417347371/25000000000000)
theorem h225 : Model (fun x => f225 ((77/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(493074596997/100000000000000),(-1719492277/50000000000000),(402369/4000000000000),(84093/100000000000000)⟩
def e226 : ℝ := (42441/100000000000000)
theorem h226 : Model (fun x => f226 ((77/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (20138879424822049/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1178786525469/25000000000000),(27586156093/20000000000000),(54983039/100000000000000),(-3968059/100000000000000)⟩
def e227 : ℝ := (2533433/100000000000000)
theorem h227 : Model (fun x => f227 ((77/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(4831833797311/50000000000000),(144928016819/50000000000000),(167863461/50000000000000),(-7838927/100000000000000)⟩
def e228 : ℝ := (3419891/100000000000000)
theorem h228 : Model (fun x => f228 ((77/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(3020077617093/25000000000000),(150736086429/50000000000000),(-389591729/50000000000000),(412511/50000000000000)⟩
def e229 : ℝ := (16188261/50000000000000)
theorem h229 : Model (fun x => f229 ((77/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(1255097191519/20000000000000),(37554551667/50000000000000),(-1380213529/100000000000000),(18353433/100000000000000)⟩
def e230 : ℝ := (17643507/100000000000000)
theorem h230 : Model (fun x => f230 ((77/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-34823102156537/25000000000000),(-1458538087303/100000000000000),(29911242021/100000000000000),(-439993487/100000000000000)⟩
def e231 : ℝ := (44778737/100000000000000)
theorem h231 : Model (fun x => f231 ((77/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((77/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-5929/320),(-77/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((77/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1617/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((77/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(7007/320),(7/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((77/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((77/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15327/320),(7/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((77/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((77/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(383175/32),(175/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((77/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(12551/1600),(43/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((77/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(22151/1600),(43/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((77/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((77/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4186539/1600),(8127/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((77/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(19108862953/50000000000000),(-18547269/12500000000000),(2301397/100000000000000),(-7817/50000000000000)⟩
def e244 : ℝ := (169/100000000000000)
theorem h244 : Model (fun x => f244 ((77/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (260631/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(91525482025197/20000000000000),(-42459564771/3125000000000),(-3923053293/100000000000000),(-1844519/4000000000000)⟩
def e245 : ℝ := (2003401/50000000000000)
theorem h245 : Model (fun x => f245 ((77/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(693/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((77/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(61369/1600),(437/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((77/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(94969/1600),(437/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((77/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(24649/1600),(157/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((77/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2340890881/2560000),(12840873/640000),(197027/1280000),(297/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((77/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((77/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(123201/160),(1053/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((77/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(64934537869/50000000000000),(-2219984201/100000000000000),(5692267/20000000000000),(-162173/50000000000000)⟩
def e253 : ℝ := (111/3125000000000)
theorem h253 : Model (fun x => f253 ((77/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (60543/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(29688411632713/25000000000000),(287849308717/50000000000000),(368571053/25000000000000),(-1397987/20000000000000)⟩
def e254 : ℝ := (1641287/25000000000000)
theorem h254 : Model (fun x => f254 ((77/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(54688411632713/25000000000000),(287849308717/50000000000000),(368571053/25000000000000),(-1397987/20000000000000)⟩
def e255 : ℝ := (1641287/25000000000000)
theorem h255 : Model (fun x => f255 ((77/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(54688411632713/50000000000000),(287849308717/100000000000000),(368571053/50000000000000),(-436871/12500000000000)⟩
def e256 : ℝ := (131303/4000000000000)
theorem h256 : Model (fun x => f256 ((77/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(4688411632713/50000000000000),(287849308717/100000000000000),(368571053/50000000000000),(-436871/12500000000000)⟩
def e257 : ℝ := (131303/4000000000000)
theorem h257 : Model (fun x => f257 ((77/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(12614142564093/3125000000000),(212460204053/20000000000000),(2720405391/100000000000000),(-12898097/100000000000000)⟩
def e258 : ℝ := (12114267/100000000000000)
theorem h258 : Model (fun x => f258 ((77/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2759366847765261/100000000000000),(212460204053/20000000000000),(2720405391/100000000000000),(-12898097/100000000000000)⟩
def e259 : ℝ := (3028567/25000000000000)
theorem h259 : Model (fun x => f259 ((77/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1509053900162483/50000000000000),(455236475287/5000000000000),(26373774033/100000000000000),(-94885181/100000000000000)⟩
def e260 : ℝ := (103952803/100000000000000)
theorem h260 : Model (fun x => f260 ((77/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4150244376352959/50000000000000),(455236475287/5000000000000),(26373774033/100000000000000),(-94885181/100000000000000)⟩
def e261 : ℝ := (25988201/25000000000000)
theorem h261 : Model (fun x => f261 ((77/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4539405456606857/50000000000000),(8462840848771/25000000000000),(23248218951/20000000000000),(-125425151/50000000000000)⟩
def e262 : ℝ := (96792083/25000000000000)
theorem h262 : Model (fun x => f262 ((77/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14347858532261333/100000000000000),(8462840848771/25000000000000),(23248218951/20000000000000),(-125425151/50000000000000)⟩
def e263 : ℝ := (387168333/100000000000000)
theorem h263 : Model (fun x => f263 ((77/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(15693231869204823/100000000000000),(15665151502877/20000000000000),(165172919423/50000000000000),(-47923329/25000000000000)⟩
def e264 : ℝ := (897738229/100000000000000)
theorem h264 : Model (fun x => f264 ((77/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(4507236538729777/25000000000000),(15665151502877/20000000000000),(165172919423/50000000000000),(-47923329/25000000000000)⟩
def e265 : ℝ := (89773823/10000000000000)
theorem h265 : Model (fun x => f265 ((77/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(19719488572484689/100000000000000),(137566422243709/100000000000000),(719680889247/100000000000000),(688496393/100000000000000)⟩
def e266 : ℝ := (789885549/50000000000000)
theorem h266 : Model (fun x => f266 ((77/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(20121869524865641/100000000000000),(137566422243709/100000000000000),(719680889247/100000000000000),(688496393/100000000000000)⟩
def e267 : ℝ := (1579771099/100000000000000)
theorem h267 : Model (fun x => f267 ((77/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(11004330833955953/50000000000000),(208386444858333/100000000000000),(83217178909/6250000000000),(783864767/25000000000000)⟩
def e268 : ℝ := (1200008243/50000000000000)
theorem h268 : Model (fun x => f268 ((77/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(10995521310146429/50000000000000),(208386444858333/100000000000000),(83217178909/6250000000000),(783864767/25000000000000)⟩
def e269 : ℝ := (2400016487/100000000000000)
theorem h269 : Model (fun x => f269 ((77/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(12026551910511113/50000000000000),(291227537663977/100000000000000),(443653816583/20000000000000),(2007407759/25000000000000)⟩
def e270 : ℝ := (843081387/25000000000000)
theorem h270 : Model (fun x => f270 ((77/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(24056437154355559/100000000000000),(291227537663977/100000000000000),(443653816583/20000000000000),(2007407759/25000000000000)⟩
def e271 : ℝ := (3372325549/100000000000000)
theorem h271 : Model (fun x => f271 ((77/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(563932398980549/25000000000000),(19310835911551/20000000000000),(305907438221/25000000000000),(1688838511/20000000000000)⟩
def e272 : ℝ := (144319761/12500000000000)
theorem h272 : Model (fun x => f272 ((77/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(59816447338181/50000000000000),(157420214833/25000000000000),(1220548741/50000000000000),(-1700827/50000000000000)⟩
def e273 : ℝ := (180361/2500000000000)
theorem h273 : Model (fun x => f273 ((77/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(104688411632713/50000000000000),(287849308717/100000000000000),(368571053/50000000000000),(-436871/12500000000000)⟩
def e274 : ℝ := (131303/4000000000000)
theorem h274 : Model (fun x => f274 ((77/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(219193270603607/50000000000000),(602689738383/50000000000000),(1957690847/50000000000000),(-1039159/10000000000000)⟩
def e275 : ℝ := (1377959/10000000000000)
theorem h275 : Model (fun x => f275 ((77/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(458939906801421/50000000000000),(3785677885119/100000000000000),(14899110083/100000000000000),(-4230823/25000000000000)⟩
def e276 : ℝ := (10841123/25000000000000)
theorem h276 : Model (fun x => f276 ((77/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(480456898779061/25000000000000),(660527674577/6250000000000),(48858409597/100000000000000),(1639877/50000000000000)⟩
def e277 : ℝ := (30311759/25000000000000)
theorem h277 : Model (fun x => f277 ((77/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(574784495681669/25000000000000),(12372357275783/50000000000000),(42977969031/25000000000000),(504187783/100000000000000)⟩
def e278 : ℝ := (71522069/25000000000000)
theorem h278 : Model (fun x => f278 ((77/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(54688411632713/6250000000000),(287849308717/12500000000000),(368571053/6250000000000),(-436871/1562500000000)⟩
def e279 : ℝ := (131303/500000000000)
theorem h279 : Model (fun x => f279 ((77/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(99464748079977/10000000000000),(733118832267/25000000000000),(833823433/10000000000000),(-15680699/50000000000000)⟩
def e280 : ℝ := (209219/625000000000)
theorem h280 : Model (fun x => f280 ((77/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(109464748079977/10000000000000),(733118832267/25000000000000),(833823433/10000000000000),(-15680699/50000000000000)⟩
def e281 : ℝ := (209219/625000000000)
theorem h281 : Model (fun x => f281 ((77/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(25167456008028209/100000000000000),(169144524297251/50000000000000),(2799169183229/100000000000000),(1190258269/10000000000000)⟩
def e282 : ℝ := (3939421337/100000000000000)
theorem h282 : Model (fun x => f282 ((77/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(39733853103/10000000000000),(-2670418369/50000000000000),(5519261/20000000000000),(7033/20000000000000)⟩
def e283 : ℝ := (64951/100000000000000)
theorem h283 : Model (fun x => f283 ((77/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (24826351948246451/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(4481441420223/50000000000000),(263172123733/100000000000000),(32764941/10000000000000),(-272589/6250000000000)⟩
def e284 : ℝ := (3130123/50000000000000)
theorem h284 : Model (fun x => f284 ((77/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(29688411632713/12500000000000),(287849308717/25000000000000),(368571053/12500000000000),(-1397987/10000000000000)⟩
def e285 : ℝ := (1641287/12500000000000)
theorem h285 : Model (fun x => f285 ((77/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(45713523676459/100000000000000),(-120305251117/100000000000000),(8524843/100000000000000),(2249063/100000000000000)⟩
def e286 : ℝ := (27781/2000000000000)
theorem h286 : Model (fun x => f286 ((77/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (218176460074123/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(54286476323539/50000000000000),(30076312779/12500000000000),(-17049687/100000000000000),(-4498131/100000000000000)⟩
def e287 : ℝ := (9376283/100000000000000)
theorem h287 : Model (fun x => f287 ((77/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(4286476323539/50000000000000),(30076312779/12500000000000),(-17049687/100000000000000),(-4498131/100000000000000)⟩
def e288 : ℝ := (9376283/100000000000000)
theorem h288 : Model (fun x => f288 ((77/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(20034294833687/5000000000000),(177593465933/20000000000000),(-7865183/12500000000000),(-8300123/50000000000000)⟩
def e289 : ℝ := (34602951/100000000000000)
theorem h289 : Model (fun x => f289 ((77/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(110256007295521/4000000000000),(177593465933/20000000000000),(-7865183/12500000000000),(-8300123/50000000000000)⟩
def e290 : ℝ := (4325369/12500000000000)
theorem h290 : Model (fun x => f290 ((77/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1496352532394061/50000000000000),(3798140335363/50000000000000),(399567339/25000000000000),(-7115633/5000000000000)⟩
def e291 : ℝ := (59252749/20000000000000)
theorem h291 : Model (fun x => f291 ((77/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4137543008584537/50000000000000),(3798140335363/50000000000000),(399567339/25000000000000),(-7115633/5000000000000)⟩
def e292 : ℝ := (148131873/50000000000000)
theorem h292 : Model (fun x => f292 ((77/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(8984505222925951/100000000000000),(14079116120803/50000000000000),(9300930519/50000000000000),(-104837361/20000000000000)⟩
def e293 : ℝ := (219933513/20000000000000)
theorem h293 : Model (fun x => f293 ((77/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1425355284197357/10000000000000),(14079116120803/50000000000000),(9300930519/50000000000000),(-104837361/20000000000000)⟩
def e294 : ℝ := (549833783/50000000000000)
theorem h294 : Model (fun x => f294 ((77/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(3868875794410551/25000000000000),(64867769236909/100000000000000),(42759033823/50000000000000),(-117031143/10000000000000)⟩
def e295 : ℝ := (253821503/10000000000000)
theorem h295 : Model (fun x => f295 ((77/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(17811217463356489/100000000000000),(64867769236909/100000000000000),(42759033823/50000000000000),(-117031143/10000000000000)⟩
def e296 : ℝ := (2538215031/100000000000000)
theorem h296 : Model (fun x => f296 ((77/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(1208635293897383/6250000000000),(5664225608451/5000000000000),(245891399609/100000000000000),(-1877107869/100000000000000)⟩
def e297 : ℝ := (4443795481/100000000000000)
theorem h297 : Model (fun x => f297 ((77/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(493513641368477/2500000000000),(5664225608451/5000000000000),(245891399609/100000000000000),(-1877107869/100000000000000)⟩
def e298 : ℝ := (2221897741/50000000000000)
theorem h298 : Model (fun x => f298 ((77/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(857315731439787/4000000000000),(42623541449237/25000000000000),(107236057059/20000000000000),(-470732233/20000000000000)⟩
def e299 : ℝ := (3353346533/50000000000000)
theorem h299 : Model (fun x => f299 ((77/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(21415274238375627/100000000000000),(42623541449237/25000000000000),(107236057059/20000000000000),(-470732233/20000000000000)⟩
def e300 : ℝ := (6706693067/100000000000000)
theorem h300 : Model (fun x => f300 ((77/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(23251195558073463/100000000000000),(118318974398033/50000000000000),(247180599657/25000000000000),(-564422289/25000000000000)⟩
def e301 : ℝ := (9335234447/100000000000000)
theorem h301 : Model (fun x => f301 ((77/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(5813632222851699/25000000000000),(118318974398033/50000000000000),(247180599657/25000000000000),(-564422289/25000000000000)⟩
def e302 : ℝ := (583452153/6250000000000)
theorem h302 : Model (fun x => f302 ((77/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(1993599750161377/100000000000000),(38119849026301/50000000000000),(26006945429/4000000000000),(137381763/12500000000000)⟩
def e303 : ℝ := (38021877/1250000000000)
theorem h303 : Model (fun x => f303 ((77/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(58940430232523/50000000000000),(65309481663/12500000000000),(6773893/1250000000000),(-4924777/50000000000000)⟩
def e304 : ℝ := (20426987/100000000000000)
theorem h304 : Model (fun x => f304 ((77/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(104286476323539/50000000000000),(30076312779/12500000000000),(-17049687/100000000000000),(-4498131/100000000000000)⟩
def e305 : ℝ := (9376283/100000000000000)
theorem h305 : Model (fun x => f305 ((77/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(217513382879601/50000000000000),(125462107221/12500000000000),(253906033/50000000000000),(-2355727/12500000000000)⟩
def e306 : ℝ := (39179553/100000000000000)
theorem h306 : Model (fun x => f306 ((77/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(181469634029811/20000000000000),(3140160257809/100000000000000),(13281203/390625000000),(-57824627/100000000000000)⟩
def e307 : ℝ := (61393167/50000000000000)
theorem h307 : Model (fun x => f307 ((77/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1892482869269117/100000000000000),(34930799827/400000000000),(7246155319/50000000000000),(-153774901/100000000000000)⟩
def e308 : ℝ := (1336117/390625000000)
theorem h308 : Model (fun x => f308 ((77/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1115437545224013/50000000000000),(20181947870693/100000000000000),(14593098053/20000000000000),(-9785199/4000000000000)⟩
def e309 : ℝ := (12421049/1562500000000)
theorem h309 : Model (fun x => f309 ((77/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(54286476323539/6250000000000),(30076312779/1562500000000),(-17049687/12500000000000),(-4498131/12500000000000)⟩
def e310 : ℝ := (9376283/12500000000000)
theorem h310 : Model (fun x => f310 ((77/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(98646448164167/10000000000000),(61183996779/2500000000000),(50689243/12500000000000),(-22917301/50000000000000)⟩
def e311 : ℝ := (95437251/100000000000000)
theorem h311 : Model (fun x => f311 ((77/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(108646448164167/10000000000000),(61183996779/2500000000000),(50689243/12500000000000),(-22917301/50000000000000)⟩
def e312 : ℝ := (95437251/100000000000000)
theorem h312 : Model (fun x => f312 ((77/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(12118832743754641/50000000000000),(136933618528923/50000000000000),(259143107711/20000000000000),(-226595221/12500000000000)⟩
def e313 : ℝ := (5409835313/50000000000000)
theorem h313 : Model (fun x => f313 ((77/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(412580989087/100000000000000),(-4661852257/100000000000000),(15309663/50000000000000),(-65901/100000000000000)⟩
def e314 : ℝ := (189673/100000000000000)
theorem h314 : Model (fun x => f314 ((77/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (23962489902480487/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(8225213567651/100000000000000),(221611825353/100000000000000),(-261262461/100000000000000),(-3745367/100000000000000)⟩
def e315 : ℝ := (16717281/100000000000000)
theorem h315 : Model (fun x => f315 ((77/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(17188096408097/100000000000000),(242391974543/50000000000000),(66386949/100000000000000),(-8106791/100000000000000)⟩
def e316 : ℝ := (22977527/100000000000000)
theorem h316 : Model (fun x => f316 ((77/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(78657440442331/100000000000000),(396993704247/20000000000000),(-6957282263/100000000000000),(-64945177/100000000000000)⟩
def e317 : ℝ := (106288991/100000000000000)
theorem h317 : Model (fun x => f317 ((77/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(40861008021989/100000000000000),(500490036719/100000000000000),(-2528510803/25000000000000),(19522691/20000000000000)⟩
def e318 : ℝ := (11916291/20000000000000)
theorem h318 : Model (fun x => f318 ((77/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-98431400604159/100000000000000),(-119756006323/12500000000000),(19797198809/100000000000000),(-668711/195312500000)⟩
def e319 : ℝ := (407657/390625000000)
theorem h319 : Model (fun x => f319 ((77/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((77/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-65219/1600),(-847/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((77/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((77/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(7469/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((77/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(233541/1600),(1093/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((77/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((77/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(406341/1600),(1093/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((77/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2031705/32),(5465/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((77/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((77/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(126674967384751569/12500000000000),(30738023100223/781250000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (26269/20000000000000)
theorem h329 : Model (fun x => f329 ((77/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9867774397/100000000000000),(-19155537/50000000000000),(297109/50000000000000),(-4037/100000000000000)⟩
def e330 : ℝ := (9/20000000000000)
theorem h330 : Model (fun x => f330 ((77/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (504709761252637793/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(626512705664277/100000000000000),(117257709211/12500000000000),(3840750797/50000000000000),(624873/5000000000000)⟩
def e331 : ℝ := (2639837/50000000000000)
theorem h331 : Model (fun x => f331 ((77/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((77/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(437/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((77/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((77/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((77/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(635806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((77/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((77/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((77/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(88148467485127/3125000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (21/2000000000000)
theorem h339 : Model (fun x => f339 ((77/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3734193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((77/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((77/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((77/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2104249040475677/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1049/100000000000000)
theorem h343 : Model (fun x => f343 ((77/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(95045784103/2000000000000),(-795400903/12500000000000),(8520189/100000000000000),(-11409/100000000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((77/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2101431498840147/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(134050243353627/100000000000000),(874684345513/100000000000000),(-1171182481/100000000000000),(1568167/100000000000000)⟩
def e345 : ℝ := (3153/100000000000000)
theorem h345 : Model (fun x => f345 ((77/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(234050243353627/100000000000000),(874684345513/100000000000000),(-1171182481/100000000000000),(1568167/100000000000000)⟩
def e346 : ℝ := (3153/100000000000000)
theorem h346 : Model (fun x => f346 ((77/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(117025121676813/100000000000000),(109335543189/25000000000000),(-585591241/100000000000000),(784083/100000000000000)⟩
def e347 : ℝ := (1579/100000000000000)
theorem h347 : Model (fun x => f347 ((77/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(17025121676813/100000000000000),(109335543189/25000000000000),(-585591241/100000000000000),(784083/100000000000000)⟩
def e348 : ℝ := (1579/100000000000000)
theorem h348 : Model (fun x => f348 ((77/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(431878425235857/100000000000000),(1614000875647/100000000000000),(-2161110533/100000000000000),(2893639/100000000000000)⟩
def e349 : ℝ := (583/10000000000000)
theorem h349 : Model (fun x => f349 ((77/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(1393796355475071/50000000000000),(1614000875647/100000000000000),(-2161110533/100000000000000),(2893639/100000000000000)⟩
def e350 : ℝ := (5831/100000000000000)
theorem h350 : Model (fun x => f350 ((77/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3262183761843373/100000000000000),(14080105018247/100000000000000),(-2948558621/25000000000000),(6340429/100000000000000)⟩
def e351 : ℝ := (44447/50000000000000)
theorem h351 : Model (fun x => f351 ((77/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(341782588568973/4000000000000),(14080105018247/100000000000000),(-2948558621/25000000000000),(6340429/100000000000000)⟩
def e352 : ℝ := (17779/20000000000000)
theorem h352 : Model (fun x => f352 ((77/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1999857450715009/20000000000000),(53846245003557/100000000000000),(-2260202591/100000000000000),(-59616649/100000000000000)⟩
def e353 : ℝ := (446887/100000000000000)
theorem h353 : Model (fun x => f353 ((77/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(1908541859077833/12500000000000),(53846245003557/100000000000000),(-2260202591/100000000000000),(-59616649/100000000000000)⟩
def e354 : ℝ := (55861/12500000000000)
theorem h354 : Model (fun x => f354 ((77/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(17867787462709943/100000000000000),(129788501209397/100000000000000),(143437301353/100000000000000),(-34406719/12500000000000)⟩
def e355 : ℝ := (470953/50000000000000)
theorem h355 : Model (fun x => f355 ((77/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(5050875437106057/25000000000000),(129788501209397/100000000000000),(143437301353/100000000000000),(-34406719/12500000000000)⟩
def e356 : ℝ := (941907/100000000000000)
theorem h356 : Model (fun x => f356 ((77/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(11821586252035247/50000000000000),(240243584982163/100000000000000),(617167591/100000000000),(-296422101/100000000000000)⟩
def e357 : ℝ := (2456307/100000000000000)
theorem h357 : Model (fun x => f357 ((77/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(12022776728225723/50000000000000),(240243584982163/100000000000000),(617167591/100000000000),(-296422101/100000000000000)⟩
def e358 : ℝ := (614077/25000000000000)
theorem h358 : Model (fun x => f358 ((77/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(14069669095137709/50000000000000),(96576673395941/25000000000000),(816059491947/50000000000000),(1133937533/100000000000000)⟩
def e359 : ℝ := (3151033/50000000000000)
theorem h359 : Model (fun x => f359 ((77/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(2812171914265637/10000000000000),(96576673395941/25000000000000),(816059491947/50000000000000),(1133937533/100000000000000)⟩
def e360 : ℝ := (6302067/100000000000000)
theorem h360 : Model (fun x => f360 ((77/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(3290947604430523/10000000000000),(287532007863453/50000000000000),(686958597983/20000000000000),(6423255861/100000000000000)⟩
def e361 : ℝ := (942833/10000000000000)
theorem h361 : Model (fun x => f361 ((77/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(32912809377638563/100000000000000),(287532007863453/50000000000000),(686958597983/20000000000000),(6423255861/100000000000000)⟩
def e362 : ℝ := (9428331/100000000000000)
theorem h362 : Model (fun x => f362 ((77/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(1400861460950121/25000000000000),(241846944044277/100000000000000),(581408123623/20000000000000),(6502952327/50000000000000)⟩
def e363 : ℝ := (14672777/100000000000000)
theorem h363 : Model (fun x => f363 ((77/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(17118598879341/12500000000000),(1023600419623/100000000000000),(135526009/25000000000000),(-3286927/100000000000000)⟩
def e364 : ℝ := (1751/12500000000000)
theorem h364 : Model (fun x => f364 ((77/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(217025121676813/100000000000000),(109335543189/25000000000000),(-585591241/100000000000000),(784083/100000000000000)⟩
def e365 : ℝ := (1579/100000000000000)
theorem h365 : Model (fun x => f365 ((77/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(235499517194177/50000000000000),(379656953027/20000000000000),(-314539223/50000000000000),(-1718761/100000000000000)⟩
def e366 : ℝ := (8583/50000000000000)
theorem h366 : Model (fun x => f366 ((77/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1022186227477939/100000000000000),(154490805799/2500000000000),(4178612483/100000000000000),(-2780907/20000000000000)⟩
def e367 : ℝ := (3491/6250000000000)
theorem h367 : Model (fun x => f367 ((77/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2218400903947621/100000000000000),(3576361165491/20000000000000),(15054471841/50000000000000),(-40074097/100000000000000)⟩
def e368 : ℝ := (21831/12500000000000)
theorem h368 : Model (fun x => f368 ((77/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(94939788070617/3125000000000),(9439295571521/20000000000000),(118149057343/50000000000000),(55467011/20000000000000)⟩
def e369 : ℝ := (1390179/100000000000000)
theorem h369 : Model (fun x => f369 ((77/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(117025121676813/12500000000000),(109335543189/3125000000000),(-585591241/12500000000000),(784083/12500000000000)⟩
def e370 : ℝ := (1579/12500000000000)
theorem h370 : Model (fun x => f370 ((77/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(67071860278077/6250000000000),(4522337801671/100000000000000),(-1035656473/25000000000000),(2985737/100000000000000)⟩
def e371 : ℝ := (333/1250000000000)
theorem h371 : Model (fun x => f371 ((77/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(73321860278077/6250000000000),(4522337801671/100000000000000),(-1035656473/25000000000000),(2985737/100000000000000)⟩
def e372 : ℝ := (333/1250000000000)
theorem h372 : Model (fun x => f372 ((77/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(8910287200952347/25000000000000),(69107730240663/10000000000000),(478065892729/10000000000000),(12075289873/100000000000000)⟩
def e373 : ℝ := (5340119/25000000000000)
theorem h373 : Model (fun x => f373 ((77/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(280574570001/100000000000000),(-2720152457/50000000000000),(16963117/25000000000000),(-136197/20000000000000)⟩
def e374 : ℝ := (789/12500000000000)
theorem h374 : Model (fun x => f374 ((77/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (34945278745825119/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(7860922040741/50000000000000),(373716483719/100000000000000),(-119871817/10000000000000),(2139941/50000000000000)⟩
def e375 : ℝ := (804181/100000000000000)
theorem h375 : Model (fun x => f375 ((77/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(134050243353627/50000000000000),(874684345513/50000000000000),(-1171182481/50000000000000),(1568167/50000000000000)⟩
def e376 : ℝ := (3153/50000000000000)
theorem h376 : Model (fun x => f376 ((77/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(10681467210537/25000000000000),(-39918403939/25000000000000),(202631493/25000000000000),(-2057171/50000000000000)⟩
def e377 : ℝ := (5297/25000000000000)
theorem h377 : Model (fun x => f377 ((77/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (233174386254313/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(114548262315701/100000000000000),(79836807877/25000000000000),(-405262987/25000000000000),(8228681/100000000000000)⟩
def e378 : ℝ := (77987/50000000000000)
theorem h378 : Model (fun x => f378 ((77/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(14548262315701/100000000000000),(79836807877/25000000000000),(-405262987/25000000000000),(8228681/100000000000000)⟩
def e379 : ℝ := (77987/50000000000000)
theorem h379 : Model (fun x => f379 ((77/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(84547526947303/20000000000000),(589271677187/50000000000000),(-2991226809/50000000000000),(30367751/100000000000000)⟩
def e380 : ℝ := (575621/100000000000000)
theorem h380 : Model (fun x => f380 ((77/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(6946129801127/250000000000),(589271677187/50000000000000),(-2991226809/50000000000000),(30367751/100000000000000)⟩
def e381 : ℝ := (287811/50000000000000)
theorem h381 : Model (fun x => f381 ((77/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1591334197076807/50000000000000),(10222910219813/100000000000000),(-4812930007/10000000000000),(56301519/25000000000000)⟩
def e382 : ℝ := (5288647/100000000000000)
theorem h382 : Model (fun x => f382 ((77/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4232524673267283/50000000000000),(10222910219813/100000000000000),(-4812930007/10000000000000),(56301519/25000000000000)⟩
def e383 : ℝ := (661081/12500000000000)
theorem h383 : Model (fun x => f383 ((77/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2424141732655487/25000000000000),(19371533374417/50000000000000),(-7985377173/5000000000000),(635113281/100000000000000)⟩
def e384 : ℝ := (10821279/50000000000000)
theorem h384 : Model (fun x => f384 ((77/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(14965614549669567/100000000000000),(19371533374417/50000000000000),(-7985377173/5000000000000),(635113281/100000000000000)⟩
def e385 : ℝ := (21642559/100000000000000)
theorem h385 : Model (fun x => f385 ((77/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1714285141151221/10000000000000),(92171785471129/100000000000000),(-60363538189/20000000000000),(820917051/100000000000000)⟩
def e386 : ℝ := (14023121/25000000000000)
theorem h386 : Model (fun x => f386 ((77/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3895713139445299/20000000000000),(92171785471129/100000000000000),(-60363538189/20000000000000),(820917051/100000000000000)⟩
def e387 : ℝ := (11218497/20000000000000)
theorem h387 : Model (fun x => f387 ((77/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(11156179265097579/50000000000000),(167785438894093/100000000000000),(-367136543883/100000000000000),(85176287/100000000000000)⟩
def e388 : ℝ := (55047839/50000000000000)
theorem h388 : Model (fun x => f388 ((77/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(2271473948257611/10000000000000),(167785438894093/100000000000000),(-367136543883/100000000000000),(85176287/100000000000000)⟩
def e389 : ℝ := (110095679/100000000000000)
theorem h389 : Model (fun x => f389 ((77/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(13009669683414693/50000000000000),(264734196353817/100000000000000),(-63237026057/25000000000000),(-962819053/50000000000000)⟩
def e390 : ℝ := (91109521/50000000000000)
theorem h390 : Model (fun x => f390 ((77/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(13000860159605169/50000000000000),(264734196353817/100000000000000),(-63237026057/25000000000000),(-962819053/50000000000000)⟩
def e391 : ℝ := (182219043/100000000000000)
theorem h391 : Model (fun x => f391 ((77/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(5956903759568797/20000000000000),(48285524457823/12500000000000),(134172275209/100000000000000),(-1033089597/20000000000000)⟩
def e392 : ℝ := (67507127/25000000000000)
theorem h392 : Model (fun x => f392 ((77/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(14893926065588659/50000000000000),(48285524457823/12500000000000),(134172275209/100000000000000),(-1033089597/20000000000000)⟩
def e393 : ℝ := (270028509/100000000000000)
theorem h393 : Model (fun x => f393 ((77/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(2166807433128403/50000000000000),(151324319175699/100000000000000),(770231061913/100000000000000),(-4133727627/100000000000000)⟩
def e394 : ℝ := (10042579/10000000000000)
theorem h394 : Model (fun x => f394 ((77/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(65606521997733/50000000000000),(731613408891/100000000000000),(-2693947133/100000000000000),(8498053/100000000000000)⟩
def e395 : ℝ := (109359/25000000000000)
theorem h395 : Model (fun x => f395 ((77/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(214548262315701/100000000000000),(79836807877/25000000000000),(-405262987/25000000000000),(8228681/100000000000000)⟩
def e396 : ℝ := (77987/50000000000000)
theorem h396 : Model (fun x => f396 ((77/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(115077392156717/25000000000000),(1370307871907/100000000000000),(-5936051029/100000000000000),(4991083/20000000000000)⟩
def e397 : ℝ := (93673/12500000000000)
theorem h397 : Model (fun x => f397 ((77/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(246896545190461/25000000000000),(137811174729/3125000000000),(-1582151131/10000000000000),(25124399/50000000000000)⟩
def e398 : ℝ := (2619881/100000000000000)
theorem h398 : Model (fun x => f398 ((77/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1059424494847267/50000000000000),(1576914563509/12500000000000),(-35870985131/100000000000000),(67059977/100000000000000)⟩
def e399 : ℝ := (3979273/50000000000000)
theorem h399 : Model (fun x => f399 ((77/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(22241650056363/800000000000),(1602736206133/5000000000000),(-2370547193/20000000000000),(-83558637/25000000000000)⟩
def e400 : ℝ := (894357/4000000000000)
theorem h400 : Model (fun x => f400 ((77/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(114548262315701/12500000000000),(79836807877/3125000000000),(-405262987/3125000000000),(8228681/12500000000000)⟩
def e401 : ℝ := (77987/6250000000000)
theorem h401 : Model (fun x => f401 ((77/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(523799571260537/50000000000000),(657278252191/20000000000000),(-15662362717/100000000000000),(74327501/100000000000000)⟩
def e402 : ℝ := (421307/25000000000000)
theorem h402 : Model (fun x => f402 ((77/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(573799571260537/50000000000000),(657278252191/20000000000000),(-15662362717/100000000000000),(74327501/100000000000000)⟩
def e403 : ℝ := (421307/25000000000000)
theorem h403 : Model (fun x => f403 ((77/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(3190562316616997/10000000000000),(91845638927441/20000000000000),(481975767731/100000000000000),(-7179269413/100000000000000)⟩
def e404 : ℝ := (79865949/25000000000000)
theorem h404 : Model (fun x => f404 ((77/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(78356093751/25000000000000),(-451122077/10000000000000),(15049203/25000000000000),(-9097/1250000000000)⟩
def e405 : ℝ := (5967/50000000000000)
theorem h405 : Model (fun x => f405 ((77/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (1257836219881273/4000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(2716521061929/20000000000000),(278788367667/100000000000000),(-1803784231/100000000000000),(5925583/50000000000000)⟩
def e406 : ℝ := (1313943/100000000000000)
theorem h406 : Model (fun x => f406 ((77/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(29304449391127/100000000000000),(326252425693/50000000000000),(-3002502401/100000000000000),(2016381/12500000000000)⟩
def e407 : ℝ := (529531/25000000000000)
theorem h407 : Model (fun x => f407 ((77/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(11474756172523/6250000000000),(545364950929/12500000000000),(-5219569677/50000000000000),(126682223/100000000000000)⟩
def e408 : ℝ := (7437617/50000000000000)
theorem h408 : Model (fun x => f408 ((77/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(9537459675863/10000000000000),(1027820617383/100000000000000),(-9385624621/50000000000000),(309591403/100000000000000)⟩
def e409 : ℝ := (17400299/100000000000000)
theorem h409 : Model (fun x => f409 ((77/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3056803845529/100000000000000),(69772566799/100000000000000),(1025949567/100000000000000),(-32788629/100000000000000)⟩
def e410 : ℝ := (121760491/100000000000000)
theorem h410 : Model (fun x => f410 ((77/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1004127391845703/25000000000000),(60744747314453/25000000000000),(598829/10240000),(7161/10240000)⟩
def e411 : ℝ := (208007813/50000000000000)
theorem h411 : Model (fun x => f411 ((77/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(38809/1600),(197/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((77/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(7645373/64000),(116427/64000),(591/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((77/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(479808028136097367/100000000000000),(36332736928760071/100000000000000),(73606201501171/6250000000000),(10649442312561/50000000000000)⟩
def e414 : ℝ := (236211971361/100000000000000)
theorem h414 : Model (fun x => f414 ((77/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(20841668779/100000000000000),(-1578203833/100000000000000),(4271923/6250000000000),(-1113597/50000000000000)⟩
def e415 : ℝ := (2293/2500000000000)
theorem h415 : Model (fun x => f415 ((77/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (442276056886722077/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5661296355213/100000000000000),(15729716707/100000000000000),(-154038149/12500000000000),(27312519/100000000000000)⟩
def e416 : ℝ := (24458567/50000000000000)
theorem h416 : Model (fun x => f416 ((77/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(651123127421/25000000000000),(42751141753/50000000000000),(-330169/160000000000),(-547611/10000000000000)⟩
def e417 : ℝ := (1365421/800000000000)
theorem h417 : Model (fun x => f417 ((77/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((77/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((976594892569/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (19/10) (39/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (19/10) (39/20) ≤ (3906891603151/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(77/40)-(1/40)) (by norm_num : ((77/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel18

