import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel7
open Hf4Quad.Dag

def p0 : Cubic := ⟨(11/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((11/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((11/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((11/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((11/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(12047619047619/5000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((11/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-12047619047619/5000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((11/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-149523809523809/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((11/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((11/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(121/64),(11/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((11/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(228875661375661/100000000000000),(8322751322751/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((11/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-228875661375661/100000000000000),(-8322751322751/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((11/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-37839947089947/10000000000000),(-12703703703703/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((11/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((11/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1331/512),(363/2560),(33/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((11/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(101307740162037/4000000000000),(138146918402777/100000000000000),(2511762152777/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/25000000000000)
theorem h14 : Model (fun x => f14 ((11/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-101307740162037/4000000000000),(-138146918402777/100000000000000),(-2511762152777/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/25000000000000)
theorem h15 : Model (fun x => f15 ((11/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-582218594990079/20000000000000),(-1885632776331/1250000000000),(-1293711764219/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (9/100000000000000)
theorem h16 : Model (fun x => f16 ((11/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((11/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(14641/4096),(1331/5120),(363/51200),(11/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((11/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(124822513640873/12500000000000),(72624007936507/100000000000000),(123790922619/6250000000000),(24007936507/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((11/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1912512865823411/100000000000000),(-78226614169973/100000000000000),(-303384383267/50000000000000),(4392567791/50000000000000)⟩
def e20 : ℝ := (27281749/25000000000000)
theorem h20 : Model (fun x => f20 ((11/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((11/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(491488647460937/100000000000000),(11170196533203/25000000000000),(1331/81920),(121/409600)⟩
def e22 : ℝ := (269531251/100000000000000)
theorem h22 : Model (fun x => f22 ((11/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(50030586277997/1562500000000),(58217409487123/20000000000000),(10584983543113/100000000000000),(96227123119/50000000000000)⟩
def e23 : ℝ := (1755946189/100000000000000)
theorem h23 : Model (fun x => f23 ((11/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(1289444655968397/100000000000000),(106430216632821/50000000000000),(9978214776579/100000000000000),(10061969091/5000000000000)⟩
def e24 : ℝ := (373014637/20000000000000)
theorem h24 : Model (fun x => f24 ((11/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((11/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(168949222564697/25000000000000),(73723297119139/100000000000000),(83776473999/2500000000000),(10154724121/12500000000000)⟩
def e26 : ℝ := (223173829/20000000000000)
theorem h26 : Model (fun x => f26 ((11/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(1517503704898569/100000000000000),(41386464679051/25000000000000),(300992470393/4000000000000),(11401229939/6250000000000)⟩
def e27 : ℝ := (2505687119/100000000000000)
theorem h27 : Model (fun x => f27 ((11/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(1403474180433483/50000000000000),(189203145990923/50000000000000),(4375756634101/25000000000000),(95914765211/25000000000000)⟩
def e28 : ℝ := (273172519/6250000000000)
theorem h28 : Model (fun x => f28 ((11/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((11/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(929220724105833/100000000000000),(23652891159057/20000000000000),(6450788497923/100000000000000),(19547843933/10000000000000)⟩
def e30 : ℝ := (3593161629/100000000000000)
theorem h30 : Model (fun x => f30 ((11/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(55126388195961/25000000000000),(28064343081579/100000000000000),(1530782349903/100000000000000),(724802249/1562500000000)⟩
def e31 : ℝ := (852662961/100000000000000)
theorem h31 : Model (fun x => f31 ((11/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(302745391365081/10000000000000),(16258825402537/4000000000000),(19033808886307/100000000000000),(21502320239/5000000000000)⟩
def e32 : ℝ := (1044684653/20000000000000)
theorem h32 : Model (fun x => f32 ((11/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((11/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(259545/64),(4719/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((11/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((11/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(24299/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((11/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(648329/64),(41267/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((11/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((11/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(794249/64),(41267/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((11/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-794249/64),(-41267/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((11/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((11/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(19/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((11/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(361/64),(19/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((11/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((11/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(37905/32),(399/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((11/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(42210790133/50000000000000),(-1777296427/100000000000000),(1122503/4000000000000),(-393861/100000000000000)⟩
def e46 : ℝ := (5341/100000000000000)
theorem h46 : Model (fun x => f46 ((11/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (92757/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-209536736577157/20000000000000),(70647534037/25000000000000),(-3040110263/100000000000000),(32694153/100000000000000)⟩
def e47 : ℝ := (26431607/20000000000000)
theorem h47 : Model (fun x => f47 ((11/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((11/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(27/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((11/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((11/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((11/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(56249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((11/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(106249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((11/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((11/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(106249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((11/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((11/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2231249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((11/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((11/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((11/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(17431640624997/12500000000000),(615234374999/6250000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (73/100000000000000)
theorem h60 : Model (fun x => f60 ((11/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(112890624999997/100000000000000),(177083333333/20000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((11/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((11/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(106249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((11/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1175390624999987/100000000000000),(202083333333/4000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((11/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1275390624999987/100000000000000),(202083333333/4000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((11/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1778572082519207/100000000000000),(33147888183539/25000000000000),(964721679681/100000000000000),(2012803819/100000000000000)⟩
def e66 : ℝ := (633951/100000000000000)
theorem h66 : Model (fun x => f66 ((11/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(206249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((11/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(85078124999999/20000000000000),(1718749999997/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((11/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(175473632812497/20000000000000),(531738281249/10000000000000),(10742187499/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (9/20000000000000)
theorem h69 : Model (fun x => f69 ((11/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(975289076682917/6250000000000),(1257889558149227/100000000000000),(7852809436569/50000000000000),(3333181447/4000000000000)⟩
def e70 : ℝ := (113067487/50000000000000)
theorem h70 : Model (fun x => f70 ((11/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((11/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2370703124999937/12500000000000),(3718749999993/2500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((11/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(592675781249889/50000000000000),(22080078124963/25000000000000),(63802083333/10000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (333/50000000000000)
theorem h73 : Model (fun x => f73 ((11/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(10399897241590281/100000000000000),(167584796905229/20000000000000),(5210726737947/50000000000000),(27080874967/50000000000000)⟩
def e74 : ℝ := (3493263/2500000000000)
theorem h74 : Model (fun x => f74 ((11/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(26004522468516953/100000000000000),(523953385668843/25000000000000),(3265884043629/12500000000000),(137491286109/100000000000000)⟩
def e75 : ℝ := (182932747/50000000000000)
theorem h75 : Model (fun x => f75 ((11/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((11/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(790234374999979/12500000000000),(1239583333331/2500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((11/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(390624999999/100000000000000),(52083333333/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((11/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(24414062499/100000000000000),(4882812499/100000000000000),(325520833/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((11/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(192928314201/12500000000000),(16039530433/5000000000000),(5755954313/25000000000000),(623462799/100000000000000)⟩
def e80 : ℝ := (1955231/50000000000000)
theorem h80 : Model (fun x => f80 ((11/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(795829296079/25000000000000),(668061574167/100000000000000),(24411625309/50000000000000),(690912297/50000000000000)⟩
def e81 : ℝ := (5339693/50000000000000)
theorem h81 : Model (fun x => f81 ((11/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(26007705785701269/100000000000000),(2096481604249539/100000000000000),(523517911993/2000000000000),(138873110703/100000000000000)⟩
def e82 : ℝ := (4706811/1250000000000)
theorem h82 : Model (fun x => f82 ((11/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(762939453/50000000000000),(406901041/100000000000000),(5086263/12500000000000),(1808449/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((11/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(95367431/100000000000000),(31789143/100000000000000),(529819/12500000000000),(28257/10000000000000)⟩
def e84 : ℝ := (9547/100000000000000)
theorem h84 : Model (fun x => f84 ((11/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(372529/6250000000000),(476837/20000000000000),(99341/25000000000000),(35321/100000000000000)⟩
def e85 : ℝ := (227/12500000000000)
theorem h85 : Model (fun x => f85 ((11/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(23283/6250000000000),(86923/50000000000000),(34769/100000000000000),(3863/100000000000000)⟩
def e86 : ℝ := (271/100000000000000)
theorem h86 : Model (fun x => f86 ((11/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(69849/6250000000000),(260769/50000000000000),(104307/100000000000000),(11589/100000000000000)⟩
def e87 : ℝ := (813/100000000000000)
theorem h87 : Model (fun x => f87 ((11/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-69849/6250000000000),(-260769/50000000000000),(-104307/100000000000000),(-11589/100000000000000)⟩
def e88 : ℝ := (813/100000000000000)
theorem h88 : Model (fun x => f88 ((11/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(5201541156916737/20000000000000),(2096481603728001/100000000000000),(26175895495343/100000000000000),(69436549557/50000000000000)⟩
def e89 : ℝ := (376545693/100000000000000)
theorem h89 : Model (fun x => f89 ((11/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2370703124999937/10000000000000),(3718749999993/2000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((11/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(904785919189433/50000000000000),(3655700683587/25000000000000),(8862304687/20000000000000),(29839409/50000000000000)⟩
def e91 : ℝ := (30263/100000000000000)
theorem h91 : Model (fun x => f91 ((11/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(85799152243133171/20000000000000),(6831305050837013/100000000000000),(22145808934607/50000000000000),(149852116551/100000000000000)⟩
def e92 : ℝ := (87499/31250000000)
theorem h92 : Model (fun x => f92 ((11/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(23310253629/100000000000000),(-74238241/20000000000000),(876041/25000000000000),(-1281/5000000000000)⟩
def e93 : ℝ := (199/100000000000000)
theorem h93 : Model (fun x => f93 ((11/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (422120014414846277/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(606246218147/10000000000000),(392156862619/100000000000000),(-153787007/20000000000000),(2010029/100000000000000)⟩
def e94 : ℝ := (282399/100000000000000)
theorem h94 : Model (fun x => f94 ((11/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(56249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((11/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(11764705882353/25000000000000),(-92272202999/50000000000000),(2826967/390625000000),(-1419027/50000000000000)⟩
def e96 : ℝ := (11177/100000000000000)
theorem h96 : Model (fun x => f96 ((11/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (10583333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(4235294117647/4000000000000),(184544405997/50000000000000),(-361851777/25000000000000),(709513/12500000000000)⟩
def e97 : ℝ := (36321/50000000000000)
theorem h97 : Model (fun x => f97 ((11/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(88941176470587/4000000000000),(3875432525937/50000000000000),(-7598887317/25000000000000),(14899773/12500000000000)⟩
def e98 : ℝ := (762741/50000000000000)
theorem h98 : Model (fun x => f98 ((11/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(235294117647/4000000000000),(184544405997/50000000000000),(-361851777/25000000000000),(709513/12500000000000)⟩
def e99 : ℝ := (36321/50000000000000)
theorem h99 : Model (fun x => f99 ((11/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(13079584775083/10000000000000),(2165682882141/25000000000000),(-2681960251/50000000000000),(-22787911/25000000000000)⟩
def e100 : ℝ := (3039557/100000000000000)
theorem h100 : Model (fun x => f100 ((11/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(22422145328719/20000000000000),(781599837163/100000000000000),(-851415947/50000000000000),(1335549/100000000000000)⟩
def e101 : ℝ := (43477/20000000000000)
theorem h101 : Model (fun x => f101 ((11/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(4235294117647/400000000000),(184544405997/5000000000000),(-361851777/2500000000000),(709513/1250000000000)⟩
def e102 : ℝ := (36321/5000000000000)
theorem h102 : Model (fun x => f102 ((11/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(234186851211069/20000000000000),(4472487957103/100000000000000),(-8088451487/50000000000000),(58096589/100000000000000)⟩
def e103 : ℝ := (188761/20000000000000)
theorem h103 : Model (fun x => f103 ((11/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(254186851211069/20000000000000),(4472487957103/100000000000000),(-8088451487/50000000000000),(58096589/100000000000000)⟩
def e104 : ℝ := (188761/20000000000000)
theorem h104 : Model (fun x => f104 ((11/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(415582308640823/25000000000000),(115947451045673/100000000000000),(298109003859/100000000000000),(-680937979/25000000000000)⟩
def e105 : ℝ := (41918883/100000000000000)
theorem h105 : Model (fun x => f105 ((11/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(8235294117647/4000000000000),(184544405997/50000000000000),(-361851777/25000000000000),(709513/12500000000000)⟩
def e106 : ℝ := (36321/50000000000000)
theorem h106 : Model (fun x => f106 ((11/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(84775086505189/20000000000000),(1519777461151/100000000000000),(-459764611/10000000000000),(12687757/100000000000000)⟩
def e107 : ℝ := (362669/100000000000000)
theorem h107 : Model (fun x => f107 ((11/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(436342357011999/50000000000000),(4693430394731/100000000000000),(-1998323311/20000000000000),(5607349/50000000000000)⟩
def e108 : ℝ := (628561/50000000000000)
theorem h108 : Model (fun x => f108 ((11/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(14506893126785979/100000000000000),(1089875947131539/100000000000000),(78773710541/1000000000000),(-21176827533/100000000000000)⟩
def e109 : ℝ := (6688453/1250000000000)
theorem h109 : Model (fun x => f109 ((11/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(470865051903099/2500000000000),(16413596580423/12500000000000),(-17879734887/6250000000000),(28046529/12500000000000)⟩
def e110 : ℝ := (913017/2500000000000)
theorem h110 : Model (fun x => f110 ((11/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(221583553836697/20000000000000),(19310113624043/25000000000000),(48801158501/25000000000000),(-937088079/50000000000000)⟩
def e111 : ℝ := (28502561/100000000000000)
theorem h111 : Model (fun x => f111 ((11/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(4834314507809977/50000000000000),(363032494379119/50000000000000),(5218049075129/100000000000000),(-3696793907/25000000000000)⟩
def e112 : ℝ := (90998447/25000000000000)
theorem h112 : Model (fun x => f112 ((11/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(24175522142405933/100000000000000),(1815940935889777/100000000000000),(13095420129229/100000000000000),(-35964003161/100000000000000)⟩
def e113 : ℝ := (224767507/25000000000000)
theorem h113 : Model (fun x => f113 ((11/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(156955017301033/2500000000000),(5471198860141/12500000000000),(-5959911629/6250000000000),(9348843/12500000000000)⟩
def e114 : ℝ := (304339/2500000000000)
theorem h114 : Model (fun x => f114 ((11/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(69204152249/20000000000000),(1736888527/4000000000000),(595991161/50000000000000),(-10016659/100000000000000)⟩
def e115 : ℝ := (72101/100000000000000)
theorem h115 : Model (fun x => f115 ((11/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(10177081213/50000000000000),(15325487/400000000000),(28171851/12500000000000),(1600701/50000000000000)⟩
def e116 : ℝ := (56767/100000000000000)
theorem h116 : Model (fun x => f116 ((11/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(79867197893/6250000000000),(7795316917/3125000000000),(7903524527/50000000000000),(59199551/20000000000000)⟩
def e117 : ℝ := (4783899/100000000000000)
theorem h117 : Model (fun x => f117 ((11/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(657729865001/25000000000000),(129572578671/25000000000000),(3344612103/10000000000000),(332105583/50000000000000)⟩
def e118 : ℝ := (10749319/100000000000000)
theorem h118 : Model (fun x => f118 ((11/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(24178153061865937/100000000000000),(1816459226204461/100000000000000),(13128866250259/100000000000000),(-7059958399/20000000000000)⟩
def e119 : ℝ := (909819347/100000000000000)
theorem h119 : Model (fun x => f119 ((11/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(149662959/12500000000000),(60099949/20000000000000),(13551949/50000000000000),(19317/2000000000000)⟩
def e120 : ℝ := (6187/50000000000000)
theorem h120 : Model (fun x => f120 ((11/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(70429627/100000000000000),(22095569/100000000000000),(167883/6250000000000),(15257/10000000000000)⟩
def e121 : ℝ := (3979/100000000000000)
theorem h121 : Model (fun x => f121 ((11/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(4142919/100000000000000),(1559687/100000000000000),(11927/5000000000000),(18573/100000000000000)⟩
def e122 : ℝ := (389/50000000000000)
theorem h122 : Model (fun x => f122 ((11/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(243701/100000000000000),(107037/100000000000000),(1233/6250000000000),(39/2000000000000)⟩
def e123 : ℝ := (29/25000000000000)
theorem h123 : Model (fun x => f123 ((11/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(731103/100000000000000),(321111/100000000000000),(3699/6250000000000),(117/2000000000000)⟩
def e124 : ℝ := (87/25000000000000)
theorem h124 : Model (fun x => f124 ((11/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-731103/100000000000000),(-321111/100000000000000),(-3699/6250000000000),(-117/2000000000000)⟩
def e125 : ℝ := (87/25000000000000)
theorem h125 : Model (fun x => f125 ((11/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(12089076530567417/50000000000000),(36329184517667/2000000000000),(525154647643/4000000000000),(-7059959569/20000000000000)⟩
def e126 : ℝ := (181963939/20000000000000)
theorem h126 : Model (fun x => f126 ((11/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(470865051903099/2000000000000),(16413596580423/10000000000000),(-17879734887/5000000000000),(28046529/10000000000000)⟩
def e127 : ℝ := (913017/2000000000000)
theorem h127 : Model (fun x => f127 ((11/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1796703822990571/100000000000000),(3220981643443/25000000000000),(-3969837339/25000000000000),(-2011713/6250000000000)⟩
def e128 : ℝ := (73667/2000000000000)
theorem h128 : Model (fun x => f128 ((11/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(211501259716737903/50000000000000),(5982332549944531/100000000000000),(686482773807/6250000000000),(-746747939/1000000000000)⟩
def e129 : ℝ := (173949693/10000000000000)
theorem h129 : Model (fun x => f129 ((11/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(23640521133/100000000000000),(-83584289/25000000000000),(2057263/50000000000000),(-5667/12500000000000)⟩
def e130 : ℝ := (587/100000000000000)
theorem h130 : Model (fun x => f130 ((11/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (417009126744859533/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2857920691993/50000000000000),(348583877849/100000000000000),(-246818667/12500000000000),(2307509/20000000000000)⟩
def e131 : ℝ := (271777/50000000000000)
theorem h131 : Model (fun x => f131 ((11/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(736143972841/6250000000000),(185185185117/25000000000000),(-2743484371/100000000000000),(6773787/50000000000000)⟩
def e132 : ℝ := (825953/100000000000000)
theorem h132 : Model (fun x => f132 ((11/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-61699682288019/50000000000000),(-772733554629/10000000000000),(7619556237/25000000000000),(-84178529/50000000000000)⟩
def e133 : ℝ := (25569487/100000000000000)
theorem h133 : Model (fun x => f133 ((11/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(9090909090909/12500000000000),(-1322314049587/100000000000000),(6010518407/25000000000000),(-109282153/25000000000000)⟩
def e134 : ℝ := (8094977/100000000000000)
theorem h134 : Model (fun x => f134 ((11/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (27/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-11218124052367/12500000000000),(-997038315603/25000000000000),(94677859279/100000000000000),(-11524107/625000000000)⟩
def e135 : ℝ := (73064163/100000000000000)
theorem h135 : Model (fun x => f135 ((11/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(73205/2048),(1331/512),(363/5120),(11/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((11/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((11/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(11979/256),(3267/1280),(297/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((11/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(169037/2048),(13189/2560),(3003/25600),(73/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((11/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-121/64),(-11/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((11/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(165165/2048),(13013/2560),(2987/25600),(73/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((11/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((11/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(33/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((11/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-33/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((11/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(148269/2048),(12629/2560),(2987/25600),(73/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((11/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(154413/2048),(12629/2560),(2987/25600),(73/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((11/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((11/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(154413/32),(12629/40),(2987/400),(73/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((11/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((11/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(13835745/4096),(251559/1024),(68607/10240),(2079/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((11/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(7401119347/25000000000000),(-2153052901/100000000000000),(2446651/2500000000000),(-1779383/50000000000000)⟩
def e151 : ℝ := (6741/5000000000000)
theorem h151 : Model (fun x => f151 ((11/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (800108253/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(71426815108019/50000000000000),(-52124065087/5000000000000),(2708441761/20000000000000),(-190531909/100000000000000)⟩
def e152 : ℝ := (635874479/50000000000000)
theorem h152 : Model (fun x => f152 ((11/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(35/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((11/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(945/64),(31/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((11/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(57/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((11/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(7017543859649/100000000000000),(-36934441367/50000000000000),(388783593/50000000000000),(-4092459/50000000000000)⟩
def e156 : ℝ := (21769/25000000000000)
theorem h156 : Model (fun x => f156 ((11/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (141/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(103618421052629/100000000000000),(268928901187/100000000000000),(1555134363/100000000000000),(-204623/1250000000000)⟩
def e157 : ℝ := (300953/12500000000000)
theorem h157 : Model (fun x => f157 ((11/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(203618421052629/100000000000000),(268928901187/100000000000000),(1555134363/100000000000000),(-204623/1250000000000)⟩
def e158 : ℝ := (300953/12500000000000)
theorem h158 : Model (fun x => f158 ((11/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(50904605263157/50000000000000),(134464450593/100000000000000),(777567181/100000000000000),(-204623/2500000000000)⟩
def e159 : ℝ := (601907/50000000000000)
theorem h159 : Model (fun x => f159 ((11/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(904605263157/50000000000000),(134464450593/100000000000000),(777567181/100000000000000),(-204623/2500000000000)⟩
def e160 : ℝ := (601907/50000000000000)
theorem h160 : Model (fun x => f160 ((11/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((11/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((11/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(375724467418539/100000000000000),(248118926689/50000000000000),(2869593167/100000000000000),(-30206253/100000000000000)⟩
def e163 : ℝ := (4442651/100000000000000)
theorem h163 : Model (fun x => f163 ((11/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(341429844141603/12500000000000),(248118926689/50000000000000),(2869593167/100000000000000),(-30206253/100000000000000)⟩
def e164 : ℝ := (1110663/25000000000000)
theorem h164 : Model (fun x => f164 ((11/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((11/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1390428115287161/50000000000000),(4178029953541/100000000000000),(4965508993/20000000000000),(-12330083/5000000000000)⟩
def e166 : ℝ := (9368971/25000000000000)
theorem h166 : Model (fun x => f166 ((11/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4031618591477637/50000000000000),(4178029953541/100000000000000),(4965508993/20000000000000),(-12330083/5000000000000)⟩
def e167 : ℝ := (7495177/20000000000000)
theorem h167 : Model (fun x => f167 ((11/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((11/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1641823623766193/20000000000000),(3773951722331/25000000000000),(18718355721/20000000000000),(-169032301/20000000000000)⟩
def e169 : ℝ := (67903023/50000000000000)
theorem h169 : Model (fun x => f169 ((11/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(1684770717234823/12500000000000),(3773951722331/25000000000000),(18718355721/20000000000000),(-169032301/20000000000000)⟩
def e170 : ℝ := (135806047/100000000000000)
theorem h170 : Model (fun x => f170 ((11/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((11/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(1372201413116233/10000000000000),(669845266521/2000000000000),(22038533809/10000000000000),(-1720401629/100000000000000)⟩
def e172 : ℝ := (151270119/50000000000000)
theorem h172 : Model (fun x => f172 ((11/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(3211545683375323/20000000000000),(669845266521/2000000000000),(22038533809/10000000000000),(-1720401629/100000000000000)⟩
def e173 : ℝ := (302540239/100000000000000)
theorem h173 : Model (fun x => f173 ((11/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((11/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(16348246529681661/100000000000000),(27845072586557/50000000000000),(394267386881/100000000000000),(-62726869/2500000000000)⟩
def e175 : ℝ := (505506619/100000000000000)
theorem h175 : Model (fun x => f175 ((11/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(16750627482062613/100000000000000),(27845072586557/50000000000000),(394267386881/100000000000000),(-62726869/2500000000000)⟩
def e176 : ℝ := (25275331/5000000000000)
theorem h176 : Model (fun x => f176 ((11/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((11/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(3410736319538347/20000000000000),(79221336356341/100000000000000),(606531343599/100000000000000),(-2962316897/100000000000000)⟩
def e178 : ℝ := (722575887/100000000000000)
theorem h178 : Model (fun x => f178 ((11/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(17036062550072687/100000000000000),(79221336356341/100000000000000),(606531343599/100000000000000),(-2962316897/100000000000000)⟩
def e179 : ℝ := (45160993/6250000000000)
theorem h179 : Model (fun x => f179 ((11/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((11/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(17344280786998039/100000000000000),(103562065023421/100000000000000),(21412403463/2500000000000),(-2978731387/100000000000000)⟩
def e181 : ℝ := (948493823/100000000000000)
theorem h181 : Model (fun x => f181 ((11/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(4336903530082843/25000000000000),(103562065023421/100000000000000),(21412403463/2500000000000),(-2978731387/100000000000000)⟩
def e182 : ℝ := (1852527/195312500000)
theorem h182 : Model (fun x => f182 ((11/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(39231857591171/12500000000000),(25200029799569/100000000000000),(144819667069/50000000000000),(483167597/100000000000000)⟩
def e183 : ℝ := (46889727/20000000000000)
theorem h183 : Model (fun x => f183 ((11/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(103651153479913/100000000000000),(136897195587/50000000000000),(1764076901/100000000000000),(-7287451/50000000000000)⟩
def e184 : ℝ := (1235269/50000000000000)
theorem h184 : Model (fun x => f184 ((11/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(100904605263157/50000000000000),(134464450593/100000000000000),(777567181/100000000000000),(-204623/2500000000000)⟩
def e185 : ℝ := (601907/50000000000000)
theorem h185 : Model (fun x => f185 ((11/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(407269574532541/100000000000000),(13568082309/2500000000000),(3319211263/100000000000000),(-15472371/50000000000000)⟩
def e186 : ℝ := (2439083/50000000000000)
theorem h186 : Model (fun x => f186 ((11/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(410953756538999/50000000000000),(1642898387481/100000000000000),(1324379811/12500000000000),(-87100831/100000000000000)⟩
def e187 : ℝ := (3705317/25000000000000)
theorem h187 : Model (fun x => f187 ((11/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(6479238528903/390625000000),(4420693687367/100000000000000),(29981760897/100000000000000),(-216028773/100000000000000)⟩
def e188 : ℝ := (8003127/20000000000000)
theorem h188 : Model (fun x => f188 ((11/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1719246200812263/100000000000000),(9123486669597/100000000000000),(36220266217/50000000000000),(-152797611/50000000000000)⟩
def e189 : ℝ := (41695223/50000000000000)
theorem h189 : Model (fun x => f189 ((11/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((11/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(50904605263157/6250000000000),(134464450593/12500000000000),(777567181/12500000000000),(-204623/312500000000)⟩
def e191 : ℝ := (601907/6250000000000)
theorem h191 : Model (fun x => f191 ((11/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(36724993507617/4000000000000),(674754997959/50000000000000),(7984614349/100000000000000),(-40027131/50000000000000)⟩
def e192 : ℝ := (242021/2000000000000)
theorem h192 : Model (fun x => f192 ((11/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(40724993507617/4000000000000),(674754997959/50000000000000),(7984614349/100000000000000),(-40027131/50000000000000)⟩
def e193 : ℝ := (242021/2000000000000)
theorem h193 : Model (fun x => f193 ((11/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(350081451830373/2000000000000),(116089883180943/100000000000000),(249483149173/25000000000000),(-43462551/1562500000000)⟩
def e194 : ℝ := (213007389/20000000000000)
theorem h194 : Model (fun x => f194 ((11/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(142823904947/25000000000000),(-473615793/12500000000000),(-1860403/25000000000000),(356151/100000000000000)⟩
def e195 : ℝ := (37809/100000000000000)
theorem h195 : Model (fun x => f195 ((11/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (8693490464550403/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(896519535919/50000000000000),(13207493693/10000000000000),(845663/125000000000),(-8971397/100000000000000)⟩
def e196 : ℝ := (23867/1562500000000)
theorem h196 : Model (fun x => f196 ((11/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(103618421052629/50000000000000),(268928901187/50000000000000),(1555134363/50000000000000),(-204623/625000000000)⟩
def e197 : ℝ := (300953/6250000000000)
theorem h197 : Model (fun x => f197 ((11/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(24555735056543/50000000000000),(-64863943179/100000000000000),(-289419521/100000000000000),(96519/2000000000000)⟩
def e198 : ℝ := (591701/100000000000000)
theorem h198 : Model (fun x => f198 ((11/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (40669583647923/20000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(101777059773827/100000000000000),(64863943177/50000000000000),(226109/39062500000),(-9651901/100000000000000)⟩
def e199 : ℝ := (3635841/100000000000000)
theorem h199 : Model (fun x => f199 ((11/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1777059773827/100000000000000),(64863943177/50000000000000),(226109/39062500000),(-9651901/100000000000000)⟩
def e200 : ℝ := (3635841/100000000000000)
theorem h200 : Model (fun x => f200 ((11/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(18780290791599/5000000000000),(47875767583/10000000000000),(427238339/20000000000000),(-35620111/100000000000000)⟩
def e201 : ℝ := (6708993/50000000000000)
theorem h201 : Model (fun x => f201 ((11/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(546264020309253/20000000000000),(47875767583/10000000000000),(427238339/20000000000000),(-35620111/100000000000000)⟩
def e202 : ℝ := (13417987/100000000000000)
theorem h202 : Model (fun x => f202 ((11/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1389928646182647/50000000000000),(4030549323199/100000000000000),(18605182367/100000000000000),(-147167471/50000000000000)⟩
def e203 : ℝ := (28269583/25000000000000)
theorem h203 : Model (fun x => f203 ((11/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4031119122373123/50000000000000),(4030549323199/100000000000000),(18605182367/100000000000000),(-147167471/50000000000000)⟩
def e204 : ℝ := (113078333/100000000000000)
theorem h204 : Model (fun x => f204 ((11/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8205509037463727/100000000000000),(7280572930809/50000000000000),(35415968241/50000000000000),(-1030258201/100000000000000)⟩
def e205 : ℝ := (409179257/100000000000000)
theorem h205 : Model (fun x => f205 ((11/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6737278328255673/50000000000000),(7280572930809/50000000000000),(35415968241/50000000000000),(-1030258201/100000000000000)⟩
def e206 : ℝ := (204589629/50000000000000)
theorem h206 : Model (fun x => f206 ((11/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13714007582555737/100000000000000),(32300163673397/100000000000000),(84488261741/50000000000000),(-2172943003/100000000000000)⟩
def e207 : ℝ := (909774207/100000000000000)
theorem h207 : Model (fun x => f207 ((11/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8024860934135011/50000000000000),(32300163673397/100000000000000),(84488261741/50000000000000),(-2172943003/100000000000000)⟩
def e208 : ℝ := (7107611/781250000000)
theorem h208 : Model (fun x => f208 ((11/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(16334935019402163/100000000000000),(53695121834319/100000000000000),(61356742583/20000000000000),(-670897027/20000000000000)⟩
def e209 : ℝ := (1516837521/100000000000000)
theorem h209 : Model (fun x => f209 ((11/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(3347463194356623/20000000000000),(53695121834319/100000000000000),(61356742583/20000000000000),(-670897027/20000000000000)⟩
def e210 : ℝ := (758418761/50000000000000)
theorem h210 : Model (fun x => f210 ((11/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(8517374040567997/50000000000000),(9545285310941/12500000000000),(478775108593/100000000000000),(-864154631/20000000000000)⟩
def e211 : ℝ := (2164082989/100000000000000)
theorem h211 : Model (fun x => f211 ((11/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(8508564516758473/50000000000000),(9545285310941/12500000000000),(478775108593/100000000000000),(-864154631/20000000000000)⟩
def e212 : ℝ := (216408299/10000000000000)
theorem h212 : Model (fun x => f212 ((11/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(1731953358823181/10000000000000),(12474405963163/12500000000000),(68484818983/10000000000000),(-4976912793/100000000000000)⟩
def e213 : ℝ := (1418572983/50000000000000)
theorem h213 : Model (fun x => f213 ((11/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(17322866921565143/100000000000000),(12474405963163/12500000000000),(68484818983/10000000000000),(-4976912793/100000000000000)⟩
def e214 : ℝ := (2837145967/100000000000000)
theorem h214 : Model (fun x => f214 ((11/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(307837699736717/100000000000000),(3030751289553/12500000000000),(60475985953/25000000000000),(-147167873/50000000000000)⟩
def e215 : ℝ := (69982033/10000000000000)
theorem h215 : Model (fun x => f215 ((11/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(103585698962051/100000000000000),(422506331/160000000000),(336635989/25000000000000),(-18145011/100000000000000)⟩
def e216 : ℝ := (7432187/100000000000000)
theorem h216 : Model (fun x => f216 ((11/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(201777059773827/100000000000000),(64863943177/50000000000000),(226109/39062500000),(-9651901/100000000000000)⟩
def e217 : ℝ := (3635841/100000000000000)
theorem h217 : Model (fun x => f217 ((11/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(81427963701941/20000000000000),(523522229583/100000000000000),(626055509/25000000000000),(-37448813/100000000000000)⟩
def e218 : ℝ := (14703869/100000000000000)
theorem h218 : Model (fun x => f218 ((11/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(410757377478689/50000000000000),(1584521643173/100000000000000),(4044392067/50000000000000),(-108580821/100000000000000)⟩
def e219 : ℝ := (278721/625000000000)
theorem h219 : Model (fun x => f219 ((11/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1657628318161157/100000000000000),(2131467455383/50000000000000),(11566062677/50000000000000),(-278717741/100000000000000)⟩
def e220 : ℝ := (120216599/100000000000000)
theorem h220 : Model (fun x => f220 ((11/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(13736527036481/800000000000),(8793031291539/100000000000000),(57539248841/100000000000000),(-94200417/20000000000000)⟩
def e221 : ℝ := (12478447/5000000000000)
theorem h221 : Model (fun x => f221 ((11/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(101777059773827/12500000000000),(64863943177/6250000000000),(226109/4882812500),(-9651901/12500000000000)⟩
def e222 : ℝ := (3635841/12500000000000)
theorem h222 : Model (fun x => f222 ((11/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(917802177152667/100000000000000),(1301889547707/100000000000000),(1494314069/25000000000000),(-95360219/100000000000000)⟩
def e223 : ℝ := (7303783/20000000000000)
theorem h223 : Model (fun x => f223 ((11/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1017802177152667/100000000000000),(1301889547707/100000000000000),(1494314069/25000000000000),(-95360219/100000000000000)⟩
def e224 : ℝ := (7303783/20000000000000)
theorem h224 : Model (fun x => f224 ((11/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(17476333905308543/100000000000000),(22369993027247/20000000000000),(802744710781/100000000000000),(-2578293889/50000000000000)⟩
def e225 : ℝ := (3184829783/100000000000000)
theorem h225 : Model (fun x => f225 ((11/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(572202388337/100000000000000),(-732428409/20000000000000),(-177819/6250000000000),(355257/100000000000000)⟩
def e226 : ℝ := (108889/100000000000000)
theorem h226 : Model (fun x => f226 ((11/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (8681836427021983/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(352290934019/20000000000000),(63731398137/50000000000000),(487498503/100000000000000),(-1267409/12500000000000)⟩
def e227 : ℝ := (448281/10000000000000)
theorem h227 : Model (fun x => f227 ((11/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(3554493741933/100000000000000),(64884433301/25000000000000),(1164028903/100000000000000),(-19110669/100000000000000)⟩
def e228 : ℝ := (3005149/50000000000000)
theorem h228 : Model (fun x => f228 ((11/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(5077723346153/100000000000000),(333704141031/100000000000000),(-561417831/100000000000000),(-2765093/25000000000000)⟩
def e229 : ℝ := (2292477/4000000000000)
theorem h229 : Model (fun x => f229 ((11/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3692889706293/100000000000000),(21943808943/12500000000000),(-3600130633/100000000000000),(57413013/100000000000000)⟩
def e230 : ℝ := (44339073/100000000000000)
theorem h230 : Model (fun x => f230 ((11/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-86052102712643/100000000000000),(-953150697717/25000000000000),(45538864323/50000000000000),(-1786444107/100000000000000)⟩
def e231 : ℝ := (29350809/25000000000000)
theorem h231 : Model (fun x => f231 ((11/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((11/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-605/64),(-11/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((11/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(231/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((11/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1243/64),(29/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((11/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((11/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2907/64),(29/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((11/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((11/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(363375/32),(725/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((11/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(407/64),(13/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((11/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(791/64),(13/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((11/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((11/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(149499/64),(2457/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((11/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(428096509/1000000000000),(-56285761/20000000000000),(4014937/100000000000000),(-20313/50000000000000)⟩
def e244 : ℝ := (239/50000000000000)
theorem h244 : Model (fun x => f244 ((11/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (928179/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(486123652993359/100000000000000),(-627971847061/50000000000000),(-75723857/12500000000000),(-59534187/100000000000000)⟩
def e245 : ℝ := (1307403/12500000000000)
theorem h245 : Model (fun x => f245 ((11/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(99/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((11/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(1705/64),(83/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((11/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(3049/64),(83/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((11/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(729/64),(27/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((11/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2222721/4096),(14283/1024),(6371/51200),(11/25600)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((11/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((11/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(16245/32),(171/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((11/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(24622960911/12500000000000),(-1036756249/25000000000000),(32739671/50000000000000),(-919009/100000000000000)⟩
def e253 : ℝ := (623/5000000000000)
theorem h253 : Model (fun x => f253 ((11/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (39753/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(106894477146599/100000000000000),(124291532959/25000000000000),(440093857/20000000000000),(-8386139/50000000000000)⟩
def e254 : ℝ := (13554717/100000000000000)
theorem h254 : Model (fun x => f254 ((11/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(206894477146599/100000000000000),(124291532959/25000000000000),(440093857/20000000000000),(-8386139/50000000000000)⟩
def e255 : ℝ := (13554717/100000000000000)
theorem h255 : Model (fun x => f255 ((11/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(103447238573299/100000000000000),(124291532959/50000000000000),(550117321/50000000000000),(-8386139/100000000000000)⟩
def e256 : ℝ := (84717/1250000000000)
theorem h256 : Model (fun x => f256 ((11/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(3447238573299/100000000000000),(124291532959/50000000000000),(550117321/50000000000000),(-8386139/100000000000000)⟩
def e257 : ℝ := (84717/1250000000000)
theorem h257 : Model (fun x => f257 ((11/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(38176957092527/10000000000000),(7339119089/800000000000),(16241559/400000000000),(-30948847/100000000000000)⟩
def e258 : ℝ := (3126461/12500000000000)
theorem h258 : Model (fun x => f258 ((11/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(547496771327911/20000000000000),(7339119089/800000000000),(16241559/400000000000),(-30948847/100000000000000)⟩
def e259 : ℝ := (25011689/100000000000000)
theorem h259 : Model (fun x => f259 ((11/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1415925728041733/50000000000000),(7753935803991/100000000000000),(18299791343/50000000000000),(-241398047/100000000000000)⟩
def e260 : ℝ := (3306841/1562500000000)
theorem h260 : Model (fun x => f260 ((11/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4057116204232209/50000000000000),(7753935803991/100000000000000),(18299791343/50000000000000),(-241398047/100000000000000)⟩
def e261 : ℝ := (8465513/4000000000000)
theorem h261 : Model (fun x => f261 ((11/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8393949357976131/100000000000000),(28191840166647/100000000000000),(146411824859/100000000000000),(-75389857/10000000000000)⟩
def e262 : ℝ := (77077409/10000000000000)
theorem h262 : Model (fun x => f262 ((11/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(10930397581619/80000000000),(28191840166647/100000000000000),(146411824859/100000000000000),(-75389857/10000000000000)⟩
def e263 : ℝ := (770774091/100000000000000)
theorem h263 : Model (fun x => f263 ((11/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(14133993079084389/100000000000000),(63127576937163/100000000000000),(185932078131/50000000000000),(-78222111/6250000000000)⟩
def e264 : ℝ := (1729828289/100000000000000)
theorem h264 : Model (fun x => f264 ((11/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(8234853682399337/50000000000000),(63127576937163/100000000000000),(185932078131/50000000000000),(-78222111/6250000000000)⟩
def e265 : ℝ := (172982829/10000000000000)
theorem h265 : Model (fun x => f265 ((11/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(425936436749687/2500000000000),(106244638634869/100000000000000),(14456261859/2000000000000),(-1056927583/100000000000000)⟩
def e266 : ℝ := (2918652783/100000000000000)
theorem h266 : Model (fun x => f266 ((11/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(1089989901398027/6250000000000),(106244638634869/100000000000000),(14456261859/2000000000000),(-1056927583/100000000000000)⟩
def e267 : ℝ := (182415799/6250000000000)
theorem h267 : Model (fun x => f267 ((11/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(2255128907448167/12500000000000),(153259629841421/100000000000000),(601857754313/50000000000000),(409839777/100000000000000)⟩
def e268 : ℝ := (168776827/4000000000000)
theorem h268 : Model (fun x => f268 ((11/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(1126463263247893/6250000000000),(153259629841421/100000000000000),(601857754313/50000000000000),(409839777/100000000000000)⟩
def e269 : ℝ := (1054855169/25000000000000)
theorem h269 : Model (fun x => f269 ((11/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(1165295139372617/6250000000000),(101673002789077/50000000000000),(1824487765453/100000000000000),(3590947987/100000000000000)⟩
def e270 : ℝ := (560889649/10000000000000)
theorem h270 : Model (fun x => f270 ((11/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(3729611112659041/20000000000000),(101673002789077/50000000000000),(1824487765453/100000000000000),(3590947987/100000000000000)⟩
def e271 : ℝ := (5608896491/100000000000000)
theorem h271 : Model (fun x => f271 ((11/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(321421482274071/50000000000000),(13341432548721/25000000000000),(77355054847/10000000000000),(333286719/6250000000000)⟩
def e272 : ℝ := (187146209/12500000000000)
theorem h272 : Model (fun x => f272 ((11/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(10701331168441/10000000000000),(257152317253/50000000000000),(723565029/25000000000000),(-2376093/20000000000000)⟩
def e273 : ℝ := (3521401/25000000000000)
theorem h273 : Model (fun x => f273 ((11/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(203447238573299/100000000000000),(124291532959/50000000000000),(550117321/50000000000000),(-8386139/100000000000000)⟩
def e274 : ℝ := (84717/1250000000000)
theorem h274 : Model (fun x => f274 ((11/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(12934618400969/3125000000000),(505735383171/50000000000000),(25473647/500000000000),(-28652743/100000000000000)⟩
def e275 : ℝ := (6910081/25000000000000)
theorem h275 : Model (fun x => f275 ((11/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(842083966616487/100000000000000),(385839251831/12500000000000),(17433388197/100000000000000),(-69210911/100000000000000)⟩
def e276 : ℝ := (16904831/20000000000000)
theorem h276 : Model (fun x => f276 ((11/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1713196576549743/100000000000000),(334924502691/4000000000000),(2096227789/4000000000000),(-16766059/12500000000000)⟩
def e277 : ℝ := (14355993/6250000000000)
theorem h277 : Model (fun x => f277 ((11/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(916674196114909/50000000000000),(17771394440697/100000000000000),(74364370323/50000000000000),(82396767/50000000000000)⟩
def e278 : ℝ := (489672073/100000000000000)
theorem h278 : Model (fun x => f278 ((11/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(103447238573299/12500000000000),(124291532959/6250000000000),(550117321/6250000000000),(-8386139/12500000000000)⟩
def e279 : ℝ := (84717/156250000000)
theorem h279 : Model (fun x => f279 ((11/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(467295610135401/50000000000000),(50059383237/2000000000000),(2924034313/25000000000000),(-78969577/100000000000000)⟩
def e280 : ℝ := (17076121/25000000000000)
theorem h280 : Model (fun x => f280 ((11/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(517295610135401/50000000000000),(50059383237/2000000000000),(2924034313/25000000000000),(-78969577/100000000000000)⟩
def e281 : ℝ := (17076121/25000000000000)
theorem h281 : Model (fun x => f281 ((11/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(18967661502985603/100000000000000),(229749431489929/100000000000000),(1098988979743/50000000000000),(3029176581/50000000000000)⟩
def e282 : ℝ := (6350502693/100000000000000)
theorem h282 : Model (fun x => f282 ((11/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(105442623999/20000000000000),(-99780779/1562500000000),(16257677/100000000000000),(374689/100000000000000)⟩
def e283 : ℝ := (92679/50000000000000)
theorem h283 : Model (fun x => f283 ((11/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (18735701684680333/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1694576225031/50000000000000),(240299373231/100000000000000),(77485187/10000000000000),(-5099957/50000000000000)⟩
def e284 : ℝ := (1859933/20000000000000)
theorem h284 : Model (fun x => f284 ((11/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(106894477146599/50000000000000),(124291532959/12500000000000),(440093857/10000000000000),(-8386139/25000000000000)⟩
def e285 : ℝ := (13554717/50000000000000)
theorem h285 : Model (fun x => f285 ((11/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(12083454495639/25000000000000),(-14518232709/12500000000000),(-234966607/100000000000000),(1143637/20000000000000)⟩
def e286 : ℝ := (3202693/100000000000000)
theorem h286 : Model (fun x => f286 ((11/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (206395080218483/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(25833091008721/25000000000000),(232291723341/100000000000000),(46993321/10000000000000),(-5718187/50000000000000)⟩
def e287 : ℝ := (20099381/100000000000000)
theorem h287 : Model (fun x => f287 ((11/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(833091008721/25000000000000),(232291723341/100000000000000),(46993321/10000000000000),(-5718187/50000000000000)⟩
def e288 : ℝ := (20099381/100000000000000)
theorem h288 : Model (fun x => f288 ((11/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(381345629176357/100000000000000),(428633537117/50000000000000),(867138661/50000000000000),(-21102833/50000000000000)⟩
def e289 : ℝ := (74176289/100000000000000)
theorem h289 : Model (fun x => f289 ((11/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1368529957445321/50000000000000),(428633537117/50000000000000),(867138661/50000000000000),(-21102833/50000000000000)⟩
def e290 : ℝ := (7417629/10000000000000)
theorem h290 : Model (fun x => f290 ((11/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(707067178776921/25000000000000),(7243797979073/100000000000000),(16645783733/100000000000000),(-87143839/25000000000000)⟩
def e291 : ℝ := (627313889/100000000000000)
theorem h291 : Model (fun x => f291 ((11/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(2027662416872159/25000000000000),(7243797979073/100000000000000),(16645783733/100000000000000),(-87143839/25000000000000)⟩
def e292 : ℝ := (62731389/10000000000000)
theorem h292 : Model (fun x => f292 ((11/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4190463020001733/50000000000000),(26325555584447/100000000000000),(36070930669/50000000000000),(-303761899/25000000000000)⟩
def e293 : ℝ := (2282891869/100000000000000)
theorem h293 : Model (fun x => f293 ((11/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(2729994731810217/20000000000000),(26325555584447/100000000000000),(36070930669/50000000000000),(-303761899/25000000000000)⟩
def e294 : ℝ := (228289187/10000000000000)
theorem h294 : Model (fun x => f294 ((11/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(7052420236018221/50000000000000),(3681911123683/6250000000000),(39968747381/20000000000000),(-2525307343/100000000000000)⟩
def e295 : ℝ := (5118655013/100000000000000)
theorem h295 : Model (fun x => f295 ((11/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(16440554757750727/100000000000000),(3681911123683/6250000000000),(39968747381/20000000000000),(-2525307343/100000000000000)⟩
def e296 : ℝ := (2559327507/50000000000000)
theorem h296 : Model (fun x => f296 ((11/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(8494206945816711/50000000000000),(1238296760823/1250000000000),(420607281251/100000000000000),(-937150569/25000000000000)⟩
def e297 : ℝ := (1078646673/12500000000000)
theorem h297 : Model (fun x => f297 ((11/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(8695397422007187/50000000000000),(1238296760823/1250000000000),(420607281251/100000000000000),(-937150569/25000000000000)⟩
def e298 : ℝ := (1725834677/20000000000000)
theorem h298 : Model (fun x => f298 ((11/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(1797031943677677/10000000000000),(71381141191961/50000000000000),(746465438337/100000000000000),(-4419826371/100000000000000)⟩
def e299 : ℝ := (12470382159/100000000000000)
theorem h299 : Model (fun x => f299 ((11/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(8976350194578861/50000000000000),(71381141191961/50000000000000),(746465438337/100000000000000),(-4419826371/100000000000000)⟩
def e300 : ℝ := (155879777/1250000000000)
theorem h300 : Model (fun x => f300 ((11/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(18550949720216493/100000000000000),(47305569614421/25000000000000),(1187331051387/100000000000000),(-1053846057/25000000000000)⟩
def e301 : ℝ := (8287695139/50000000000000)
theorem h301 : Model (fun x => f301 ((11/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(9277141526774913/50000000000000),(47305569614421/25000000000000),(1187331051387/100000000000000),(-1053846057/25000000000000)⟩
def e302 : ℝ := (16575390279/100000000000000)
theorem h302 : Model (fun x => f302 ((11/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(618296255407071/100000000000000),(49405639011969/100000000000000),(566306622451/100000000000000),(1384880937/100000000000000)⟩
def e303 : ℝ := (4384515343/100000000000000)
theorem h303 : Model (fun x => f303 ((11/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(106775774570377/100000000000000),(480065058371/100000000000000),(1510780637/100000000000000),(-536293/2500000000000)⟩
def e304 : ℝ := (20841471/50000000000000)
theorem h304 : Model (fun x => f304 ((11/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(50833091008721/25000000000000),(232291723341/100000000000000),(46993321/10000000000000),(-5718187/50000000000000)⟩
def e305 : ℝ := (20099381/100000000000000)
theorem h305 : Model (fun x => f305 ((11/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(82688100528029/20000000000000),(944648505053/100000000000000),(2450647057/100000000000000),(-11081117/25000000000000)⟩
def e306 : ℝ := (10235213/12500000000000)
theorem h306 : Model (fun x => f306 ((11/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(840658347895913/100000000000000),(720291051429/25000000000000),(1140024139/12500000000000),(-31819181/25000000000000)⟩
def e307 : ℝ := (250171947/100000000000000)
theorem h307 : Model (fun x => f307 ((11/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1709330492233359/100000000000000),(3905559527473/50000000000000),(7296885751/25000000000000),(-80052651/25000000000000)⟩
def e308 : ℝ := (13587899/2000000000000)
theorem h308 : Model (fun x => f308 ((11/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(912575436524903/50000000000000),(8273140649413/50000000000000),(9448791247/10000000000000),(-18018403/4000000000000)⟩
def e309 : ℝ := (723625971/50000000000000)
theorem h309 : Model (fun x => f309 ((11/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(25833091008721/3125000000000),(232291723341/12500000000000),(46993321/1250000000000),(-5718187/6250000000000)⟩
def e310 : ℝ := (20099381/12500000000000)
theorem h310 : Model (fun x => f310 ((11/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(933434686849449/100000000000000),(2338398845099/100000000000000),(5270246317/100000000000000),(-14117839/12500000000000)⟩
def e311 : ℝ := (20247799/10000000000000)
theorem h311 : Model (fun x => f311 ((11/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1033434686849449/100000000000000),(2338398845099/100000000000000),(5270246317/100000000000000),(-14117839/12500000000000)⟩
def e312 : ℝ := (20247799/10000000000000)
theorem h312 : Model (fun x => f312 ((11/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(18861742209432247/100000000000000),(106837158631231/50000000000000),(145957885981/10000000000000),(-145402061/4000000000000)⟩
def e313 : ℝ := (18743923139/100000000000000)
theorem h313 : Model (fun x => f313 ((11/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(265086859129/50000000000000),(-1201209369/20000000000000),(13506377/50000000000000),(260929/100000000000000)⟩
def e314 : ℝ := (272649/50000000000000)
theorem h314 : Model (fun x => f314 ((11/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (18646585934335311/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(3278044247141/100000000000000),(112400275319/50000000000000),(2021019/1000000000000),(-11711229/100000000000000)⟩
def e315 : ℝ := (13677367/50000000000000)
theorem h315 : Model (fun x => f315 ((11/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(6667196697203/100000000000000),(465099923869/100000000000000),(97695377/10000000000000),(-21911143/100000000000000)⟩
def e316 : ℝ := (36654399/100000000000000)
theorem h316 : Model (fun x => f316 ((11/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(6482164027339/20000000000000),(34019132867/1562500000000),(-1132579079/100000000000000),(-125572033/100000000000000)⟩
def e317 : ℝ := (89700241/50000000000000)
theorem h317 : Model (fun x => f317 ((11/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(23571505553959/100000000000000),(577431587141/50000000000000),(-2727650767/12500000000000),(305424087/100000000000000)⟩
def e318 : ℝ := (143844143/100000000000000)
theorem h318 : Model (fun x => f318 ((11/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-15620149289671/25000000000000),(-1328869808293/50000000000000),(6925652251/10000000000000),(-74051001/5000000000000)⟩
def e319 : ℝ := (261247379/100000000000000)
theorem h319 : Model (fun x => f319 ((11/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((11/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-1331/64),(-121/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((11/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((11/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(1067/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((11/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(7205/64),(267/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((11/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((11/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(14117/64),(267/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((11/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1764625/32),(6675/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((11/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((11/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(904698651991679753/100000000000000),(1486862512754973/25000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (29393/25000000000000)
theorem h329 : Model (fun x => f329 ((11/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(11053404333/100000000000000),(-14532921/20000000000000),(259163/25000000000000),(-1049/10000000000000)⟩
def e330 : ℝ := (31/25000000000000)
theorem h330 : Model (fun x => f330 ((11/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (224676363081191303/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(609534800660003/100000000000000),(302143269491/50000000000000),(7852885013/100000000000000),(-21095587/100000000000000)⟩
def e331 : ℝ := (13065941/100000000000000)
theorem h331 : Model (fun x => f331 ((11/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((11/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(83/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((11/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((11/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((11/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(525806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((11/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((11/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((11/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(583184218870663/25000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (511/50000000000000)
theorem h339 : Model (fun x => f339 ((11/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3624193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((11/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((11/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((11/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2042263124517089/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (511/50000000000000)
theorem h343 : Model (fun x => f343 ((11/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4896528698947/100000000000000),(-1351067187/20000000000000),(4659889/50000000000000),(-6429/50000000000000)⟩
def e344 : ℝ := (11/50000000000000)
theorem h344 : Model (fun x => f344 ((11/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1019722791440793/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(114223130578927/100000000000000),(928586227581/100000000000000),(-320273421/25000000000000),(441853/25000000000000)⟩
def e345 : ℝ := (3423/100000000000000)
theorem h345 : Model (fun x => f345 ((11/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(214223130578927/100000000000000),(928586227581/100000000000000),(-320273421/25000000000000),(441853/25000000000000)⟩
def e346 : ℝ := (3423/100000000000000)
theorem h346 : Model (fun x => f346 ((11/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(107111565289463/100000000000000),(46429311379/10000000000000),(-320273421/50000000000000),(441853/50000000000000)⟩
def e347 : ℝ := (1713/100000000000000)
theorem h347 : Model (fun x => f347 ((11/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(7111565289463/100000000000000),(46429311379/10000000000000),(-320273421/50000000000000),(441853/50000000000000)⟩
def e348 : ℝ := (1713/100000000000000)
theorem h348 : Model (fun x => f348 ((11/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(395292681425399/100000000000000),(428365670461/25000000000000),(-236392287/10000000000000),(652259/20000000000000)⟩
def e349 : ℝ := (1581/25000000000000)
theorem h349 : Model (fun x => f349 ((11/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(687751741784921/25000000000000),(428365670461/25000000000000),(-236392287/10000000000000),(652259/20000000000000)⟩
def e350 : ℝ := (253/4000000000000)
theorem h350 : Model (fun x => f350 ((11/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1473323311862749/50000000000000),(7304026303743/50000000000000),(-12198033801/100000000000000),(234119/4000000000000)⟩
def e351 : ℝ := (99429/100000000000000)
theorem h351 : Model (fun x => f351 ((11/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(164580551522129/2000000000000),(7304026303743/50000000000000),(-12198033801/100000000000000),(234119/4000000000000)⟩
def e352 : ℝ := (9943/10000000000000)
theorem h352 : Model (fun x => f352 ((11/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(4407120122434587/50000000000000),(6731715271741/12500000000000),(204790111/10000000000000),(-17804107/25000000000000)⟩
def e353 : ℝ := (482727/100000000000000)
theorem h353 : Model (fun x => f353 ((11/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(14083287863916793/100000000000000),(6731715271741/12500000000000),(204790111/10000000000000),(-17804107/25000000000000)⟩
def e354 : ℝ := (60341/12500000000000)
theorem h354 : Model (fun x => f354 ((11/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(7542415037631127/50000000000000),(123071300534521/100000000000000),(32404521369/20000000000000),(-4488691/1562500000000)⟩
def e355 : ℝ := (447043/50000000000000)
theorem h355 : Model (fun x => f355 ((11/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(17420544360976539/100000000000000),(123071300534521/100000000000000),(32404521369/20000000000000),(-4488691/1562500000000)⟩
def e356 : ℝ := (894087/100000000000000)
theorem h356 : Model (fun x => f356 ((11/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(74637670987949/400000000000),(21270598427737/10000000000000),(79171222123/12500000000000),(-47457297/25000000000000)⟩
def e357 : ℝ := (637419/25000000000000)
theorem h357 : Model (fun x => f357 ((11/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(9530899349684101/50000000000000),(21270598427737/10000000000000),(79171222123/12500000000000),(-47457297/25000000000000)⟩
def e358 : ℝ := (2549677/100000000000000)
theorem h358 : Model (fun x => f358 ((11/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(1020869547960989/5000000000000),(39541915993691/12500000000000),(1543891770219/100000000000000),(771666019/50000000000000)⟩
def e359 : ℝ := (767319/12500000000000)
theorem h359 : Model (fun x => f359 ((11/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(5099942977900183/25000000000000),(39541915993691/12500000000000),(1543891770219/100000000000000),(771666019/50000000000000)⟩
def e360 : ℝ := (6138553/100000000000000)
theorem h360 : Model (fun x => f360 ((11/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(2731314376249469/12500000000000),(108386614386181/25000000000000),(373967461357/12500000000000),(1743817083/25000000000000)⟩
def e361 : ℝ := (219813/3125000000000)
theorem h361 : Model (fun x => f361 ((11/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(4370769668665817/20000000000000),(108386614386181/25000000000000),(373967461357/12500000000000),(1743817083/25000000000000)⟩
def e362 : ℝ := (7034017/100000000000000)
theorem h362 : Model (fun x => f362 ((11/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(388537673299019/25000000000000),(132297852344633/100000000000000),(2085701733447/100000000000000),(2360509551/20000000000000)⟩
def e363 : ℝ := (3597309/20000000000000)
theorem h363 : Model (fun x => f363 ((11/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(28682218546897/25000000000000),(994623243423/100000000000000),(783481457/100000000000000),(-253433/6250000000000)⟩
def e364 : ℝ := (16009/100000000000000)
theorem h364 : Model (fun x => f364 ((11/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(207111565289463/100000000000000),(46429311379/10000000000000),(-320273421/50000000000000),(441853/50000000000000)⟩
def e365 : ℝ := (1713/100000000000000)
theorem h365 : Model (fun x => f365 ((11/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(214476002383257/50000000000000),(1923209471003/100000000000000),(-497612227/100000000000000),(-571879/25000000000000)⟩
def e366 : ℝ := (3887/20000000000000)
theorem h366 : Model (fun x => f366 ((11/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(888409211412459/100000000000000),(186711995587/3125000000000),(20121399/390625000000),(-15576473/100000000000000)⟩
def e367 : ℝ := (57299/100000000000000)
theorem h367 : Model (fun x => f367 ((11/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(919999111966059/50000000000000),(16499291163453/100000000000000),(6543662289/20000000000000),(-1938247/5000000000000)⟩
def e368 : ℝ := (46731/25000000000000)
theorem h368 : Model (fun x => f368 ((11/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2111009247388933/100000000000000),(37230501014561/100000000000000),(216059180179/100000000000000),(167803817/50000000000000)⟩
def e369 : ℝ := (65671/5000000000000)
theorem h369 : Model (fun x => f369 ((11/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(107111565289463/12500000000000),(46429311379/1250000000000),(-320273421/6250000000000),(441853/6250000000000)⟩
def e370 : ℝ := (1713/12500000000000)
theorem h370 : Model (fun x => f370 ((11/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(242905349125823/25000000000000),(4708968153743/100000000000000),(-4340893279/100000000000000),(9421/312500000000)⟩
def e371 : ℝ := (29713/100000000000000)
theorem h371 : Model (fun x => f371 ((11/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(267905349125823/25000000000000),(4708968153743/100000000000000),(-4340893279/100000000000000),(9421/312500000000)⟩
def e372 : ℝ := (29713/100000000000000)
theorem h372 : Model (fun x => f372 ((11/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(11311013388591459/50000000000000),(19935070723181/4000000000000),(3976872181623/100000000000000),(12218105903/100000000000000)⟩
def e373 : ℝ := (22330387/100000000000000)
theorem h373 : Model (fun x => f373 ((11/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(110511760269/25000000000000),(-2434640117/25000000000000),(68418001/50000000000000),(-385331/25000000000000)⟩
def e374 : ℝ := (8083/50000000000000)
theorem h374 : Model (fun x => f374 ((11/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (552991522412137/2500000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(1374015430627/20000000000000),(17338673467/4000000000000),(-1537485877/100000000000000),(3066041/50000000000000)⟩
def e375 : ℝ := (88123/12500000000000)
theorem h375 : Model (fun x => f375 ((11/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(114223130578927/50000000000000),(928586227581/50000000000000),(-320273421/12500000000000),(441853/12500000000000)⟩
def e376 : ℝ := (3423/50000000000000)
theorem h376 : Model (fun x => f376 ((11/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(46680299988967/100000000000000),(-202343619721/100000000000000),(1156249259/100000000000000),(-3303569/50000000000000)⟩
def e377 : ℝ := (3819/10000000000000)
theorem h377 : Model (fun x => f377 ((11/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (213293261486827/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(21327880004413/20000000000000),(404687239437/100000000000000),(-2312498519/100000000000000),(206473/1562500000000)⟩
def e378 : ℝ := (12543/5000000000000)
theorem h378 : Model (fun x => f378 ((11/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1327880004413/20000000000000),(404687239437/100000000000000),(-2312498519/100000000000000),(206473/1562500000000)⟩
def e379 : ℝ := (12543/5000000000000)
theorem h379 : Model (fun x => f379 ((11/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(393550166748097/100000000000000),(1493488621731/100000000000000),(-341368829/4000000000000),(12191739/25000000000000)⟩
def e380 : ℝ := (462897/50000000000000)
theorem h380 : Model (fun x => f380 ((11/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1374632226231191/50000000000000),(1493488621731/100000000000000),(-341368829/4000000000000),(12191739/25000000000000)⟩
def e381 : ℝ := (185159/20000000000000)
theorem h381 : Model (fun x => f381 ((11/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1465899558562897/50000000000000),(397455303847/3125000000000),(-1332671673/2000000000000),(346226267/100000000000000)⟩
def e382 : ℝ := (8485929/100000000000000)
theorem h382 : Model (fun x => f382 ((11/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4107090034753373/50000000000000),(397455303847/3125000000000),(-1332671673/2000000000000),(346226267/100000000000000)⟩
def e383 : ℝ := (848593/10000000000000)
theorem h383 : Model (fun x => f383 ((11/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(1751910468570807/20000000000000),(46804745009777/100000000000000),(-41908003513/20000000000000),(222720841/25000000000000)⟩
def e384 : ℝ := (3436161/10000000000000)
theorem h384 : Model (fun x => f384 ((11/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(7014299980950827/50000000000000),(46804745009777/100000000000000),(-41908003513/20000000000000),(222720841/25000000000000)⟩
def e385 : ℝ := (34361611/100000000000000)
theorem h385 : Model (fun x => f385 ((11/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(7480007415433781/50000000000000),(106684253177763/100000000000000),(-89612638347/25000000000000),(873469283/100000000000000)⟩
def e386 : ℝ := (86777179/100000000000000)
theorem h386 : Model (fun x => f386 ((11/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(17295729116581847/100000000000000),(106684253177763/100000000000000),(-89612638347/25000000000000),(873469283/100000000000000)⟩
def e387 : ℝ := (4338859/5000000000000)
theorem h387 : Model (fun x => f387 ((11/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4611015439841121/25000000000000),(183761056209183/100000000000000),(-350475440081/100000000000000),(-175177083/25000000000000)⟩
def e388 : ℝ := (40634417/25000000000000)
theorem h388 : Model (fun x => f388 ((11/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(4711610677936359/25000000000000),(183761056209183/100000000000000),(-350475440081/100000000000000),(-175177083/25000000000000)⟩
def e389 : ℝ := (162537669/100000000000000)
theorem h389 : Model (fun x => f389 ((11/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(2009773343330753/10000000000000),(1701442728487/625000000000),(-16477767397/25000000000000),(-1962306023/50000000000000)⟩
def e390 : ℝ := (251312747/100000000000000)
theorem h390 : Model (fun x => f390 ((11/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(10040057192844241/50000000000000),(1701442728487/625000000000),(-16477767397/25000000000000),(-1962306023/50000000000000)⟩
def e391 : ℝ := (62828187/25000000000000)
theorem h391 : Model (fun x => f391 ((11/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(8364575587751/39062500000),(5805734240057/1562500000000),(567043940423/100000000000000),(-4046904779/50000000000000)⟩
def e392 : ℝ := (34177503/10000000000000)
theorem h392 : Model (fun x => f392 ((11/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(21416646837975893/100000000000000),(5805734240057/1562500000000),(567043940423/100000000000000),(-4046904779/50000000000000)⟩
def e393 : ℝ := (341775031/100000000000000)
theorem h393 : Model (fun x => f393 ((11/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(710968427443077/50000000000000),(2783506394379/2500000000000),(523036437283/50000000000000),(-4005053131/100000000000000)⟩
def e394 : ℝ := (16447557/20000000000000)
theorem h394 : Model (fun x => f394 ((11/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(113719616370659/100000000000000),(431556044101/50000000000000),(-131774059/4000000000000),(9466467/100000000000000)⟩
def e395 : ℝ := (698119/100000000000000)
theorem h395 : Model (fun x => f395 ((11/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(41327880004413/20000000000000),(404687239437/100000000000000),(-2312498519/100000000000000),(206473/1562500000000)⟩
def e396 : ℝ := (12543/5000000000000)
theorem h396 : Model (fun x => f396 ((11/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(426998416414789/100000000000000),(418121641769/25000000000000),(-7919348513/100000000000000),(35895011/100000000000000)⟩
def e397 : ℝ := (1199839/100000000000000)
theorem h397 : Model (fun x => f397 ((11/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(441173482891619/50000000000000),(1296006077871/25000000000000),(-19470486591/100000000000000),(59873147/100000000000000)⟩
def e398 : ℝ := (256931/6250000000000)
theorem h398 : Model (fun x => f398 ((11/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(911638238103689/50000000000000),(3570745578083/25000000000000),(-4957359039/12500000000000),(41642179/100000000000000)⟩
def e399 : ℝ := (484781/4000000000000)
theorem h399 : Model (fun x => f399 ((11/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2073423014119499/100000000000000),(15989736179681/50000000000000),(4528273489/25000000000000),(-74109621/12500000000000)⟩
def e400 : ℝ := (1486953/5000000000000)
theorem h400 : Model (fun x => f400 ((11/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(21327880004413/2500000000000),(404687239437/12500000000000),(-2312498519/12500000000000),(206473/195312500000)⟩
def e401 : ℝ := (12543/625000000000)
theorem h401 : Model (fun x => f401 ((11/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(966834816547179/100000000000000),(2050305001849/50000000000000),(-21794339627/100000000000000),(115180643/100000000000000)⟩
def e402 : ℝ := (2704999/100000000000000)
theorem h402 : Model (fun x => f402 ((11/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1066834816547179/100000000000000),(2050305001849/50000000000000),(-21794339627/100000000000000),(115180643/100000000000000)⟩
def e403 : ℝ := (2704999/100000000000000)
theorem h403 : Model (fun x => f403 ((11/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(11059999304464373/50000000000000),(106547784203429/25000000000000),(263175345443/25000000000000),(-10163803429/100000000000000)⟩
def e404 : ℝ := (38416999/10000000000000)
theorem h404 : Model (fun x => f404 ((11/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(452079594433/100000000000000),(-8710322261/100000000000000),(146309111/100000000000000),(-27459/1250000000000)⟩
def e405 : ℝ := (40319/100000000000000)
theorem h405 : Model (fun x => f405 ((11/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (21692744222759839/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(3214143183331/50000000000000),(18974564717/5000000000000),(-577717981/20000000000000),(1122131/5000000000000)⟩
def e406 : ℝ := (796551/50000000000000)
theorem h406 : Model (fun x => f406 ((11/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(13298363519797/100000000000000),(162591626203/20000000000000),(-2213037891/50000000000000),(14287351/50000000000000)⟩
def e407 : ℝ := (1149043/50000000000000)
theorem h407 : Model (fun x => f407 ((11/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(81058153571437/100000000000000),(2517811471993/50000000000000),(-10510785223/50000000000000),(13028867/6250000000000)⟩
def e408 : ℝ := (8107823/50000000000000)
theorem h408 : Model (fun x => f408 ((11/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(58951384415589/100000000000000),(1295213939489/50000000000000),(-3119355179/5000000000000),(1285919607/100000000000000)⟩
def e409 : ℝ := (9789639/20000000000000)
theorem h409 : Model (fun x => f409 ((11/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-705842548619/20000000000000),(-8413967201/12500000000000),(686941893/10000000000000),(-195100413/100000000000000)⟩
def e410 : ℝ := (155097787/50000000000000)
theorem h410 : Model (fun x => f410 ((11/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(848934936523437/100000000000000),(17669219970703/25000000000000),(9559/409600),(781/2048000)⟩
def e411 : ℝ := (308593751/100000000000000)
theorem h411 : Model (fun x => f411 ((11/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1225/64),(7/32),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((11/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(42875/512),(735/512),(21/2560),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((11/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(35545005276799181/50000000000000),(3568592190742471/50000000000000),(303851847648619/100000000000000),(7136643600463/100000000000000)⟩
def e414 : ℝ := (50814833807/50000000000000)
theorem h414 : Model (fun x => f414 ((11/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(140666739561/100000000000000),(-564897627/4000000000000),(816607197/100000000000000),(-35743909/100000000000000)⟩
def e415 : ℝ := (2025027/100000000000000)
theorem h415 : Model (fun x => f415 ((11/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (15910434012799181/25000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1064655178011/25000000000000),(72109303349/50000000000000),(-5906929379/100000000000000),(6161279/4000000000000)⟩
def e416 : ℝ := (66048707/50000000000000)
theorem h416 : Model (fun x => f416 ((11/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(729407968949/100000000000000),(7690686909/10000000000000),(962489551/100000000000000),(-20534219/50000000000000)⟩
def e417 : ℝ := (110573247/25000000000000)
theorem h417 : Model (fun x => f417 ((11/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((11/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((1093929758717/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (27/20) (7/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (27/20) (7/5) ≤ (1095256637681/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(11/8)-(1/40)) (by norm_num : ((11/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel7


noncomputable section
namespace Hf4Quad.Panel8
open Hf4Quad.Dag

def p0 : Cubic := ⟨(57/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((57/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((57/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((57/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((57/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(49942857142857/20000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((57/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-49942857142857/20000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((57/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-79142857142857/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((57/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((57/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(3249/1600),(57/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((57/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(245823809523809/100000000000000),(2156349206349/25000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((57/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-245823809523809/100000000000000),(-2156349206349/25000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((57/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-404109523809523/100000000000000),(-3251587301587/25000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((57/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((57/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(185193/64000),(9747/64000),(171/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((57/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(36085199/1280000),(1899221/1280000),(2603098958333/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((57/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-36085199/1280000),(-1899221/1280000),(-2603098958333/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((57/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-3223265695684523/100000000000000),(-40345747457837/25000000000000),(-1339380166997/50000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((57/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((57/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(10556001/2560000),(185193/640000),(9747/1280000),(57/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((57/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(287986138392857/25000000000000),(40419107142857/50000000000000),(2127321428571/100000000000000),(1244047619/5000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((57/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-414264228422619/20000000000000),(-40272387772817/50000000000000),(-551438905423/100000000000000),(1931630291/20000000000000)⟩
def e20 : ℝ := (54563497/50000000000000)
theorem h20 : Model (fun x => f20 ((57/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((57/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(293794949707031/50000000000000),(12885743408203/25000000000000),(185193/10240000),(3249/10240000)⟩
def e22 : ℝ := (69824219/25000000000000)
theorem h22 : Model (fun x => f22 ((57/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(3828039381738277/100000000000000),(83948232055663/25000000000000),(2945552001953/25000000000000),(41341080729/20000000000000)⟩
def e23 : ℝ := (1819567429/100000000000000)
theorem h23 : Model (fun x => f23 ((57/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(878359119812591/50000000000000),(127624076338509/50000000000000),(11230769102389/100000000000000),(2163635551/1000000000000)⟩
def e24 : ℝ := (1928694423/100000000000000)
theorem h24 : Model (fun x => f24 ((57/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((57/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(418657803332519/50000000000000),(22034621228027/25000000000000),(193286151123/5000000000000),(90426269531/100000000000000)⟩
def e26 : ℝ := (1198193363/100000000000000)
theorem h26 : Model (fun x => f26 ((57/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(376038881977399/20000000000000),(197915201040733/100000000000000),(4340245636857/50000000000000),(101526213727/50000000000000)⟩
def e27 : ℝ := (2690546369/100000000000000)
theorem h27 : Model (fun x => f27 ((57/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(3636912649512177/100000000000000),(453163353717751/100000000000000),(19911260376103/100000000000000),(209707991277/50000000000000)⟩
def e28 : ℝ := (577405099/12500000000000)
theorem h28 : Model (fun x => f28 ((57/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((57/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(1193174739497679/100000000000000),(146530231166379/100000000000000),(482007339363/6250000000000),(225500509643/100000000000000)⟩
def e30 : ℝ := (999509279/25000000000000)
theorem h30 : Model (fun x => f30 ((57/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(283142259610957/100000000000000),(695437128869/2000000000000),(1830097707549/100000000000000),(428093031/800000000000)⟩
def e31 : ℝ := (237185139/25000000000000)
theorem h31 : Model (fun x => f31 ((57/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(1960027454561567/50000000000000),(487935210161201/100000000000000),(5435339520913/25000000000000),(472927611429/100000000000000)⟩
def e32 : ℝ := (1391995337/25000000000000)
theorem h32 : Model (fun x => f32 ((57/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((57/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1393821/320),(24453/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((57/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((57/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(125913/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((57/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(3408429/320),(8425/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((57/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((57/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(4138029/320),(8425/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((57/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-4138029/320),(-8425/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((57/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((57/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(97/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((57/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(9409/1600),(97/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((57/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((57/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(197589/160),(2037/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((57/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(80976167701/100000000000000),(-834805853/50000000000000),(25818737/100000000000000),(-354897/100000000000000)⟩
def e46 : ℝ := (589/12500000000000)
theorem h46 : Model (fun x => f46 ((57/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (96747/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-209426081409751/20000000000000),(67702757311/25000000000000),(-2852100509/100000000000000),(7506959/25000000000000)⟩
def e47 : ℝ := (30369911/25000000000000)
theorem h47 : Model (fun x => f47 ((57/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((57/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(137/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((57/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((57/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((57/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(22833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((57/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(42833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((57/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((57/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(26770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((57/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((57/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(562187499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((57/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((57/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(1770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((57/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(159286458333301/100000000000000),(9989583333317/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (49/50000000000000)
theorem h60 : Model (fun x => f60 ((57/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(57334201388887/50000000000000),(892361111109/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((57/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((57/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(26770833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((57/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(592750868055547/50000000000000),(5059027777769/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((57/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(642750868055547/50000000000000),(5059027777769/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((57/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1023815093632229/50000000000000),(1705932666917/1250000000000),(97681369357/10000000000000),(504466869/25000000000000)⟩
def e66 : ℝ := (634311/100000000000000)
theorem h66 : Model (fun x => f66 ((57/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(51770833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((57/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(214417534722219/50000000000000),(1725694444441/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((57/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(888045956307851/100000000000000),(1072087673609/20000000000000),(10785590277/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (59/100000000000000)
theorem h69 : Model (fun x => f69 ((57/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(568246783691903/3125000000000),(1321719239465083/100000000000000),(1621104104563/10000000000000),(85148800557/100000000000000)⟩
def e70 : ℝ := (114675371/50000000000000)
theorem h70 : Model (fun x => f70 ((57/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((57/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(1204018229166627/6250000000000),(18739583333289/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((57/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1364553993055253/100000000000000),(22721744791627/25000000000000),(161328124999/25000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (459/50000000000000)
theorem h73 : Model (fun x => f73 ((57/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(1514733319620561/12500000000000),(880264219094957/100000000000000),(10749787267361/100000000000000),(86383141/156250000000)⟩
def e74 : ℝ := (141506463/100000000000000)
theorem h74 : Model (fun x => f74 ((57/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(3787720454388173/12500000000000),(55049586464001/2500000000000),(26960828312991/100000000000000),(140434010797/100000000000000)⟩
def e75 : ℝ := (74171441/20000000000000)
theorem h75 : Model (fun x => f75 ((57/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((57/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(401339409722209/6250000000000),(6246527777763/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((57/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(50173611111/10000000000000),(59027777777/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((57/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(35539641203/100000000000000),(1567925347/25000000000000),(368923611/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((57/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(285269172443/12500000000000),(420492897761/100000000000000),(26858834467/100000000000000),(65497/10000000000)⟩
def e80 : ℝ := (3980793/100000000000000)
theorem h80 : Model (fun x => f80 ((57/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(4725959290139/100000000000000),(110034960191/12500000000000),(57372223449/100000000000000),(734122759/50000000000000)⟩
def e81 : ℝ := (10989189/100000000000000)
theorem h81 : Model (fun x => f81 ((57/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(30306489594395523/100000000000000),(68839491820049/3125000000000),(675455013411/2500000000000),(28380451263/20000000000000)⟩
def e82 : ℝ := (190923197/50000000000000)
theorem h82 : Model (fun x => f82 ((57/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(2517391251/100000000000000),(592327353/100000000000000),(26132089/50000000000000),(81983/4000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((57/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(178315213/100000000000000),(52445651/100000000000000),(1542519/25000000000000),(72589/20000000000000)⟩
def e84 : ℝ := (10803/100000000000000)
theorem h84 : Model (fun x => f84 ((57/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(631533/5000000000000),(111447/2500000000000),(65557/10000000000000),(51417/100000000000000)⟩
def e85 : ℝ := (93/4000000000000)
theorem h85 : Model (fun x => f85 ((57/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(894671/100000000000000),(184197/50000000000000),(6501/10000000000000),(6373/100000000000000)⟩
def e86 : ℝ := (391/100000000000000)
theorem h86 : Model (fun x => f86 ((57/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(2684013/100000000000000),(552591/50000000000000),(19503/10000000000000),(19119/100000000000000)⟩
def e87 : ℝ := (1173/100000000000000)
theorem h87 : Model (fun x => f87 ((57/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-2684013/100000000000000),(-552591/50000000000000),(-19503/10000000000000),(-19119/100000000000000)⟩
def e88 : ℝ := (1173/100000000000000)
theorem h88 : Model (fun x => f88 ((57/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(3030648959171151/10000000000000),(1101431868568193/50000000000000),(2701820034141/10000000000000),(35475559299/25000000000000)⟩
def e89 : ℝ := (381847567/100000000000000)
theorem h89 : Model (fun x => f89 ((57/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(1204018229166627/5000000000000),(18739583333289/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((57/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(919497583927081/50000000000000),(3700191484609/25000000000000),(11167579933/25000000000000),(11983989/20000000000000)⟩
def e91 : ℝ := (30301/100000000000000)
theorem h91 : Model (fun x => f91 ((57/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(442836741089150421/100000000000000),(3505139359426487/50000000000000),(45197464404361/100000000000000),(76050192471/50000000000000)⟩
def e92 : ℝ := (28276279/10000000000000)
theorem h92 : Model (fun x => f92 ((57/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(4516337093/20000000000000),(-357476909/100000000000000),(3354233/100000000000000),(-2437/10000000000000)⟩
def e93 : ℝ := (47/25000000000000)
theorem h93 : Model (fun x => f93 ((57/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (217890556261372677/50000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(6843716155083/100000000000000),(389105058123/100000000000000),(-757013903/100000000000000),(98179/5000000000000)⟩
def e94 : ℝ := (36061/12500000000000)
theorem h94 : Model (fun x => f94 ((57/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(22833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((57/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(46692607003891/100000000000000),(-36336659147/20000000000000),(706938893/100000000000000),(-550147/20000000000000)⟩
def e96 : ℝ := (2687/25000000000000)
theorem h96 : Model (fun x => f96 ((57/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (213333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(13326848249027/12500000000000),(363366591469/100000000000000),(-141387779/10000000000000),(5501469/100000000000000)⟩
def e97 : ℝ := (70573/100000000000000)
theorem h97 : Model (fun x => f97 ((57/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(279863813229567/12500000000000),(7630698420849/100000000000000),(-2969143359/10000000000000),(115530849/100000000000000)⟩
def e98 : ℝ := (1482033/100000000000000)
theorem h98 : Model (fun x => f98 ((57/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(826848249027/12500000000000),(363366591469/100000000000000),(-141387779/10000000000000),(5501469/100000000000000)⟩
def e99 : ℝ := (70573/100000000000000)
theorem h99 : Model (fun x => f99 ((57/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(148099138518327/100000000000000),(172804143227/2000000000000),(-5892074413/100000000000000),(-16992483/20000000000000)⟩
def e100 : ℝ := (2951589/100000000000000)
theorem h100 : Model (fun x => f100 ((57/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(5683356296083/5000000000000),(774805027723/100000000000000),(-1694452763/100000000000000),(1455639/100000000000000)⟩
def e101 : ℝ := (26391/12500000000000)
theorem h101 : Model (fun x => f101 ((57/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(13326848249027/1250000000000),(363366591469/10000000000000),(-141387779/1000000000000),(5501469/10000000000000)⟩
def e102 : ℝ := (70573/10000000000000)
theorem h102 : Model (fun x => f102 ((57/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(58990749292191/5000000000000),(4408470942413/100000000000000),(-15833230663/100000000000000),(56470329/100000000000000)⟩
def e103 : ℝ := (458429/50000000000000)
theorem h103 : Model (fun x => f103 ((57/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(63990749292191/5000000000000),(4408470942413/100000000000000),(-15833230663/100000000000000),(56470329/100000000000000)⟩
def e104 : ℝ := (458429/50000000000000)
theorem h104 : Model (fun x => f104 ((57/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(947697484331573/50000000000000),(29276893386613/25000000000000),(141022246273/50000000000000),(-2631503967/100000000000000)⟩
def e105 : ℝ := (4141929/10000000000000)
theorem h105 : Model (fun x => f105 ((57/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(25826848249027/12500000000000),(363366591469/100000000000000),(-141387779/10000000000000),(5501469/100000000000000)⟩
def e106 : ℝ := (70573/100000000000000)
theorem h106 : Model (fun x => f106 ((57/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(106724174476523/25000000000000),(1501538210661/100000000000000),(-4522208343/100000000000000),(12458577/100000000000000)⟩
def e107 : ℝ := (176137/50000000000000)
theorem h107 : Model (fun x => f107 ((57/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(220507924696627/25000000000000),(4653599940823/100000000000000),(-9923260473/100000000000000),(5782371/50000000000000)⟩
def e108 : ℝ := (305929/25000000000000)
theorem h108 : Model (fun x => f108 ((57/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(16717984440813547/100000000000000),(2242260038999/200000000000),(7749354822461/100000000000000),(-859486753/4000000000000)⟩
def e109 : ℝ := (264546107/50000000000000)
theorem h109 : Model (fun x => f109 ((57/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(119350482217743/625000000000),(16270905582183/12500000000000),(-35583508023/12500000000000),(30568419/12500000000000)⟩
def e110 : ℝ := (554211/1562500000000)
theorem h110 : Model (fun x => f110 ((57/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1263164636701041/100000000000000),(77999049327883/100000000000000),(184158903233/100000000000000),(-452013339/25000000000000)⟩
def e111 : ℝ := (14069033/50000000000000)
theorem h111 : Model (fun x => f111 ((57/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(5570756251782307/50000000000000),(746758968610069/100000000000000),(2564378249457/50000000000000),(-748577611/5000000000000)⟩
def e112 : ℝ := (359507877/100000000000000)
theorem h112 : Model (fun x => f112 ((57/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(27859496944378161/100000000000000),(1867888988109569/100000000000000),(103024890571/800000000000),(-7291744209/20000000000000)⟩
def e113 : ℝ := (888600091/100000000000000)
theorem h113 : Model (fun x => f113 ((57/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(39783494072581/625000000000),(5423635194061/12500000000000),(-11861169341/12500000000000),(10189473/12500000000000)⟩
def e114 : ℝ := (184737/1562500000000)
theorem h114 : Model (fun x => f114 ((57/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(109388484307/25000000000000),(9614368957/20000000000000),(1133302817/100000000000000),(-9547299/100000000000000)⟩
def e115 : ℝ := (34991/50000000000000)
theorem h115 : Model (fun x => f115 ((57/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(7235814137/25000000000000),(2384887241/50000000000000),(243456101/100000000000000),(566181/20000000000000)⟩
def e116 : ℝ := (53499/100000000000000)
theorem h116 : Model (fun x => f116 ((57/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(1842342200509/100000000000000),(316171484919/100000000000000),(2192369029/12500000000000),(140664109/50000000000000)⟩
def e117 : ℝ := (34659/781250000000)
theorem h117 : Model (fun x => f117 ((57/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(152262055793/4000000000000),(65995149299/10000000000000),(373608817/1000000000000),(128125493/20000000000000)⟩
def e118 : ℝ := (4989289/50000000000000)
theorem h118 : Model (fun x => f118 ((57/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(13931651747886493/50000000000000),(1868548939602559/100000000000000),(516618888123/4000000000000),(-1790904679/5000000000000)⟩
def e119 : ℝ := (898578669/100000000000000)
theorem h119 : Model (fun x => f119 ((57/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(1914534479/100000000000000),(420680499/100000000000000),(8256661/25000000000000),(1006049/100000000000000)⟩
def e120 : ℝ := (2179/20000000000000)
theorem h120 : Model (fun x => f120 ((57/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(63321179/50000000000000),(34783893/100000000000000),(737237/20000000000000),(180713/100000000000000)⟩
def e121 : ℝ := (997/25000000000000)
theorem h121 : Model (fun x => f121 ((57/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(52357/625000000000),(86283/3125000000000),(73687/20000000000000),(24863/100000000000000)⟩
def e122 : ℝ := (89/10000000000000)
theorem h122 : Model (fun x => f122 ((57/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(34633/6250000000000),(213077/100000000000000),(6857/20000000000000),(23/781250000000)⟩
def e123 : ℝ := (151/100000000000000)
theorem h123 : Model (fun x => f123 ((57/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(103899/6250000000000),(639231/100000000000000),(20571/20000000000000),(69/781250000000)⟩
def e124 : ℝ := (453/100000000000000)
theorem h124 : Model (fun x => f124 ((57/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-103899/6250000000000),(-639231/100000000000000),(-20571/20000000000000),(-69/781250000000)⟩
def e125 : ℝ := (453/100000000000000)
theorem h125 : Model (fun x => f125 ((57/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(13931651747055301/50000000000000),(14598038585651/781250000000),(645773605011/5000000000000),(-8954525603/25000000000000)⟩
def e126 : ℝ := (449289561/50000000000000)
theorem h126 : Model (fun x => f126 ((57/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(119350482217743/500000000000),(16270905582183/10000000000000),(-35583508023/10000000000000),(30568419/10000000000000)⟩
def e127 : ℝ := (554211/1250000000000)
theorem h127 : Model (fun x => f127 ((57/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(291585265093/16000000000),(12820034078221/100000000000000),(-3212829239/20000000000000),(-14717431/50000000000000)⟩
def e128 : ℝ := (112427/3125000000000)
theorem h128 : Model (fun x => f128 ((57/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(43501052495547469/10000000000000),(6025377196994651/100000000000000),(527003128887/5000000000000),(-73211316247/100000000000000)⟩
def e129 : ℝ := (215854447/12500000000000)
theorem h129 : Model (fun x => f129 ((57/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(11493974773/50000000000000),(-159204271/50000000000000),(154133/4000000000000),(-4179/10000000000000)⟩
def e130 : ℝ := (67/12500000000000)
theorem h130 : Model (fun x => f130 ((57/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (107243633189437619/25000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(256208085963/4000000000000),(170410974461/50000000000000),(-119184599/6250000000000),(17599/160000000000)⟩
def e131 : ℝ := (544831/100000000000000)
theorem h131 : Model (fun x => f131 ((57/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(6624459152079/50000000000000),(145985401409/20000000000000),(-2663967487/100000000000000),(2592591/20000000000000)⟩
def e132 : ℝ := (833319/100000000000000)
theorem h132 : Model (fun x => f132 ((57/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-138733452167887/100000000000000),(-3803704054003/50000000000000),(7373515991/25000000000000),(-639173/400000000000)⟩
def e133 : ℝ := (13022181/50000000000000)
theorem h133 : Model (fun x => f133 ((57/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(70175438596491/100000000000000),(-1231148045553/100000000000000),(10799544259/50000000000000),(-189465689/50000000000000)⟩
def e134 : ℝ := (3383317/50000000000000)
theorem h134 : Model (fun x => f134 ((57/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (7/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-24339202134717/25000000000000),(-1815258910363/50000000000000),(84390883847/100000000000000),(-398169359/25000000000000)⟩
def e135 : ℝ := (32909477/50000000000000)
theorem h135 : Model (fun x => f135 ((57/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(10556001/256000),(185193/64000),(9747/128000),(57/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((57/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((57/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(1666737/32000),(87723/32000),(1539/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((57/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(23889897/256000),(360639/64000),(15903/128000),(3/2560)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((57/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-3249/1600),(-57/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((57/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(23370057/256000),(356079/64000),(15823/128000),(3/2560)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((57/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((57/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(171/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((57/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-171/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((57/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(21181257/256000),(346479/64000),(15823/128000),(3/2560)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((57/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(21949257/256000),(346479/64000),(15823/128000),(3/2560)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((57/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((57/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(21949257/4000),(346479/1000),(15823/2000),(3/40)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((57/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((57/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(1995084189/512000),(35001477/128000),(1842183/256000),(10773/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((57/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(25663077419/100000000000000),(-900458857/50000000000000),(78987619/100000000000000),(-346437/12500000000000)⟩
def e151 : ℝ := (100871/100000000000000)
theorem h151 : Model (fun x => f151 ((57/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (925675317/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(140821370420131/100000000000000),(-247621008513/25000000000000),(12483155683/100000000000000),(-8187397/5000000000000)⟩
def e152 : ℝ := (1082786557/100000000000000)
theorem h152 : Model (fun x => f152 ((57/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(177/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((57/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(24249/1600),(157/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((57/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(291/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((57/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1718213058419/25000000000000),(-70854146739/100000000000000),(730455121/100000000000000),(-3765233/50000000000000)⟩
def e156 : ℝ := (15689/20000000000000)
theorem h156 : Model (fun x => f156 ((57/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (72/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(20832474226801/20000000000000),(274958373187/100000000000000),(1460910241/100000000000000),(-15060943/100000000000000)⟩
def e157 : ℝ := (557589/25000000000000)
theorem h157 : Model (fun x => f157 ((57/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(40832474226801/20000000000000),(274958373187/100000000000000),(1460910241/100000000000000),(-15060943/100000000000000)⟩
def e158 : ℝ := (557589/25000000000000)
theorem h158 : Model (fun x => f158 ((57/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(51040592783501/50000000000000),(137479186593/100000000000000),(9130689/1250000000000),(-941309/12500000000000)⟩
def e159 : ℝ := (55759/5000000000000)
theorem h159 : Model (fun x => f159 ((57/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(1040592783501/50000000000000),(137479186593/100000000000000),(9130689/1250000000000),(-941309/12500000000000)⟩
def e160 : ℝ := (55759/5000000000000)
theorem h160 : Model (fun x => f160 ((57/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((57/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((57/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(188364092415301/50000000000000),(507363664807/100000000000000),(673931807/25000000000000),(-6947757/25000000000000)⟩
def e163 : ℝ := (1028887/25000000000000)
theorem h163 : Model (fun x => f163 ((57/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2732442470544887/100000000000000),(507363664807/100000000000000),(673931807/25000000000000),(-6947757/25000000000000)⟩
def e164 : ℝ := (4115549/100000000000000)
theorem h164 : Model (fun x => f164 ((57/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((57/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(5578619337737/200000000000),(4274462526797/100000000000000),(18287981/78125000000),(-226723099/100000000000000)⟩
def e166 : ℝ := (8685341/25000000000000)
theorem h166 : Model (fun x => f166 ((57/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(2017922655312363/25000000000000),(4274462526797/100000000000000),(18287981/78125000000),(-226723099/100000000000000)⟩
def e167 : ℝ := (6948273/20000000000000)
theorem h167 : Model (fun x => f167 ((57/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((57/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8239677481471949/100000000000000),(60391861853/390625000000),(88732366137/100000000000000),(-31034921/4000000000000)⟩
def e169 : ℝ := (126040261/100000000000000)
theorem h169 : Model (fun x => f169 ((57/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(844295318782473/6250000000000),(60391861853/390625000000),(88732366137/100000000000000),(-31034921/4000000000000)⟩
def e170 : ℝ := (63020131/50000000000000)
theorem h170 : Model (fun x => f170 ((57/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((57/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(13789866737597557/100000000000000),(34353759900053/100000000000000),(210508943031/100000000000000),(-314874387/20000000000000)⟩
def e172 : ℝ := (140626387/50000000000000)
theorem h172 : Model (fun x => f172 ((57/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(8062790511655921/50000000000000),(34353759900053/100000000000000),(210508943031/100000000000000),(-314874387/20000000000000)⟩
def e173 : ℝ := (11250111/4000000000000)
theorem h173 : Model (fun x => f173 ((57/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((57/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(16461184288164221/100000000000000),(57238043017059/100000000000000),(379909426659/100000000000000),(-1782129/78125000000)⟩
def e175 : ℝ := (47095087/10000000000000)
theorem h175 : Model (fun x => f175 ((57/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(16863565240545173/100000000000000),(57238043017059/100000000000000),(379909426659/100000000000000),(-1782129/78125000000)⟩
def e176 : ℝ := (470950871/100000000000000)
theorem h176 : Model (fun x => f176 ((57/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((57/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(3442905465282673/20000000000000),(16322633046089/20000000000000),(58968721849/10000000000000),(-2658111021/100000000000000)⟩
def e178 : ℝ := (337410797/50000000000000)
theorem h178 : Model (fun x => f178 ((57/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(17196908278794317/100000000000000),(16322633046089/20000000000000),(58968721849/10000000000000),(-2658111021/100000000000000)⟩
def e179 : ℝ := (134964319/20000000000000)
theorem h179 : Model (fun x => f179 ((57/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((57/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(4388701962965789/25000000000000),(4278154250673/4000000000000),(839776516487/100000000000000),(-325199359/12500000000000)⟩
def e181 : ℝ := (888048663/100000000000000)
theorem h181 : Model (fun x => f181 ((57/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(17558141185196489/100000000000000),(4278154250673/4000000000000),(839776516487/100000000000000),(-325199359/12500000000000)⟩
def e182 : ℝ := (111006083/12500000000000)
theorem h182 : Model (fun x => f182 ((57/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(365417500180143/100000000000000),(5272939580447/20000000000000),(58554188109/20000000000000),(13985323/2500000000000)⟩
def e183 : ℝ := (11114771/5000000000000)
theorem h183 : Model (fun x => f183 ((57/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(52102842233823/50000000000000),(70170191791/25000000000000),(21003997/1250000000000),(-13365943/100000000000000)⟩
def e184 : ℝ := (143459/6250000000000)
theorem h184 : Model (fun x => f184 ((57/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(101040592783501/50000000000000),(137479186593/100000000000000),(9130689/1250000000000),(-941309/12500000000000)⟩
def e185 : ℝ := (55759/5000000000000)
theorem h185 : Model (fun x => f185 ((57/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(8167361112033/2000000000000),(11112782807/2000000000000),(314123/10000000000),(-28426887/100000000000000)⟩
def e186 : ℝ := (565713/12500000000000)
theorem h186 : Model (fun x => f186 ((57/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(103154376029591/12500000000000),(21053290543/1250000000000),(5047334183/50000000000000),(-79820201/100000000000000)⟩
def e187 : ℝ := (13770549/100000000000000)
theorem h187 : Model (fun x => f187 ((57/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(833822344179363/50000000000000),(4538105507217/100000000000000),(28742908289/100000000000000),(-39452969/20000000000000)⟩
def e188 : ℝ := (18616329/50000000000000)
theorem h188 : Model (fun x => f188 ((57/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(217222570249069/12500000000000),(4704860905257/50000000000000),(14142219379/20000000000000),(-135763561/50000000000000)⟩
def e189 : ℝ := (4873197/6250000000000)
theorem h189 : Model (fun x => f189 ((57/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((57/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(51040592783501/6250000000000),(137479186593/12500000000000),(9130689/156250000000),(-941309/1562500000000)⟩
def e191 : ℝ := (55759/625000000000)
theorem h191 : Model (fun x => f191 ((57/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(460427584501831/50000000000000),(345128564977/25000000000000),(94049509/1250000000000),(-73609719/100000000000000)⟩
def e192 : ℝ := (701049/6250000000000)
theorem h192 : Model (fun x => f192 ((57/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(510427584501831/50000000000000),(345128564977/25000000000000),(94049509/1250000000000),(-73609719/100000000000000)⟩
def e193 : ℝ := (701049/6250000000000)
theorem h193 : Model (fun x => f193 ((57/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(8870111346520927/50000000000000),(120049939955713/100000000000000),(982510366007/100000000000000),(-4733827/200000000000)⟩
def e194 : ℝ := (49923437/5000000000000)
theorem h194 : Model (fun x => f194 ((57/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(70461347731/12500000000000),(-4768193/125000000000),(-2702757/50000000000000),(323049/100000000000000)⟩
def e195 : ℝ := (6919/20000000000000)
theorem h195 : Model (fun x => f195 ((57/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (8809593438668947/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(1029912381887/50000000000000),(26935264481/20000000000000),(124974873/20000000000000),(-4129609/50000000000000)⟩
def e196 : ℝ := (361529/25000000000000)
theorem h196 : Model (fun x => f196 ((57/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(20832474226801/10000000000000),(274958373187/50000000000000),(1460910241/50000000000000),(-15060943/50000000000000)⟩
def e197 : ℝ := (557589/12500000000000)
theorem h197 : Model (fun x => f197 ((57/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(612257779461/1250000000000),(-16491325221/25000000000000),(-52329507/20000000000000),(4437673/100000000000000)⟩
def e198 : ℝ := (136393/25000000000000)
theorem h198 : Model (fun x => f198 ((57/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (101942967279639/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(102038755286237/100000000000000),(26386120353/20000000000000),(261647533/50000000000000),(-2218837/25000000000000)⟩
def e199 : ℝ := (1682129/50000000000000)
theorem h199 : Model (fun x => f199 ((57/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(2038755286237/100000000000000),(26386120353/20000000000000),(261647533/50000000000000),(-2218837/25000000000000)⟩
def e200 : ℝ := (1682129/50000000000000)
theorem h200 : Model (fun x => f200 ((57/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(94142899222421/25000000000000),(15215210769/3125000000000),(1931207981/100000000000000),(-32754261/100000000000000)⟩
def e201 : ℝ := (12415717/100000000000000)
theorem h201 : Model (fun x => f201 ((57/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2732285882603969/100000000000000),(15215210769/3125000000000),(1931207981/100000000000000),(-32754261/100000000000000)⟩
def e202 : ℝ := (6207859/50000000000000)
theorem h202 : Model (fun x => f202 ((57/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(348498813183833/12500000000000),(4101534380711/100000000000000),(1691085041/10000000000000),(-270826213/100000000000000)⟩
def e203 : ℝ := (3271861/3125000000000)
theorem h203 : Model (fun x => f203 ((57/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(252199108057863/3125000000000),(4101534380711/100000000000000),(1691085041/10000000000000),(-270826213/100000000000000)⟩
def e204 : ℝ := (104699553/100000000000000)
theorem h204 : Model (fun x => f204 ((57/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8234906582567527/100000000000000),(14832444258729/100000000000000),(64898655903/100000000000000),(-189769507/20000000000000)⟩
def e205 : ℝ := (379255273/100000000000000)
theorem h205 : Model (fun x => f205 ((57/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6751977100807573/50000000000000),(14832444258729/100000000000000),(64898655903/100000000000000),(-189769507/20000000000000)⟩
def e206 : ℝ := (189627637/50000000000000)
theorem h206 : Model (fun x => f206 ((57/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(6889633390875799/50000000000000),(4118836192549/12500000000000),(156455839699/100000000000000),(-500869127/25000000000000)⟩
def e207 : ℝ := (33781531/4000000000000)
theorem h207 : Model (fun x => f207 ((57/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16114981067465883/100000000000000),(4118836192549/12500000000000),(156455839699/100000000000000),(-500869127/25000000000000)⟩
def e208 : ℝ := (211134569/25000000000000)
theorem h208 : Model (fun x => f208 ((57/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(3288705219170987/20000000000000),(54883064961871/100000000000000),(28744653521/10000000000000),(-1547870339/50000000000000)⟩
def e209 : ℝ := (1410912001/100000000000000)
theorem h209 : Model (fun x => f209 ((57/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16845907048235887/100000000000000),(54883064961871/100000000000000),(28744653521/10000000000000),(-1547870339/50000000000000)⟩
def e210 : ℝ := (705456001/50000000000000)
theorem h210 : Model (fun x => f210 ((57/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(17189353868696367/100000000000000),(3911345144577/5000000000000),(453868224919/100000000000000),(-797511563/20000000000000)⟩
def e211 : ℝ := (2017635071/100000000000000)
theorem h211 : Model (fun x => f211 ((57/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(17171734821077319/100000000000000),(3911345144577/5000000000000),(453868224919/100000000000000),(-797511563/20000000000000)⟩
def e212 : ℝ := (7881387/390625000000)
theorem h212 : Model (fun x => f212 ((57/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(2190228059060079/12500000000000),(51238265546219/50000000000000),(656185552139/100000000000000),(-4584756981/100000000000000)⟩
def e213 : ℝ := (662920293/25000000000000)
theorem h213 : Model (fun x => f213 ((57/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(3505031561162793/20000000000000),(51238265546219/50000000000000),(656185552139/100000000000000),(-4584756981/100000000000000)⟩
def e214 : ℝ := (2651681173/100000000000000)
theorem h214 : Model (fun x => f214 ((57/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(22330942574213/6250000000000),(1008411673931/4000000000000),(60071051969/25000000000000),(-12346327/5000000000000)⟩
def e215 : ℝ := (331213949/50000000000000)
theorem h215 : Model (fun x => f215 ((57/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(20823815160729/20000000000000),(53848137553/20000000000000),(62099219/5000000000000),(-16731817/100000000000000)⟩
def e216 : ℝ := (6895383/100000000000000)
theorem h216 : Model (fun x => f216 ((57/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(202038755286237/100000000000000),(26386120353/20000000000000),(261647533/50000000000000),(-2218837/25000000000000)⟩
def e217 : ℝ := (1682129/50000000000000)
theorem h217 : Model (fun x => f217 ((57/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(408196586376119/100000000000000),(106620378259/20000000000000),(143035907/6250000000000),(-34482513/100000000000000)⟩
def e218 : ℝ := (13623899/100000000000000)
theorem h218 : Model (fun x => f218 ((57/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(41235765111761/5000000000000),(161560863837/10000000000000),(7463204587/100000000000000),(-50043941/50000000000000)⟩
def e219 : ℝ := (20687811/50000000000000)
theorem h219 : Model (fun x => f219 ((57/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(333248906258233/20000000000000),(2176103722173/50000000000000),(4305148467/20000000000000),(-128556007/50000000000000)⟩
def e220 : ℝ := (111687341/100000000000000)
theorem h220 : Model (fun x => f220 ((57/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1734878406609137/100000000000000),(1803537280801/20000000000000),(27412407023/50000000000000),(-217242923/50000000000000)⟩
def e221 : ℝ := (116472721/50000000000000)
theorem h221 : Model (fun x => f221 ((57/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(102038755286237/12500000000000),(26386120353/2500000000000),(261647533/6250000000000),(-2218837/3125000000000)⟩
def e222 : ℝ := (1682129/6250000000000)
theorem h222 : Model (fun x => f222 ((57/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(920429118093541/100000000000000),(264937100377/20000000000000),(1357086227/25000000000000),(-87734601/100000000000000)⟩
def e223 : ℝ := (33809447/100000000000000)
theorem h223 : Model (fun x => f223 ((57/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1020429118093541/100000000000000),(264937100377/20000000000000),(1357086227/25000000000000),(-87734601/100000000000000)⟩
def e224 : ℝ := (33809447/100000000000000)
theorem h224 : Model (fun x => f224 ((57/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(17703204424556893/100000000000000),(57500390286257/50000000000000),(77307953451/10000000000000),(-4739941251/100000000000000)⟩
def e225 : ℝ := (2980525341/100000000000000)
theorem h225 : Model (fun x => f225 ((57/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(8826085733/1562500000000),(-733883317/20000000000000),(-830543/100000000000000),(507/160000000000)⟩
def e226 : ℝ := (9939/10000000000000)
theorem h226 : Model (fun x => f226 ((57/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (17587422843983277/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(403650178373/20000000000000),(25858920249/20000000000000),(107313513/25000000000000),(-1857809/20000000000000)⟩
def e227 : ℝ := (4234297/100000000000000)
theorem h227 : Model (fun x => f227 ((57/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(4078075655639/100000000000000),(5279418473/2000000000000),(1054128417/100000000000000),(-17548263/100000000000000)⟩
def e228 : ℝ := (5680413/100000000000000)
theorem h228 : Model (fun x => f228 ((57/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(71785025313/1250000000000),(41416847991/12500000000000),(-310539619/50000000000000),(-4439271/50000000000000)⟩
def e229 : ℝ := (27606887/50000000000000)
theorem h229 : Model (fun x => f229 ((57/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(4030036508799/100000000000000),(20226655369/12500000000000),(-204667119/6250000000000),(51219863/100000000000000)⟩
def e230 : ℝ := (41130311/100000000000000)
theorem h230 : Model (fun x => f230 ((57/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-93326772030069/100000000000000),(-1734352288887/50000000000000),(81116209943/100000000000000),(-1541457573/100000000000000)⟩
def e231 : ℝ := (21389853/20000000000000)
theorem h231 : Model (fun x => f231 ((57/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((57/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-3249/320),(-57/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((57/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1197/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((57/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6327/320),(27/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((57/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((57/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14647/320),(27/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((57/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((57/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(366175/32),(675/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((57/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(10431/1600),(63/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((57/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(20031/1600),(63/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((57/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((57/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3785859/1600),(11907/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((57/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(21131267699/50000000000000),(-265841919/100000000000000),(945517/25000000000000),(-18531/50000000000000)⟩
def e244 : ℝ := (429/100000000000000)
theorem h244 : Model (fun x => f244 ((57/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (58779/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(241804435927541/50000000000000),(-629535029727/50000000000000),(-238681451/25000000000000),(-11370863/20000000000000)⟩
def e245 : ℝ := (4737359/50000000000000)
theorem h245 : Model (fun x => f245 ((57/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(513/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((57/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(44289/1600),(417/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((57/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(77889/1600),(417/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((57/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(18769/1600),(137/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((57/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1461898641/2560000),(9248733/640000),(162587/1280000),(277/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((57/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((57/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(84681/160),(873/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((57/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(188944391303/100000000000000),(-1947880323/50000000000000),(60243721/100000000000000),(-828093/100000000000000)⟩
def e253 : ℝ := (1099/10000000000000)
theorem h253 : Model (fun x => f253 ((57/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (41463/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(10789748002751/10000000000000),(252886272263/50000000000000),(2104147331/100000000000000),(-3840367/25000000000000)⟩
def e254 : ℝ := (12591731/100000000000000)
theorem h254 : Model (fun x => f254 ((57/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(20789748002751/10000000000000),(252886272263/50000000000000),(2104147331/100000000000000),(-3840367/25000000000000)⟩
def e255 : ℝ := (12591731/100000000000000)
theorem h255 : Model (fun x => f255 ((57/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(20789748002751/20000000000000),(252886272263/100000000000000),(210414733/20000000000000),(-3840367/50000000000000)⟩
def e256 : ℝ := (3147933/50000000000000)
theorem h256 : Model (fun x => f256 ((57/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(789748002751/20000000000000),(252886272263/100000000000000),(210414733/20000000000000),(-3840367/50000000000000)⟩
def e257 : ℝ := (3147933/50000000000000)
theorem h257 : Model (fun x => f257 ((57/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(191810175025381/50000000000000),(233317691671/25000000000000),(3882652811/100000000000000),(-14172783/50000000000000)⟩
def e258 : ℝ := (11617373/50000000000000)
theorem h258 : Model (fun x => f258 ((57/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2739334635765047/100000000000000),(233317691671/25000000000000),(3882652811/100000000000000),(-14172783/50000000000000)⟩
def e259 : ℝ := (23234747/100000000000000)
theorem h259 : Model (fun x => f259 ((57/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2847503838638151/100000000000000),(98719055601/1250000000000),(35215900627/100000000000000),(-110114237/50000000000000)⟩
def e260 : ℝ := (19683819/10000000000000)
theorem h260 : Model (fun x => f260 ((57/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8129884791019103/100000000000000),(98719055601/1250000000000),(35215900627/100000000000000),(-110114237/50000000000000)⟩
def e261 : ℝ := (196838191/100000000000000)
theorem h261 : Model (fun x => f261 ((57/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(528182050302141/6250000000000),(14384369871671/50000000000000),(28422123409/20000000000000),(-170303899/25000000000000)⟩
def e262 : ℝ := (359127427/50000000000000)
theorem h262 : Model (fun x => f262 ((57/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(21951936678211/160000000000),(14384369871671/50000000000000),(28422123409/20000000000000),(-170303899/25000000000000)⟩
def e263 : ℝ := (143650971/20000000000000)
theorem h263 : Model (fun x => f263 ((57/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(1782715748876381/12500000000000),(32300319476477/50000000000000),(182409239913/50000000000000),(-549931059/50000000000000)⟩
def e264 : ℝ := (1616506831/100000000000000)
theorem h264 : Model (fun x => f264 ((57/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(16597440276725333/100000000000000),(32300319476477/50000000000000),(182409239913/50000000000000),(-549931059/50000000000000)⟩
def e265 : ℝ := (101031677/6250000000000)
theorem h265 : Model (fun x => f265 ((57/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(8626415021095737/50000000000000),(109124198239319/100000000000000),(358603829519/50000000000000),(-815875889/100000000000000)⟩
def e266 : ℝ := (2737431171/100000000000000)
theorem h266 : Model (fun x => f266 ((57/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(8827605497286213/50000000000000),(109124198239319/100000000000000),(358603829519/50000000000000),(-815875889/100000000000000)⟩
def e267 : ℝ := (684357793/25000000000000)
theorem h267 : Model (fun x => f267 ((57/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(18352369375627979/100000000000000),(6323233362569/4000000000000),(120723426729/10000000000000),(189411041/25000000000000)⟩
def e268 : ℝ := (248368993/6250000000000)
theorem h268 : Model (fun x => f268 ((57/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(18334750328008931/100000000000000),(6323233362569/4000000000000),(120723426729/10000000000000),(189411041/25000000000000)⟩
def e269 : ℝ := (3973903889/100000000000000)
theorem h269 : Model (fun x => f269 ((57/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(3811748390126619/20000000000000),(105344550923113/50000000000000),(923782309017/50000000000000),(6399023/156250000000)⟩
def e270 : ℝ := (165869837/3125000000000)
theorem h270 : Model (fun x => f270 ((57/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(4765518820991607/25000000000000),(105344550923113/50000000000000),(923782309017/50000000000000),(6399023/156250000000)⟩
def e271 : ℝ := (1061566957/20000000000000)
theorem h271 : Model (fun x => f271 ((57/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(188177948547521/25000000000000),(14131234117703/25000000000000),(40315320657/5000000000000),(698306281/12500000000000)⟩
def e272 : ℝ := (1450287013/100000000000000)
theorem h272 : Model (fun x => f272 ((57/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(13506675688059/12500000000000),(52574418737/10000000000000),(353343663/12500000000000),(-10646953/100000000000000)⟩
def e273 : ℝ := (6574433/50000000000000)
theorem h273 : Model (fun x => f273 ((57/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(40789748002751/20000000000000),(252886272263/100000000000000),(210414733/20000000000000),(-3840367/50000000000000)⟩
def e274 : ℝ := (3147933/50000000000000)
theorem h274 : Model (fun x => f274 ((57/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(207975442765991/50000000000000),(128939591487/12500000000000),(2465448317/50000000000000),(-26008421/100000000000000)⟩
def e275 : ℝ := (12870299/50000000000000)
theorem h275 : Model (fun x => f275 ((57/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(848326590118533/100000000000000),(3155648066599/100000000000000),(17041175493/100000000000000),(-15417513/25000000000000)⟩
def e276 : ℝ := (3945487/5000000000000)
theorem h276 : Model (fun x => f276 ((57/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1730151391748399/100000000000000),(8581205961463/100000000000000),(5166048411/10000000000000),(-28659617/25000000000000)⟩
def e277 : ℝ := (214966083/100000000000000)
theorem h277 : Model (fun x => f277 ((57/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1869487499167163/100000000000000),(18368455649531/100000000000000),(149843146353/100000000000000),(206091997/100000000000000)⟩
def e278 : ℝ := (231054843/50000000000000)
theorem h278 : Model (fun x => f278 ((57/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(20789748002751/2500000000000),(252886272263/12500000000000),(210414733/2500000000000),(-3840367/6250000000000)⟩
def e279 : ℝ := (3147933/6250000000000)
theorem h279 : Model (fun x => f279 ((57/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(58727707850907/6250000000000),(1274417182737/50000000000000),(87838583/781250000000),(-2883713/4000000000000)⟩
def e280 : ℝ := (31757897/50000000000000)
theorem h280 : Model (fun x => f280 ((57/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(64977707850907/6250000000000),(1274417182737/50000000000000),(87838583/781250000000),(-2883713/4000000000000)⟩
def e281 : ℝ := (31757897/50000000000000)
theorem h281 : Model (fun x => f281 ((57/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(3887200401657813/20000000000000),(238616563015823/100000000000000),(34940759219/1562500000000),(6679336617/100000000000000)⟩
def e282 : ℝ := (6024248489/100000000000000)
theorem h282 : Model (fun x => f282 ((57/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(514509105099/100000000000000),(-6316648571/100000000000000),(9176457/50000000000000),(324627/100000000000000)⟩
def e283 : ℝ := (83743/50000000000000)
theorem h283 : Model (fun x => f283 ((57/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (479878413327453/2500000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(1936385358131/50000000000000),(121639893001/50000000000000),(716182867/100000000000000),(-9371269/100000000000000)⟩
def e284 : ℝ := (4467761/50000000000000)
theorem h284 : Model (fun x => f284 ((57/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(10789748002751/5000000000000),(252886272263/25000000000000),(2104147331/50000000000000),(-3840367/12500000000000)⟩
def e285 : ℝ := (12591731/50000000000000)
theorem h285 : Model (fun x => f285 ((57/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(12025157782909/25000000000000),(-58509556243/50000000000000),(-157927/78125000000),(5230279/100000000000000)⟩
def e286 : ℝ := (2947007/100000000000000)
theorem h286 : Model (fun x => f286 ((57/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (103694787691227/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(51899368868363/50000000000000),(234038224969/100000000000000),(202146559/50000000000000),(-10460561/100000000000000)⟩
def e287 : ℝ := (72707/390625000000)
theorem h287 : Model (fun x => f287 ((57/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(1899368868363/50000000000000),(234038224969/100000000000000),(202146559/50000000000000),(-10460561/100000000000000)⟩
def e288 : ℝ := (72707/390625000000)
theorem h288 : Model (fun x => f288 ((57/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(383066770218869/100000000000000),(863712496909/100000000000000),(11936273/800000000000),(-9651113/25000000000000)⟩
def e289 : ℝ := (68690807/100000000000000)
theorem h289 : Model (fun x => f289 ((57/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1369390527966577/50000000000000),(863712496909/100000000000000),(11936273/800000000000),(-9651113/25000000000000)⟩
def e290 : ℝ := (8586351/12500000000000)
theorem h290 : Model (fun x => f290 ((57/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(2842820165431189/100000000000000),(7306317238559/100000000000000),(14642833311/100000000000000),(-319578937/100000000000000)⟩
def e291 : ℝ := (581566383/100000000000000)
theorem h291 : Model (fun x => f291 ((57/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8125201117812141/100000000000000),(7306317238559/100000000000000),(14642833311/100000000000000),(-319578937/100000000000000)⟩
def e292 : ℝ := (36347899/6250000000000)
theorem h292 : Model (fun x => f292 ((57/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(8433856198859353/100000000000000),(26599941539953/100000000000000),(8143535033/12500000000000),(-558925879/50000000000000)⟩
def e293 : ℝ := (530045949/25000000000000)
theorem h293 : Model (fun x => f293 ((57/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(3425725954476743/25000000000000),(26599941539953/100000000000000),(8143535033/12500000000000),(-558925879/50000000000000)⟩
def e294 : ℝ := (2120183797/100000000000000)
theorem h294 : Model (fun x => f294 ((57/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(14223441196265071/100000000000000),(59680436421817/100000000000000),(23159627587/12500000000000),(-291712877/12500000000000)⟩
def e295 : ℝ := (953265157/20000000000000)
theorem h295 : Model (fun x => f295 ((57/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(4139788870494839/25000000000000),(59680436421817/100000000000000),(23159627587/12500000000000),(-291712877/12500000000000)⟩
def e296 : ℝ := (2383162893/50000000000000)
theorem h296 : Model (fun x => f296 ((57/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(17188194370156437/100000000000000),(12587786655187/12500000000000),(199468884433/50000000000000),(-1739815943/50000000000000)⟩
def e297 : ℝ := (8062843869/100000000000000)
theorem h297 : Model (fun x => f297 ((57/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(17590575322537389/100000000000000),(12587786655187/12500000000000),(199468884433/50000000000000),(-1739815943/50000000000000)⟩
def e298 : ℝ := (806284387/10000000000000)
theorem h298 : Model (fun x => f298 ((57/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(4564698786355457/25000000000000),(14569637950331/10000000000000),(720891713489/100000000000000),(-1027771881/25000000000000)⟩
def e299 : ℝ := (11698107211/100000000000000)
theorem h299 : Model (fun x => f299 ((57/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(912058804890139/5000000000000),(14569637950331/10000000000000),(720891713489/100000000000000),(-1027771881/25000000000000)⟩
def e300 : ℝ := (2924526803/25000000000000)
theorem h300 : Model (fun x => f300 ((57/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(18934110537852657/100000000000000),(3030036368833/1562500000000),(1163009539089/100000000000000),(-779836741/20000000000000)⟩
def e301 : ℝ := (7807219267/50000000000000)
theorem h301 : Model (fun x => f301 ((57/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(1893744387118599/10000000000000),(3030036368833/1562500000000),(1163009539089/100000000000000),(-779836741/20000000000000)⟩
def e302 : ℝ := (3122887707/20000000000000)
theorem h302 : Model (fun x => f302 ((57/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(719383826706047/100000000000000),(6460932266163/12500000000000),(114918967577/20000000000000),(11014551/800000000000)⟩
def e303 : ℝ := (131742083/3125000000000)
theorem h303 : Model (fun x => f303 ((57/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(105216581599/97656250000),(242928723339/50000000000000),(1387041213/100000000000000),(-991173/5000000000000)⟩
def e304 : ℝ := (96937/250000000000)
theorem h304 : Model (fun x => f304 ((57/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(101899368868363/50000000000000),(234038224969/100000000000000),(202146559/50000000000000),(-10460561/100000000000000)⟩
def e305 : ℝ := (72707/390625000000)
theorem h305 : Model (fun x => f305 ((57/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(103834813757707/25000000000000),(119241737077/12500000000000),(2195627449/100000000000000),(-20372291/50000000000000)⟩
def e306 : ℝ := (4750049/6250000000000)
theorem h306 : Model (fun x => f306 ((57/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(211614039769487/25000000000000),(2916157860219/100000000000000),(8386419009/100000000000000),(-7343029/6250000000000)⟩
def e307 : ℝ := (232738543/100000000000000)
theorem h307 : Model (fun x => f307 ((57/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1725066967695631/100000000000000),(7924123879383/100000000000000),(27338504173/100000000000000),(-148283409/50000000000000)⟩
def e308 : ℝ := (316753289/50000000000000)
theorem h308 : Model (fun x => f308 ((57/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1858617849551737/100000000000000),(16918958404709/100000000000000),(45941163323/50000000000000),(-209378653/50000000000000)⟩
def e309 : ℝ := (1360255029/100000000000000)
theorem h309 : Model (fun x => f309 ((57/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(51899368868363/6250000000000),(234038224969/12500000000000),(202146559/6250000000000),(-10460561/12500000000000)⟩
def e310 : ℝ := (72707/48828125000)
theorem h310 : Model (fun x => f310 ((57/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(58633230090699/6250000000000),(235816324643/10000000000000),(4621386157/100000000000000),(-25876987/25000000000000)⟩
def e311 : ℝ := (11729921/6250000000000)
theorem h311 : Model (fun x => f311 ((57/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(64883230090699/6250000000000),(235816324643/10000000000000),(4621386157/100000000000000),(-25876987/25000000000000)⟩
def e312 : ℝ := (11729921/6250000000000)
theorem h312 : Model (fun x => f312 ((57/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(4823725183325821/25000000000000),(54867577597637/25000000000000),(287746021871/20000000000000),(-3322443801/100000000000000)⟩
def e313 : ℝ := (17696795371/100000000000000)
theorem h313 : Model (fun x => f313 ((57/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(103654329589/20000000000000),(-589509327/10000000000000),(28408797/100000000000000),(8227/4000000000000)⟩
def e314 : ℝ := (491897/100000000000000)
theorem h314 : Model (fun x => f314 ((57/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (19073970673564209/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(3728362413719/100000000000000),(112736546737/50000000000000),(422833/312500000000),(-10573863/100000000000000)⟩
def e315 : ℝ := (6521109/25000000000000)
theorem h315 : Model (fun x => f315 ((57/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(7601133129981/100000000000000),(117188219869/25000000000000),(851489427/100000000000000),(-4986283/25000000000000)⟩
def e316 : ℝ := (17509979/50000000000000)
theorem h316 : Model (fun x => f316 ((57/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(36759754178103/100000000000000),(2171226920803/100000000000000),(-928309363/50000000000000),(-57987077/50000000000000)⟩
def e317 : ℝ := (170589409/100000000000000)
theorem h317 : Model (fun x => f317 ((57/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(1031852748859/4000000000000),(267775254871/25000000000000),(-20094136291/100000000000000),(54228667/20000000000000)⟩
def e318 : ℝ := (16462893/12500000000000)
theorem h318 : Model (fun x => f318 ((57/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-33765226654297/50000000000000),(-239760355829/10000000000000),(15255518413/25000000000000),(-635157119/50000000000000)⟩
def e319 : ℝ := (238652409/100000000000000)
theorem h319 : Model (fun x => f319 ((57/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((57/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-35739/1600),(-627/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((57/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((57/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(5529/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((57/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(185421/1600),(1313/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((57/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((57/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(358221/1600),(1313/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((57/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1791105/32),(6565/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((57/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((57/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(916410553630611233/100000000000000),(5764451587911587/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (119061/100000000000000)
theorem h329 : Model (fun x => f329 ((57/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10912139717/100000000000000),(-68640089/100000000000000),(39061/4000000000000),(-957/10000000000000)⟩
def e330 : ℝ := (57/50000000000000)
theorem h330 : Model (fun x => f330 ((57/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (227650088106700877/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(61077462524429/10000000000000),(3971638257/625000000000),(193474029/2500000000000),(-16996773/100000000000000)⟩
def e331 : ℝ := (12049327/100000000000000)
theorem h331 : Model (fun x => f331 ((57/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((57/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(417/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((57/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((57/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((57/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(535806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((57/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((57/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((57/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2377101792213689/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (41/4000000000000)
theorem h339 : Model (fun x => f339 ((57/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3634193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((57/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((57/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((57/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(511974551946513/25000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1/97656250000)
theorem h343 : Model (fun x => f343 ((57/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4883055203613/100000000000000),(-1679552637/25000000000000),(577691/6250000000000),(-12717/100000000000000)⟩
def e344 : ℝ := (11/50000000000000)
theorem h344 : Model (fun x => f344 ((57/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2045080666150547/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(29018798189967/25000000000000),(184696596833/20000000000000),(-79409213/6250000000000),(1748041/100000000000000)⟩
def e345 : ℝ := (17/500000000000)
theorem h345 : Model (fun x => f345 ((57/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(54018798189967/25000000000000),(184696596833/20000000000000),(-79409213/6250000000000),(1748041/100000000000000)⟩
def e346 : ℝ := (17/500000000000)
theorem h346 : Model (fun x => f346 ((57/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(54018798189967/50000000000000),(230870746041/50000000000000),(-79409213/12500000000000),(43701/5000000000000)⟩
def e347 : ℝ := (1701/100000000000000)
theorem h347 : Model (fun x => f347 ((57/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(4018798189967/50000000000000),(230870746041/50000000000000),(-79409213/12500000000000),(43701/5000000000000)⟩
def e348 : ℝ := (1701/100000000000000)
theorem h348 : Model (fun x => f348 ((57/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(398710177116423/100000000000000),(1704045982683/100000000000000),(-29305781/1250000000000),(64511/2000000000000)⟩
def e349 : ℝ := (157/2500000000000)
theorem h349 : Model (fun x => f349 ((57/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(688606115707677/25000000000000),(1704045982683/100000000000000),(-29305781/1250000000000),(64511/2000000000000)⟩
def e350 : ℝ := (6281/100000000000000)
theorem h350 : Model (fun x => f350 ((57/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(595162796748641/20000000000000),(2911866186769/20000000000000),(-97301983/800000000000),(1181663/20000000000000)⟩
def e351 : ℝ := (49211/50000000000000)
theorem h351 : Model (fun x => f351 ((57/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8258194936124157/100000000000000),(2911866186769/20000000000000),(-97301983/800000000000),(1181663/20000000000000)⟩
def e352 : ℝ := (98423/100000000000000)
theorem h352 : Model (fun x => f352 ((57/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1784391062671593/20000000000000),(26930531853513/50000000000000),(811995289/50000000000000),(-35045289/50000000000000)⟩
def e353 : ℝ := (239727/50000000000000)
theorem h353 : Model (fun x => f353 ((57/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(886937683275349/6250000000000),(26930531853513/50000000000000),(811995289/50000000000000),(-35045289/50000000000000)⟩
def e354 : ℝ := (95891/20000000000000)
theorem h354 : Model (fun x => f354 ((57/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(15331618470376943/100000000000000),(4948637891809/4000000000000),(80150844817/50000000000000),(-286358509/100000000000000)⟩
def e355 : ℝ := (899779/100000000000000)
theorem h355 : Model (fun x => f355 ((57/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(4416833189022807/25000000000000),(4948637891809/4000000000000),(80150844817/50000000000000),(-286358509/100000000000000)⟩
def e356 : ℝ := (44989/5000000000000)
theorem h356 : Model (fun x => f356 ((57/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(1908736165412571/10000000000000),(107618570837747/50000000000000),(632198034223/100000000000000),(-25089287/12500000000000)⟩
def e357 : ℝ := (2541403/100000000000000)
theorem h357 : Model (fun x => f357 ((57/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(9744871303253331/50000000000000),(107618570837747/50000000000000),(632198034223/100000000000000),(-25089287/12500000000000)⟩
def e358 : ℝ := (635351/25000000000000)
theorem h358 : Model (fun x => f358 ((57/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(4211249890541139/20000000000000),(161264631348651/50000000000000),(776518770133/50000000000000),(1505273021/100000000000000)⟩
def e359 : ℝ := (6161173/100000000000000)
theorem h359 : Model (fun x => f359 ((57/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(21038630405086647/100000000000000),(161264631348651/50000000000000),(776518770133/50000000000000),(1505273021/100000000000000)⟩
def e360 : ℝ := (3080587/50000000000000)
theorem h360 : Model (fun x => f360 ((57/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(4545926120182717/20000000000000),(55699618623269/12500000000000),(606692594543/20000000000000),(1386443549/20000000000000)⟩
def e361 : ℝ := (3574439/50000000000000)
theorem h361 : Model (fun x => f361 ((57/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(11366481967123459/50000000000000),(55699618623269/12500000000000),(606692594543/20000000000000),(1386443549/20000000000000)⟩
def e362 : ℝ := (7148879/100000000000000)
theorem h362 : Model (fun x => f362 ((57/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(456795971557683/25000000000000),(140782811105261/100000000000000),(539226742247/25000000000000),(11931871283/100000000000000)⟩
def e363 : ℝ := (17652299/100000000000000)
theorem h363 : Model (fun x => f363 ((57/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(23344244463107/20000000000000),(249427204767/25000000000000),(379691587/50000000000000),(-795621/20000000000000)⟩
def e364 : ℝ := (3953/25000000000000)
theorem h364 : Model (fun x => f364 ((57/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(104018798189967/50000000000000),(230870746041/50000000000000),(-79409213/12500000000000),(43701/5000000000000)⟩
def e365 : ℝ := (1701/100000000000000)
theorem h365 : Model (fun x => f365 ((57/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(432796415075403/100000000000000),(60037243851/3125000000000),(-255582117/50000000000000),(-446013/20000000000000)⟩
def e366 : ℝ := (9607/50000000000000)
theorem h366 : Model (fun x => f366 ((57/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(90037925914139/10000000000000),(2997600936969/50000000000000),(1011616819/20000000000000),(-15421731/100000000000000)⟩
def e367 : ℝ := (5721/10000000000000)
theorem h367 : Model (fun x => f367 ((57/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(468281842255301/25000000000000),(16629698502221/100000000000000),(3248517849/10000000000000),(-9736043/25000000000000)⟩
def e368 : ℝ := (46447/25000000000000)
theorem h368 : Model (fun x => f368 ((57/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2186337160648371/100000000000000),(38098744312281/100000000000000),(218057280013/100000000000000),(66083907/20000000000000)⟩
def e369 : ℝ := (52901/4000000000000)
theorem h369 : Model (fun x => f369 ((57/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(54018798189967/6250000000000),(230870746041/6250000000000),(-79409213/1562500000000),(43701/625000000000)⟩
def e370 : ℝ := (1701/12500000000000)
theorem h370 : Model (fun x => f370 ((57/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(981021993355007/100000000000000),(1172910188931/25000000000000),(-2161403229/50000000000000),(602811/20000000000000)⟩
def e371 : ℝ := (1471/5000000000000)
theorem h371 : Model (fun x => f371 ((57/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1081021993355007/100000000000000),(1172910188931/25000000000000),(-2161403229/50000000000000),(602811/20000000000000)⟩
def e372 : ℝ := (1471/5000000000000)
theorem h372 : Model (fun x => f372 ((57/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(23634785555502281/100000000000000),(102886178098873/20000000000000),(1012548061663/25000000000000),(1527666811/12500000000000)⟩
def e373 : ℝ := (22245329/100000000000000)
theorem h373 : Model (fun x => f373 ((57/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(105776292919/25000000000000),(-9209238211/100000000000000),(127941051/100000000000000),(-1425381/100000000000000)⟩
def e374 : ℝ := (591/4000000000000)
theorem h374 : Model (fun x => f374 ((57/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (23116292229181447/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(483181844917/6250000000000),(427389637981/100000000000000),(-750660617/50000000000000),(5924339/100000000000000)⟩
def e375 : ℝ := (91129/12500000000000)
theorem h375 : Model (fun x => f375 ((57/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(29018798189967/12500000000000),(184696596833/10000000000000),(-79409213/3125000000000),(1748041/50000000000000)⟩
def e376 : ℝ := (17/250000000000)
theorem h376 : Model (fun x => f376 ((57/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(23140092743347/50000000000000),(-98898358611/50000000000000),(1117495577/100000000000000),(-3156767/50000000000000)⟩
def e377 : ℝ := (3609/10000000000000)
theorem h377 : Model (fun x => f377 ((57/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (107575218738427/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(107439629026609/100000000000000),(197796717221/50000000000000),(-1117495579/50000000000000),(1578383/12500000000000)⟩
def e378 : ℝ := (119867/50000000000000)
theorem h378 : Model (fun x => f378 ((57/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(7439629026609/100000000000000),(197796717221/50000000000000),(-1117495579/50000000000000),(1578383/12500000000000)⟩
def e379 : ℝ := (119867/50000000000000)
theorem h379 : Model (fun x => f379 ((57/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(79300678567259/20000000000000),(364982037729/25000000000000),(-1649636331/20000000000000),(46599879/100000000000000)⟩
def e380 : ℝ := (176947/20000000000000)
theorem h380 : Model (fun x => f380 ((57/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(137610883927529/5000000000000),(364982037729/25000000000000),(-1649636331/20000000000000),(46599879/100000000000000)⟩
def e381 : ℝ := (54/6103515625)
theorem h381 : Model (fun x => f381 ((57/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(2956972463839493/100000000000000),(12456133827297/100000000000000),(-8074782203/12500000000000),(166166247/50000000000000)⟩
def e382 : ℝ := (1013841/12500000000000)
theorem h382 : Model (fun x => f382 ((57/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(1647870683244089/20000000000000),(12456133827297/100000000000000),(-8074782203/12500000000000),(166166247/50000000000000)⟩
def e383 : ℝ := (8110729/100000000000000)
theorem h383 : Model (fun x => f383 ((57/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(8852330744578481/100000000000000),(22988582565073/50000000000000),(-12767331317/6250000000000),(107938159/12500000000000)⟩
def e384 : ℝ := (32875877/100000000000000)
theorem h384 : Model (fun x => f384 ((57/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(141213783636261/1000000000000),(22988582565073/50000000000000),(-12767331317/6250000000000),(107938159/12500000000000)⟩
def e385 : ℝ := (16437939/50000000000000)
theorem h385 : Model (fun x => f385 ((57/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1517195652732371/10000000000000),(52630470655999/50000000000000),(-14128147427/4000000000000),(437584589/50000000000000)⟩
def e386 : ℝ := (16649859/20000000000000)
theorem h386 : Model (fun x => f386 ((57/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3501534162607599/20000000000000),(52630470655999/50000000000000),(-14128147427/4000000000000),(437584589/50000000000000)⟩
def e387 : ℝ := (5203081/6250000000000)
theorem h387 : Model (fun x => f387 ((57/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(18810176572727921/100000000000000),(182351161115623/100000000000000),(-354370251379/100000000000000),(-299420003/50000000000000)⟩
def e388 : ℝ := (19588849/12500000000000)
theorem h388 : Model (fun x => f388 ((57/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(19212557525108873/100000000000000),(182351161115623/100000000000000),(-354370251379/100000000000000),(-299420003/50000000000000)⟩
def e389 : ℝ := (156710793/100000000000000)
theorem h389 : Model (fun x => f389 ((57/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(2580237566437603/12500000000000),(135960513593031/50000000000000),(-22190956093/25000000000000),(-1847403661/50000000000000)⟩
def e390 : ℝ := (122049103/50000000000000)
theorem h390 : Model (fun x => f390 ((57/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(1289017592742611/6250000000000),(135960513593031/50000000000000),(-22190956093/25000000000000),(-1847403661/50000000000000)⟩
def e391 : ℝ := (244098207/100000000000000)
theorem h391 : Model (fun x => f391 ((57/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(22158651515686189/100000000000000),(373739246305123/100000000000000),(259691669617/50000000000000),(-3897000417/50000000000000)⟩
def e392 : ℝ := (67019957/20000000000000)
theorem h392 : Model (fun x => f392 ((57/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(11080992424509761/50000000000000),(373739246305123/100000000000000),(259691669617/50000000000000),(-3897000417/50000000000000)⟩
def e393 : ℝ := (167549893/50000000000000)
theorem h393 : Model (fun x => f393 ((57/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(329753891540069/20000000000000),(115476170456697/100000000000000),(127726214021/12500000000000),(-2039914729/50000000000000)⟩
def e394 : ℝ := (42641367/50000000000000)
theorem h394 : Model (fun x => f394 ((57/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(115432738853753/100000000000000),(212512059209/25000000000000),(-647518153/20000000000000),(18457/195312500000)⟩
def e395 : ℝ := (667471/100000000000000)
theorem h395 : Model (fun x => f395 ((57/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(207439629026609/100000000000000),(197796717221/50000000000000),(-1117495579/50000000000000),(1578383/12500000000000)⟩
def e396 : ℝ := (119867/50000000000000)
theorem h396 : Model (fun x => f396 ((57/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(430311996906971/100000000000000),(41030877643/2500000000000),(-7707573081/100000000000000),(2169007/6250000000000)⟩
def e397 : ℝ := (1146939/100000000000000)
theorem h397 : Model (fun x => f397 ((57/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(892637610040813/100000000000000),(255342901107/5000000000000),(-19113377767/100000000000000),(59153739/100000000000000)⟩
def e398 : ℝ := (3937873/100000000000000)
theorem h398 : Model (fun x => f398 ((57/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1851684146820651/100000000000000),(3531215778681/25000000000000),(-787933931/2000000000000),(22836563/50000000000000)⟩
def e399 : ℝ := (5823201/50000000000000)
theorem h399 : Model (fun x => f399 ((57/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1068724862797913/50000000000000),(3204492479449/10000000000000),(7320754541/50000000000000),(-564490593/100000000000000)⟩
def e400 : ℝ := (29000889/100000000000000)
theorem h400 : Model (fun x => f400 ((57/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(107439629026609/12500000000000),(197796717221/6250000000000),(-1117495579/6250000000000),(1578383/1562500000000)⟩
def e401 : ℝ := (119867/6250000000000)
theorem h401 : Model (fun x => f401 ((57/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(7799598168533/800000000000),(1003698928093/25000000000000),(-21117520029/100000000000000),(1726039/1562500000000)⟩
def e402 : ℝ := (2585343/100000000000000)
theorem h402 : Model (fun x => f402 ((57/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(8599598168533/800000000000),(1003698928093/25000000000000),(-21117520029/100000000000000),(1726039/1562500000000)⟩
def e403 : ℝ := (2585343/100000000000000)
theorem h403 : Model (fun x => f403 ((57/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(4595302186391307/20000000000000),(43028108565417/10000000000000),(992550761127/100000000000000),(-1977218251/20000000000000)⟩
def e404 : ℝ := (378784589/100000000000000)
theorem h404 : Model (fun x => f404 ((57/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(21761354519/5000000000000),(-8150497067/100000000000000),(133833189/100000000000000),(-98347/5000000000000)⟩
def e405 : ℝ := (35673/100000000000000)
theorem h405 : Model (fun x => f405 ((57/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (11272613515332697/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(7175891337823/100000000000000),(368200670469/100000000000000),(-2758088463/100000000000000),(21076041/100000000000000)⟩
def e406 : ℝ := (401227/25000000000000)
theorem h406 : Model (fun x => f406 ((57/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2981360171299/20000000000000),(15911806169/2000000000000),(-4259409697/100000000000000),(1350019/5000000000000)⟩
def e407 : ℝ := (116697/5000000000000)
theorem h407 : Model (fun x => f407 ((57/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(91046957067169/100000000000000),(4953990797829/100000000000000),(-19806087037/100000000000000),(49220321/25000000000000)⟩
def e408 : ℝ := (16458777/100000000000000)
theorem h408 : Model (fun x => f408 ((57/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(15973150362661/25000000000000),(1177780968969/50000000000000),(-27612328241/50000000000000),(553507963/50000000000000)⟩
def e409 : ℝ := (1096151/2500000000000)
theorem h409 : Model (fun x => f409 ((57/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-72757037159/2000000000000),(-328450159/781250000000),(579741717/10000000000000),(-20412289/12500000000000)⟩
def e410 : ℝ := (282498449/100000000000000)
theorem h410 : Model (fun x => f410 ((57/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(499966844238281/50000000000000),(20119844970703/25000000000000),(263169/10240000),(4161/10240000)⟩
def e411 : ℝ := (19897461/6250000000000)
theorem h411 : Model (fun x => f411 ((57/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(31329/1600),(177/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((57/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(5545233/64000),(93987/64000),(531/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((57/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(86638520111749239/100000000000000),(4220763130660561/50000000000000),(87290168860519/25000000000000),(7978300555297/100000000000000)⟩
def e414 : ℝ := (110686717423/100000000000000)
theorem h414 : Model (fun x => f414 ((57/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(57711050391/50000000000000),(-702876369/6250000000000),(630582453/100000000000000),(-6686639/25000000000000)⟩
def e415 : ℝ := (731927/50000000000000)
theorem h415 : Model (fun x => f415 ((57/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (77839744187713321/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(4524609727917/100000000000000),(61167418147/50000000000000),(-5059789969/100000000000000),(129179227/100000000000000)⟩
def e416 : ℝ := (60747421/50000000000000)
theorem h416 : Model (fun x => f416 ((57/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(886757869967/100000000000000),(40146607971/50000000000000),(737627201/100000000000000),(-6823817/20000000000000)⟩
def e417 : ℝ := (403993291/100000000000000)
theorem h417 : Model (fun x => f417 ((57/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((57/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((2659799257229/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (7/5) (29/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (7/5) (29/20) ≤ (106488928679/240000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(57/40)-(1/40)) (by norm_num : ((57/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel8


noncomputable section
namespace Hf4Quad.Panel9
open Hf4Quad.Dag

def p0 : Cubic := ⟨(59/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((59/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((59/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((59/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((59/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(25847619047619/10000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((59/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-25847619047619/10000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((59/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-167047619047619/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((59/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((59/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(3481/1600),(59/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((59/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(2057634755291/781250000000),(4464021164021/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((59/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-2057634755291/781250000000),(-4464021164021/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((59/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-430424867724867/100000000000000),(-6654497354497/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((59/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((59/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(205379/64000),(10443/64000),(177/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((59/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(156322181568287/5000000000000),(39742927517361/25000000000000),(168402235243/6250000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((59/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-156322181568287/5000000000000),(-39742927517361/25000000000000),(-168402235243/6250000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((59/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-3556868499090607/100000000000000),(-86140352389219/50000000000000),(-2770097139549/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((59/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((59/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(12117361/2560000),(205379/640000),(10443/1280000),(59/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((59/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(41322845672123/3125000000000),(89649563492063/100000000000000),(569806547619/25000000000000),(25753968253/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((59/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2234537437582671/100000000000000),(-661049130291/800000000000),(-490870949073/100000000000000),(329098979/3125000000000)⟩
def e20 : ℝ := (54563497/50000000000000)
theorem h20 : Model (fun x => f20 ((59/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((59/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(698168260742187/100000000000000),(14791700439453/25000000000000),(205379/10240000),(3481/10240000)⟩
def e22 : ℝ := (289062501/100000000000000)
theorem h22 : Model (fun x => f22 ((59/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(1137109232079173/25000000000000),(96365189159251/25000000000000),(6533233163339/50000000000000),(2768319137/1250000000000)⟩
def e23 : ℝ := (941594333/50000000000000)
theorem h23 : Model (fun x => f23 ((59/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(2313899490734021/100000000000000),(302829615350629/100000000000000),(2515119075521/20000000000000),(14499793643/6250000000000)⟩
def e24 : ℝ := (99615783/5000000000000)
theorem h24 : Model (fun x => f24 ((59/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((59/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(41191927383789/4000000000000),(104725239111327/100000000000000),(887502026367/20000000000000),(100282714843/100000000000000)⟩
def e26 : ℝ := (128344727/10000000000000)
theorem h26 : Model (fun x => f26 ((59/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(578103636960319/25000000000000),(235160801475381/100000000000000),(15569438657/156250000000),(112592550739/50000000000000)⟩
def e27 : ℝ := (2881984243/100000000000000)
theorem h27 : Model (fun x => f27 ((59/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(4626314038575297/100000000000000),(53799041682601/10000000000000),(4508007223617/20000000000000),(228590899883/50000000000000)⟩
def e28 : ℝ := (4874299903/100000000000000)
theorem h28 : Model (fun x => f28 ((59/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((59/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(1518952322277219/100000000000000),(7208587292163/4000000000000),(9163458422239/100000000000000),(258854757689/100000000000000)⟩
def e30 : ℝ := (2216119389/50000000000000)
theorem h30 : Model (fun x => f30 ((59/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(45056224638977/12500000000000),(2672826885363/6250000000000),(2174503228769/100000000000000),(767833061/1250000000000)⟩
def e31 : ℝ := (1051777299/100000000000000)
theorem h31 : Model (fun x => f31 ((59/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(4986763835687113/100000000000000),(290377823495909/50000000000000),(12357269673427/50000000000000),(259304222323/50000000000000)⟩
def e32 : ℝ := (2963038601/50000000000000)
theorem h32 : Model (fun x => f32 ((59/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((59/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1493349/320),(25311/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((59/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((59/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(130331/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((59/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(715729/64),(42983/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((59/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((59/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(861649/64),(42983/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((59/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-861649/64),(-42983/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((59/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((59/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(99/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((59/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(9801/1600),(99/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((59/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((59/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(205821/160),(2079/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((59/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(38868725737/50000000000000),(-785226783/50000000000000),(95179/400000000000),(-320469/100000000000000)⟩
def e46 : ℝ := (521/12500000000000)
theorem h46 : Model (fun x => f46 ((59/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (100821/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-104659995820501/10000000000000),(32469128921/12500000000000),(-1339637721/50000000000000),(27637713/100000000000000)⟩
def e47 : ℝ := (111861973/100000000000000)
theorem h47 : Model (fun x => f47 ((59/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((59/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(139/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((59/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((59/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((59/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(28958333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/25000000000000)
theorem h52 : Model (fun x => f52 ((59/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(53958333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/25000000000000)
theorem h53 : Model (fun x => f53 ((59/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((59/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(53958333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((59/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((59/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1133124999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((59/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((59/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(3958333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((59/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(179411458333317/100000000000000),(202708333333/2000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (3/4000000000000)
theorem h60 : Model (fun x => f60 ((59/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(116460069444443/100000000000000),(449652777777/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (7/100000000000000)
theorem h61 : Model (fun x => f61 ((59/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((59/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(53958333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((59/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1195626736111103/100000000000000),(2532986111107/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (37/100000000000000)
theorem h64 : Model (fun x => f64 ((59/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1295626736111103/100000000000000),(2532986111107/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (37/100000000000000)
theorem h65 : Model (fun x => f65 ((59/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1162251410906643/50000000000000),(140406102792013/100000000000000),(988936089403/100000000000000),(1011465567/50000000000000)⟩
def e66 : ℝ := (126801/20000000000000)
theorem h66 : Model (fun x => f66 ((59/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(103958333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((59/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(17291736111111/4000000000000),(866319444443/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (13/100000000000000)
theorem h68 : Model (fun x => f68 ((59/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(449405016637727/50000000000000),(5403667534713/100000000000000),(2165798611/20000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (21/50000000000000)
theorem h69 : Model (fun x => f69 ((59/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(20892864586228863/100000000000000),(86724533971967/6250000000000),(16727456036701/100000000000000),(86993843313/100000000000000)⟩
def e70 : ℝ := (232585597/100000000000000)
theorem h70 : Model (fun x => f70 ((59/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((59/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2445661458333303/12500000000000),(9442708333317/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (147/12500000000000)
theorem h72 : Model (fun x => f72 ((59/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1548918923610961/100000000000000),(46741406249923/50000000000000),(652604166663/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (173/25000000000000)
theorem h73 : Model (fun x => f73 ((59/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(6960919346358741/50000000000000),(923931327150887/100000000000000),(2771226109949/25000000000000),(7052861373/12500000000000)⟩
def e74 : ℝ := (28657647/20000000000000)
theorem h74 : Model (fun x => f74 ((59/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(6962940655789269/20000000000000),(2311523870702359/100000000000000),(27812360476497/100000000000000),(143416734297/100000000000000)⟩
def e75 : ℝ := (46984229/12500000000000)
theorem h75 : Model (fun x => f75 ((59/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((59/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(815220486111101/12500000000000),(3147569444439/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (49/12500000000000)
theorem h77 : Model (fun x => f77 ((59/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(626736111111/100000000000000),(32986111111/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/100000000000000)
theorem h78 : Model (fun x => f78 ((59/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(12404152199/25000000000000),(1958550347/25000000000000),(103081597/25000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((59/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(808969518837/25000000000000),(53591559259/10000000000000),(3860572839/12500000000000),(68703983/10000000000000)⟩
def e80 : ℝ := (2025563/50000000000000)
theorem h80 : Model (fun x => f80 ((59/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(6727929831661/100000000000000),(1127740661573/100000000000000),(16611794131/25000000000000),(778578037/50000000000000)⟩
def e81 : ℝ := (5651257/50000000000000)
theorem h81 : Model (fun x => f81 ((59/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(17410715604389003/50000000000000),(578162902840983/25000000000000),(27878807653021/100000000000000),(144973890371/100000000000000)⟩
def e82 : ℝ := (193588173/50000000000000)
theorem h82 : Model (fun x => f82 ((59/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(3927981529/100000000000000),(826943479/100000000000000),(65285011/100000000000000),(1145351/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((59/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(77741301/25000000000000),(20458237/25000000000000),(4306997/50000000000000),(56671/12500000000000)⟩
def e84 : ℝ := (12059/100000000000000)
theorem h84 : Model (fun x => f84 ((59/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(12309039/50000000000000),(777413/10000000000000),(1022911/100000000000000),(71783/100000000000000)⟩
def e85 : ℝ := (181/6250000000000)
theorem h85 : Model (fun x => f85 ((59/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1948931/100000000000000),(718027/100000000000000),(28343/25000000000000),(1243/12500000000000)⟩
def e86 : ℝ := (543/100000000000000)
theorem h86 : Model (fun x => f86 ((59/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(5846793/100000000000000),(2154081/100000000000000),(85029/25000000000000),(3729/12500000000000)⟩
def e87 : ℝ := (1629/100000000000000)
theorem h87 : Model (fun x => f87 ((59/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-5846793/100000000000000),(-2154081/100000000000000),(-85029/25000000000000),(-3729/12500000000000)⟩
def e88 : ℝ := (1629/100000000000000)
theorem h88 : Model (fun x => f88 ((59/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(34821431202931213/100000000000000),(2312651609209851/100000000000000),(5575761462581/20000000000000),(144973860539/100000000000000)⟩
def e89 : ℝ := (15487119/4000000000000)
theorem h89 : Model (fun x => f89 ((59/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2445661458333303/10000000000000),(9442708333317/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (147/10000000000000)
theorem h90 : Model (fun x => f90 ((59/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2990041377363/160000000000),(936260451327/6250000000000),(11257640697/25000000000000),(60161071/100000000000000)⟩
def e91 : ℝ := (15129/50000000000000)
theorem h91 : Model (fun x => f91 ((59/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(457039309714907033/100000000000000),(7192902840109029/100000000000000),(9223373296447/20000000000000),(4824082761/3125000000000)⟩
def e92 : ℝ := (35686873/12500000000000)
theorem h92 : Model (fun x => f92 ((59/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(5469989007/25000000000000),(-344347619/100000000000000),(401449/12500000000000),(-23189/100000000000000)⟩
def e93 : ℝ := (89/50000000000000)
theorem h93 : Model (fun x => f93 ((59/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (449800135352172433/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(7618913835521/100000000000000),(193050192963/50000000000000),(-745367673/100000000000000),(1199/62500000000)⟩
def e94 : ℝ := (73549/25000000000000)
theorem h94 : Model (fun x => f94 ((59/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(28958333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/12500000000000)
theorem h95 : Model (fun x => f95 ((59/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(23166023166023/50000000000000),(-178888209777/100000000000000),(172672017/25000000000000),(-10667/400000000000)⟩
def e96 : ℝ := (517/5000000000000)
theorem h96 : Model (fun x => f96 ((59/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (42999999999999/20000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(21467181467181/20000000000000),(7155528391/2000000000000),(-1381376139/100000000000000),(666687/12500000000000)⟩
def e97 : ℝ := (68579/100000000000000)
theorem h97 : Model (fun x => f97 ((59/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(450810810810801/20000000000000),(150266096211/2000000000000),(-29008898919/100000000000000),(14000427/12500000000000)⟩
def e98 : ℝ := (1440159/100000000000000)
theorem h98 : Model (fun x => f98 ((59/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1467181467181/20000000000000),(7155528391/2000000000000),(-1381376139/100000000000000),(666687/12500000000000)⟩
def e99 : ℝ := (68579/100000000000000)
theorem h99 : Model (fun x => f99 ((59/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(165355316706611/100000000000000),(4307821484041/50000000000000),(-3192098933/50000000000000),(-79137651/100000000000000)⟩
def e100 : ℝ := (286707/10000000000000)
theorem h100 : Model (fun x => f100 ((59/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(115209970036219/100000000000000),(153609026463/20000000000000),(-842692781/50000000000000),(391259/25000000000000)⟩
def e101 : ℝ := (205109/100000000000000)
theorem h101 : Model (fun x => f101 ((59/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(21467181467181/2000000000000),(7155528391/200000000000),(-1381376139/10000000000000),(666687/1250000000000)⟩
def e102 : ℝ := (68579/10000000000000)
theorem h102 : Model (fun x => f102 ((59/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1188569043395269/100000000000000),(869161865563/20000000000000),(-1937393369/12500000000000),(13724999/25000000000000)⟩
def e103 : ℝ := (890899/100000000000000)
theorem h103 : Model (fun x => f103 ((59/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1288569043395269/100000000000000),(869161865563/20000000000000),(-1937393369/12500000000000),(13724999/25000000000000)⟩
def e104 : ℝ := (890899/100000000000000)
theorem h104 : Model (fun x => f104 ((59/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1065358711344797/50000000000000),(118204534953639/100000000000000),(133262977429/50000000000000),(-1270879721/50000000000000)⟩
def e105 : ℝ := (40908303/100000000000000)
theorem h105 : Model (fun x => f105 ((59/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(41467181467181/20000000000000),(7155528391/2000000000000),(-1381376139/100000000000000),(666687/12500000000000)⟩
def e106 : ℝ := (68579/100000000000000)
theorem h106 : Model (fun x => f106 ((59/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(429881784708029/100000000000000),(296719594283/20000000000000),(-55601723/1250000000000),(3058007/25000000000000)⟩
def e107 : ℝ := (342267/100000000000000)
theorem h107 : Model (fun x => f107 ((59/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(891299298796173/100000000000000),(1153511743219/25000000000000),(-76975841/781250000000),(11880657/100000000000000)⟩
def e108 : ℝ := (1191447/100000000000000)
theorem h108 : Model (fun x => f108 ((59/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(237388368097003/1250000000000),(287967123482303/25000000000000),(1904904778423/25000000000000),(-2718811471/12500000000000)⟩
def e109 : ℝ := (523082363/100000000000000)
theorem h109 : Model (fun x => f109 ((59/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2419409370760599/12500000000000),(3225789555723/2500000000000),(-17696548401/6250000000000),(8216439/3125000000000)⟩
def e110 : ℝ := (4307289/12500000000000)
theorem h110 : Model (fun x => f110 ((59/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(709942518060799/50000000000000),(78714247074081/100000000000000),(17350418669/10000000000000),(-871917949/50000000000000)⟩
def e111 : ℝ := (13883277/50000000000000)
theorem h111 : Model (fun x => f111 ((59/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(1265542537066359/10000000000000),(383546847375729/50000000000000),(629806746547/12500000000000),(-15124182857/100000000000000)⟩
def e112 : ℝ := (71004319/20000000000000)
theorem h112 : Model (fun x => f112 ((59/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(3164649481842383/10000000000000),(191896218868067/10000000000000),(3164518271517/25000000000000),(-294997397/800000000000)⟩
def e113 : ℝ := (439051979/50000000000000)
theorem h113 : Model (fun x => f113 ((59/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(806469790253533/12500000000000),(1075263185241/2500000000000),(-5898849467/6250000000000),(2738813/3125000000000)⟩
def e114 : ℝ := (1435763/12500000000000)
theorem h114 : Model (fun x => f114 ((59/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(538155364409/100000000000000),(10498458643/20000000000000),(269341679/25000000000000),(-2275489/25000000000000)⟩
def e115 : ℝ := (67951/100000000000000)
theorem h115 : Model (fun x => f115 ((59/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(4934822357/12500000000000),(5776178983/100000000000000),(259405721/100000000000000),(2490439/100000000000000)⟩
def e116 : ℝ := (12617/25000000000000)
theorem h116 : Model (fun x => f116 ((59/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(63676562419/2500000000000),(38964505321/10000000000000),(9591667363/50000000000000),(16676989/6250000000000)⟩
def e117 : ℝ := (823313/20000000000000)
theorem h117 : Model (fun x => f117 ((59/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(5280975138069/100000000000000),(816986895467/100000000000000),(20566407359/50000000000000),(123325003/20000000000000)⟩
def e118 : ℝ := (4632529/50000000000000)
theorem h118 : Model (fun x => f118 ((59/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(31651775793561899/100000000000000),(1919779175576137/100000000000000),(6349602950393/50000000000000),(-3625804961/10000000000000)⟩
def e119 : ℝ := (110921127/12500000000000)
theorem h119 : Model (fun x => f119 ((59/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(1448055981/50000000000000),(564980183/100000000000000),(19575111/50000000000000),(1033103/100000000000000)⟩
def e120 : ℝ := (9573/100000000000000)
theorem h120 : Model (fun x => f120 ((59/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(212456089/100000000000000),(12952007/25000000000000),(4853383/100000000000000),(208207/100000000000000)⟩
def e121 : ℝ := (197/5000000000000)
theorem h121 : Model (fun x => f121 ((59/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(15585581/100000000000000),(2280353/50000000000000),(538461/100000000000000),(31933/100000000000000)⟩
def e122 : ℝ := (99/10000000000000)
theorem h122 : Model (fun x => f122 ((59/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(1143343/100000000000000),(39033/10000000000000),(27801/50000000000000),(2103/50000000000000)⟩
def e123 : ℝ := (187/100000000000000)
theorem h123 : Model (fun x => f123 ((59/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(3430029/100000000000000),(117099/10000000000000),(83403/50000000000000),(6309/50000000000000)⟩
def e124 : ℝ := (561/100000000000000)
theorem h124 : Model (fun x => f124 ((59/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-3430029/100000000000000),(-117099/10000000000000),(-83403/50000000000000),(-6309/50000000000000)⟩
def e125 : ℝ := (561/100000000000000)
theorem h125 : Model (fun x => f125 ((59/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(3165177579013187/10000000000000),(1919779174405147/100000000000000),(634960286699/5000000000000),(-9064515557/25000000000000)⟩
def e126 : ℝ := (887369577/100000000000000)
theorem h126 : Model (fun x => f126 ((59/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2419409370760599/10000000000000),(3225789555723/2000000000000),(-17696548401/5000000000000),(8216439/2500000000000)⟩
def e127 : ℝ := (4307289/10000000000000)
theorem h127 : Model (fun x => f127 ((59/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(461995872059401/25000000000000),(1594429359353/12500000000000),(-2029104907/12500000000000),(-6704611/25000000000000)⟩
def e128 : ℝ := (1757193/50000000000000)
theorem h128 : Model (fun x => f128 ((59/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(447102856845291829/100000000000000),(6066664784180283/100000000000000),(2021040021837/20000000000000),(-2869689513/4000000000000)⟩
def e129 : ℝ := (1713596739/100000000000000)
theorem h129 : Model (fun x => f129 ((59/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(22366218079/100000000000000),(-151741759/50000000000000),(3612407/100000000000000),(-38569/100000000000000)⟩
def e130 : ℝ := (491/100000000000000)
theorem h130 : Model (fun x => f130 ((59/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (441026013405167797/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(7079305199097/100000000000000),(66664814821/20000000000000),(-460622591/25000000000000),(1049291/10000000000000)⟩
def e131 : ℝ := (271987/50000000000000)
theorem h131 : Model (fun x => f131 ((59/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(7349109517309/50000000000000),(719424460031/100000000000000),(-2587858037/100000000000000),(1241131/10000000000000)⟩
def e132 : ℝ := (83817/10000000000000)
theorem h132 : Model (fun x => f132 ((59/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-153831554273193/100000000000000),(-3745658514251/50000000000000),(28559442203/100000000000000),(-151831917/100000000000000)⟩
def e133 : ℝ := (13162669/50000000000000)
theorem h133 : Model (fun x => f133 ((59/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(67796610169491/100000000000000),(-1149095087619/100000000000000),(779047517/4000000000000),(-330104881/100000000000000)⟩
def e134 : ℝ := (5691467/100000000000000)
theorem h134 : Model (fun x => f134 ((59/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (29/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-52146289584133/50000000000000),(-3311188169013/100000000000000),(75484167071/100000000000000),(-691164777/50000000000000)⟩
def e135 : ℝ := (29749607/50000000000000)
theorem h135 : Model (fun x => f135 ((59/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(12117361/256000),(205379/64000),(10443/128000),(59/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((59/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((59/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(1848411/32000),(93987/32000),(1593/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((59/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(26904649/256000),(393353/64000),(3363/25600),(77/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((59/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-3481/1600),(-59/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((59/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(26347689/256000),(388633/64000),(3347/25600),(77/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((59/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((59/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(177/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((59/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-177/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((59/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(24082089/256000),(379033/64000),(3347/25600),(77/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((59/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(24850089/256000),(379033/64000),(3347/25600),(77/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((59/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((59/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(24850089/4000),(379033/1000),(3347/400),(77/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((59/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((59/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(2290181229/512000),(38816631/128000),(1973727/256000),(11151/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((59/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(22356309339/100000000000000),(-151568199/10000000000000),(64223813/100000000000000),(-2177079/100000000000000)⟩
def e151 : ℝ := (19061/25000000000000)
theorem h151 : Model (fun x => f151 ((59/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (1065461229/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(6944453459821/5000000000000),(-942429089111/100000000000000),(36139981/312500000000),(-143240447/100000000000000)⟩
def e152 : ℝ := (927133653/100000000000000)
theorem h152 : Model (fun x => f152 ((59/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(179/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((59/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(24881/1600),(159/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((59/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(297/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((59/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3367003367003/50000000000000),(-68020270041/100000000000000),(343536717/50000000000000),(-867517/12500000000000)⟩
def e156 : ℝ := (70821/100000000000000)
theorem h156 : Model (fun x => f156 ((59/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (147/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(52359006734001/50000000000000),(280626126577/100000000000000),(1374146857/100000000000000),(-13880277/100000000000000)⟩
def e157 : ℝ := (1034851/50000000000000)
theorem h157 : Model (fun x => f157 ((59/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(102359006734001/50000000000000),(280626126577/100000000000000),(1374146857/100000000000000),(-13880277/100000000000000)⟩
def e158 : ℝ := (1034851/50000000000000)
theorem h158 : Model (fun x => f158 ((59/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(102359006734001/100000000000000),(17539132911/12500000000000),(171768357/25000000000000),(-6940139/100000000000000)⟩
def e159 : ℝ := (1034853/100000000000000)
theorem h159 : Model (fun x => f159 ((59/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(2359006734001/100000000000000),(17539132911/12500000000000),(171768357/25000000000000),(-6940139/100000000000000)⟩
def e160 : ℝ := (1034853/100000000000000)
theorem h160 : Model (fun x => f160 ((59/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((59/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((59/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(188876738616311/50000000000000),(517822019277/100000000000000),(2535628127/100000000000000),(-12806209/50000000000000)⟩
def e163 : ℝ := (1909551/50000000000000)
theorem h163 : Model (fun x => f163 ((59/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2733467762946907/100000000000000),(517822019277/100000000000000),(2535628127/100000000000000),(-12806209/50000000000000)⟩
def e164 : ℝ := (3819103/100000000000000)
theorem h164 : Model (fun x => f164 ((59/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((59/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2797950451546571/100000000000000),(2182724913881/50000000000000),(4420589273/20000000000000),(-52201861/25000000000000)⟩
def e166 : ℝ := (8065537/25000000000000)
theorem h166 : Model (fun x => f166 ((59/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8080331403927523/100000000000000),(2182724913881/50000000000000),(4420589273/20000000000000),(-52201861/25000000000000)⟩
def e167 : ℝ := (32262149/100000000000000)
theorem h167 : Model (fun x => f167 ((59/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((59/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(827094696587577/10000000000000),(15806191599841/100000000000000),(21066865677/25000000000000),(-71351229/10000000000000)⟩
def e169 : ℝ := (117180741/100000000000000)
theorem h169 : Model (fun x => f169 ((59/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13539994584923389/100000000000000),(15806191599841/100000000000000),(21066865677/25000000000000),(-71351229/10000000000000)⟩
def e170 : ℝ := (58590371/50000000000000)
theorem h170 : Model (fun x => f170 ((59/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((59/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(6929701984482551/50000000000000),(7035488379041/20000000000000),(50365798599/25000000000000),(-721600069/50000000000000)⟩
def e172 : ℝ := (52384743/20000000000000)
theorem h172 : Model (fun x => f172 ((59/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(16195118254679387/100000000000000),(7035488379041/20000000000000),(50365798599/25000000000000),(-721600069/50000000000000)⟩
def e173 : ℝ := (65480929/25000000000000)
theorem h173 : Model (fun x => f173 ((59/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((59/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(8288581092443349/50000000000000),(7341393330577/12500000000000),(91711656297/25000000000000),(-207683501/10000000000000)⟩
def e175 : ℝ := (439539813/100000000000000)
theorem h175 : Model (fun x => f175 ((59/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(339590862745353/2000000000000),(7341393330577/12500000000000),(91711656297/25000000000000),(-207683501/10000000000000)⟩
def e176 : ℝ := (219769907/50000000000000)
theorem h176 : Model (fun x => f176 ((59/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((59/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(8690045851639199/50000000000000),(41970567728563/50000000000000),(71821245229/12500000000000),(-74561617/3125000000000)⟩
def e178 : ℝ := (631362749/100000000000000)
theorem h178 : Model (fun x => f178 ((59/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(347249453113187/2000000000000),(41970567728563/50000000000000),(71821245229/12500000000000),(-74561617/3125000000000)⟩
def e179 : ℝ := (2525451/400000000000)
theorem h179 : Model (fun x => f179 ((59/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((59/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(4443013638698859/25000000000000),(110283129740853/100000000000000),(412598710251/50000000000000),(-566075691/25000000000000)⟩
def e181 : ℝ := (832979801/100000000000000)
theorem h181 : Model (fun x => f181 ((59/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(17775387888128769/100000000000000),(110283129740853/100000000000000),(412598710251/50000000000000),(-566075691/25000000000000)⟩
def e182 : ℝ := (416489901/50000000000000)
theorem h182 : Model (fun x => f182 ((59/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(83864519455151/20000000000000),(27542777714211/100000000000000),(1185352269/400000000000),(19641693/3125000000000)⟩
def e183 : ℝ := (13197361/6250000000000)
theorem h183 : Model (fun x => f183 ((59/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(818544239029/781250000000),(287246115799/100000000000000),(160344063/10000000000000),(-1534951/12500000000000)⟩
def e184 : ℝ := (1068151/50000000000000)
theorem h184 : Model (fun x => f184 ((59/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(202359006734001/100000000000000),(17539132911/12500000000000),(171768357/25000000000000),(-6940139/100000000000000)⟩
def e185 : ℝ := (1034853/100000000000000)
theorem h185 : Model (fun x => f185 ((59/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(204745838031857/50000000000000),(4542977939/800000000000),(1488793743/50000000000000),(-13079943/50000000000000)⟩
def e186 : ℝ := (525751/12500000000000)
theorem h186 : Model (fun x => f186 ((59/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(51790205521309/6250000000000),(861855471891/50000000000000),(1204465487/12500000000000),(-36638267/50000000000000)⟩
def e187 : ℝ := (12816761/100000000000000)
theorem h187 : Model (fun x => f187 ((59/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(838417163827349/50000000000000),(1162694781601/25000000000000),(13805367321/50000000000000),(-45106831/25000000000000)⟩
def e188 : ℝ := (1735227/5000000000000)
theorem h188 : Model (fun x => f188 ((59/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1756880740746009/100000000000000),(4844716552271/50000000000000),(8646875407/12500000000000),(-241065753/100000000000000)⟩
def e189 : ℝ := (36518307/50000000000000)
theorem h189 : Model (fun x => f189 ((59/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((59/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(102359006734001/12500000000000),(17539132911/1562500000000),(171768357/3125000000000),(-6940139/12500000000000)⟩
def e191 : ℝ := (1034853/12500000000000)
theorem h191 : Model (fun x => f191 ((59/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(23091142911693/2500000000000),(1409750622103/100000000000000),(3550014027/50000000000000),(-847509/1250000000000)⟩
def e192 : ℝ := (5207563/50000000000000)
theorem h192 : Model (fun x => f192 ((59/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(25591142911693/2500000000000),(1409750622103/100000000000000),(3550014027/50000000000000),(-847509/1250000000000)⟩
def e193 : ℝ := (5207563/50000000000000)
theorem h193 : Model (fun x => f193 ((59/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(1798423444609287/10000000000000),(30988276024231/25000000000000),(484721413317/50000000000000),(-1995689539/100000000000000)⟩
def e194 : ℝ := (187557891/20000000000000)
theorem h194 : Model (fun x => f194 ((59/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(278021286643/50000000000000),(-1916211757/50000000000000),(-889817/25000000000000),(146411/50000000000000)⟩
def e195 : ℝ := (15843/50000000000000)
theorem h195 : Model (fun x => f195 ((59/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (8929654482845159/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2331612160261/100000000000000),(137079352139/100000000000000),(57728511/10000000000000),(-1522893/20000000000000)⟩
def e196 : ℝ := (1370781/100000000000000)
theorem h196 : Model (fun x => f196 ((59/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(52359006734001/25000000000000),(280626126577/50000000000000),(1374146857/50000000000000),(-13880277/50000000000000)⟩
def e197 : ℝ := (1034851/25000000000000)
theorem h197 : Model (fun x => f197 ((59/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(48847679940793/100000000000000),(-66960083199/100000000000000),(-118048081/50000000000000),(1021267/25000000000000)⟩
def e198 : ℝ := (251913/50000000000000)
theorem h198 : Model (fun x => f198 ((59/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (204435997244589/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(25576160029603/25000000000000),(33480041599/25000000000000),(1475601/312500000000),(-4085069/50000000000000)⟩
def e199 : ℝ := (779507/25000000000000)
theorem h199 : Model (fun x => f199 ((59/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(576160029603/25000000000000),(33480041599/25000000000000),(1475601/312500000000),(-4085069/50000000000000)⟩
def e200 : ℝ := (779507/25000000000000)
theorem h200 : Model (fun x => f200 ((59/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(188776419266117/50000000000000),(494229185509/100000000000000),(871307257/50000000000000),(-301517/1000000000000)⟩
def e201 : ℝ := (1150701/10000000000000)
theorem h201 : Model (fun x => f201 ((59/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2733267124246519/100000000000000),(494229185509/100000000000000),(871307257/50000000000000),(-301517/1000000000000)⟩
def e202 : ℝ := (11507011/100000000000000)
theorem h202 : Model (fun x => f202 ((59/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(279625909493527/10000000000000),(4166015270433/100000000000000),(30701851/200000000000),(-12474543/5000000000000)⟩
def e203 : ℝ := (97099991/100000000000000)
theorem h203 : Model (fun x => f203 ((59/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4039320023658111/50000000000000),(4166015270433/100000000000000),(30701851/200000000000),(-12474543/5000000000000)⟩
def e204 : ℝ := (12137499/12500000000000)
theorem h204 : Model (fun x => f204 ((59/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8264823626868769/100000000000000),(7540477561797/50000000000000),(59430561533/100000000000000),(-437523589/50000000000000)⟩
def e205 : ℝ := (352097403/100000000000000)
theorem h205 : Model (fun x => f205 ((59/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(3383467811479097/25000000000000),(7540477561797/50000000000000),(59430561533/100000000000000),(-437523589/50000000000000)⟩
def e206 : ℝ := (88024351/25000000000000)
theorem h206 : Model (fun x => f206 ((59/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13845778272224003/100000000000000),(33553099757963/100000000000000),(72451281457/50000000000000),(-925074603/50000000000000)⟩
def e207 : ℝ := (196319913/25000000000000)
theorem h207 : Model (fun x => f207 ((59/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(1011343284871143/6250000000000),(33553099757963/100000000000000),(72451281457/50000000000000),(-925074603/50000000000000)⟩
def e208 : ℝ := (785279653/100000000000000)
theorem h208 : Model (fun x => f208 ((59/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(3310883545437277/20000000000000),(55996659714903/100000000000000),(134792088829/50000000000000),(-1431174923/50000000000000)⟩
def e209 : ℝ := (657291387/50000000000000)
theorem h209 : Model (fun x => f209 ((59/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16956798679567337/100000000000000),(55996659714903/100000000000000),(134792088829/50000000000000),(-1431174923/50000000000000)⟩
def e210 : ℝ := (52583311/4000000000000)
theorem h210 : Model (fun x => f210 ((59/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(8673795932367501/50000000000000),(39997877103387/50000000000000),(215428321859/50000000000000),(-230516941/6250000000000)⟩
def e211 : ℝ := (1884289331/100000000000000)
theorem h211 : Model (fun x => f211 ((59/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(8664986408557977/50000000000000),(39997877103387/50000000000000),(215428321859/50000000000000),(-230516941/6250000000000)⟩
def e212 : ℝ := (471072333/25000000000000)
theorem h212 : Model (fun x => f212 ((59/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(8864683161584551/50000000000000),(13130962110539/12500000000000),(5037980693/800000000000),(-529302173/12500000000000)⟩
def e213 : ℝ := (248260277/10000000000000)
theorem h213 : Model (fun x => f213 ((59/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(3546539931300487/20000000000000),(13130962110539/12500000000000),(5037980693/800000000000),(-529302173/12500000000000)⟩
def e214 : ℝ := (2482602771/100000000000000)
theorem h214 : Model (fun x => f214 ((59/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(204337455180631/50000000000000),(13084316126177/50000000000000),(47785182379/20000000000000),(-103493971/50000000000000)⟩
def e215 : ℝ := (628108947/100000000000000)
theorem h215 : Model (fun x => f215 ((59/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(104662393897577/100000000000000),(137006544277/50000000000000),(143186927/12500000000000),(-772607/5000000000000)⟩
def e216 : ℝ := (6407891/100000000000000)
theorem h216 : Model (fun x => f216 ((59/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(50576160029603/25000000000000),(33480041599/25000000000000),(1475601/312500000000),(-4085069/50000000000000)⟩
def e217 : ℝ := (779507/25000000000000)
theorem h217 : Model (fun x => f217 ((59/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(409271674134401/100000000000000),(270926710673/50000000000000),(261235007/12500000000000),(-993513/3125000000000)⟩
def e218 : ℝ := (12643947/100000000000000)
theorem h218 : Model (fun x => f218 ((59/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(827975587464199/100000000000000),(328858384207/20000000000000),(3443062371/50000000000000),(-92398233/100000000000000)⟩
def e219 : ℝ := (19225879/50000000000000)
theorem h219 : Model (fun x => f219 ((59/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(335006606497551/20000000000000),(1108826284449/25000000000000),(20042625489/100000000000000),(-237586531/100000000000000)⟩
def e220 : ℝ := (51967971/50000000000000)
theorem h220 : Model (fun x => f220 ((59/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1753129670376863/100000000000000),(4615953140249/50000000000000),(10463566967/20000000000000),(-200883283/50000000000000)⟩
def e221 : ℝ := (108900147/50000000000000)
theorem h221 : Model (fun x => f221 ((59/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(25576160029603/3125000000000),(33480041599/3125000000000),(1475601/39062500000),(-4085069/6250000000000)⟩
def e222 : ℝ := (779507/3125000000000)
theorem h222 : Model (fun x => f222 ((59/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(923099514844873/100000000000000),(672687209861/50000000000000),(615379247/12500000000000),(-20203311/25000000000000)⟩
def e223 : ℝ := (6270423/20000000000000)
theorem h223 : Model (fun x => f223 ((59/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1023099514844873/100000000000000),(672687209861/50000000000000),(615379247/12500000000000),(-20203311/25000000000000)⟩
def e224 : ℝ := (6270423/20000000000000)
theorem h224 : Model (fun x => f224 ((59/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(8968130576113603/50000000000000),(23607549299303/20000000000000),(18644359731/2500000000000),(-4368872097/100000000000000)⟩
def e225 : ℝ := (1397080867/50000000000000)
theorem h225 : Model (fun x => f225 ((59/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(557529794817/100000000000000),(-3669079081/100000000000000),(241109/25000000000000),(70503/25000000000000)⟩
def e226 : ℝ := (9083/10000000000000)
theorem h226 : Model (fun x => f226 ((59/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (890873523415381/5000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(455696877841/20000000000000),(130903316057/100000000000000),(187938371/50000000000000),(-8515509/100000000000000)⟩
def e227 : ℝ := (1001127/25000000000000)
theorem h227 : Model (fun x => f227 ((59/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(2305048274733/50000000000000),(66995667049/25000000000000),(238290463/25000000000000),(-8064987/50000000000000)⟩
def e228 : ℝ := (5375289/100000000000000)
theorem h228 : Model (fun x => f228 ((59/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(6402920186609/100000000000000),(164375871273/50000000000000),(-66856083/10000000000000),(-279901/4000000000000)⟩
def e229 : ℝ := (26438599/50000000000000)
theorem h229 : Model (fun x => f229 ((59/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(2170481419189/50000000000000),(14930689599/10000000000000),(-372985867/12500000000000),(4583027/10000000000000)⟩
def e230 : ℝ := (379861/1000000000000)
theorem h230 : Model (fun x => f230 ((59/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-3123488010309/3125000000000),(-3161881273023/100000000000000),(14500056027/20000000000000),(-334124821/25000000000000)⟩
def e231 : ℝ := (48742657/50000000000000)
theorem h231 : Model (fun x => f231 ((59/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((59/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-3481/320),(-59/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((59/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1239/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((59/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6431/320),(5/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((59/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((59/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14751/320),(5/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((59/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((59/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(368775/32),(625/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((59/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(10679/1600),(61/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((59/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(20279/1600),(61/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((59/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((59/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3832731/1600),(11529/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((59/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(41745689953/100000000000000),(-251145233/100000000000000),(892369/25000000000000),(-33859/100000000000000)⟩
def e244 : ℝ := (77/20000000000000)
theorem h244 : Model (fun x => f244 ((59/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (952371/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(481086462888049/100000000000000),(-1263561589323/100000000000000),(-1288758693/100000000000000),(-27279327/50000000000000)⟩
def e245 : ℝ := (8589889/100000000000000)
theorem h245 : Model (fun x => f245 ((59/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(531/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((59/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(45961/1600),(419/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((59/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(79561/1600),(419/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((59/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(19321/1600),(139/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((59/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1537198081/2560000),(9577239/640000),(165923/1280000),(279/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((59/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((59/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(88209/160),(891/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((59/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(90693693387/50000000000000),(-3664391653/100000000000000),(11104217/20000000000000),(-747759/100000000000000)⟩
def e253 : ℝ := (4859/50000000000000)
theorem h253 : Model (fun x => f253 ((59/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (43209/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(13614665179033/12500000000000),(20560400029/4000000000000),(403169177/20000000000000),(-563817/4000000000000)⟩
def e254 : ℝ := (2343517/20000000000000)
theorem h254 : Model (fun x => f254 ((59/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(26114665179033/12500000000000),(20560400029/4000000000000),(403169177/20000000000000),(-563817/4000000000000)⟩
def e255 : ℝ := (2343517/20000000000000)
theorem h255 : Model (fun x => f255 ((59/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(26114665179033/25000000000000),(128502500181/50000000000000),(503961471/50000000000000),(-7047713/100000000000000)⟩
def e256 : ℝ := (2929397/50000000000000)
theorem h256 : Model (fun x => f256 ((59/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(1114665179033/25000000000000),(128502500181/50000000000000),(503961471/50000000000000),(-7047713/100000000000000)⟩
def e257 : ℝ := (2929397/50000000000000)
theorem h257 : Model (fun x => f257 ((59/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(77100440052383/20000000000000),(948470834669/100000000000000),(3719715619/100000000000000),(-13004709/50000000000000)⟩
def e258 : ℝ := (21621743/100000000000000)
theorem h258 : Model (fun x => f258 ((59/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(13706082429881/500000000000),(948470834669/100000000000000),(3719715619/100000000000000),(-13004709/50000000000000)⟩
def e259 : ℝ := (1351359/6250000000000)
theorem h259 : Model (fun x => f259 ((59/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1431719014290277/50000000000000),(2008955842721/25000000000000),(16976266221/50000000000000),(-201242451/100000000000000)⟩
def e260 : ℝ := (91698159/50000000000000)
theorem h260 : Model (fun x => f260 ((59/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4072909490480753/50000000000000),(2008955842721/25000000000000),(16976266221/50000000000000),(-201242451/100000000000000)⟩
def e261 : ℝ := (183396319/100000000000000)
theorem h261 : Model (fun x => f261 ((59/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(425450670593643/5000000000000),(29329275572247/100000000000000),(69111203437/50000000000000),(-616054499/100000000000000)⟩
def e262 : ℝ := (670511873/100000000000000)
theorem h262 : Model (fun x => f262 ((59/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(13778061030920479/100000000000000),(29329275572247/100000000000000),(69111203437/50000000000000),(-616054499/100000000000000)⟩
def e263 : ℝ := (335255937/50000000000000)
theorem h263 : Model (fun x => f263 ((59/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(7196189012775411/50000000000000),(33023637131453/50000000000000),(179317608957/50000000000000),(-963705483/100000000000000)⟩
def e264 : ℝ := (1513365661/100000000000000)
theorem h264 : Model (fun x => f264 ((59/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(16728092311265107/100000000000000),(33023637131453/50000000000000),(179317608957/50000000000000),(-963705483/100000000000000)⟩
def e265 : ℝ := (756682831/50000000000000)
theorem h265 : Model (fun x => f265 ((59/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(17473941191705781/100000000000000),(6999008239979/6250000000000),(712976623111/100000000000000),(-119641141/20000000000000)⟩
def e266 : ℝ := (20578027/800000000000)
theorem h266 : Model (fun x => f266 ((59/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(17876322144086733/100000000000000),(6999008239979/6250000000000),(712976623111/100000000000000),(-119641141/20000000000000)⟩
def e267 : ℝ := (40191459/1562500000000)
theorem h267 : Model (fun x => f267 ((59/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(18673366697014333/100000000000000),(81460083062711/50000000000000),(303187550559/25000000000000),(1076349781/100000000000000)⟩
def e268 : ℝ := (468727241/12500000000000)
theorem h268 : Model (fun x => f268 ((59/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(3731149529879057/20000000000000),(81460083062711/50000000000000),(303187550559/25000000000000),(1076349781/100000000000000)⟩
def e269 : ℝ := (3749817929/100000000000000)
theorem h269 : Model (fun x => f269 ((59/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(19487544141139591/100000000000000),(8725217115399/4000000000000),(468392788297/25000000000000),(2284237703/50000000000000)⟩
def e270 : ℝ := (2516442799/50000000000000)
theorem h270 : Model (fun x => f270 ((59/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(4872719368618231/25000000000000),(8725217115399/4000000000000),(468392788297/25000000000000),(2284237703/50000000000000)⟩
def e271 : ℝ := (5032885599/100000000000000)
theorem h271 : Model (fun x => f271 ((59/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(173806419436749/20000000000000),(7477278177733/12500000000000),(840595313633/100000000000000),(5843789887/100000000000000)⟩
def e272 : ℝ := (11260353/800000000000)
theorem h272 : Model (fun x => f272 ((59/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(109116117986079/100000000000000),(536927962703/100000000000000),(1383120657/50000000000000),(-9543069/100000000000000)⟩
def e273 : ℝ := (6148241/50000000000000)
theorem h273 : Model (fun x => f273 ((59/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(51114665179033/25000000000000),(128502500181/50000000000000),(503961471/50000000000000),(-7047713/100000000000000)⟩
def e274 : ℝ := (2929397/50000000000000)
theorem h274 : Model (fun x => f274 ((59/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(418033439418343/100000000000000),(1050937963427/100000000000000),(2391043599/50000000000000),(-4727699/20000000000000)⟩
def e275 : ℝ := (2401407/10000000000000)
theorem h275 : Model (fun x => f275 ((59/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(854705571580327/100000000000000),(322310052747/10000000000000),(16691809497/100000000000000),(-549099/1000000000000)⟩
def e276 : ℝ := (73801579/100000000000000)
theorem h276 : Model (fun x => f276 ((59/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1747519564719297/100000000000000),(8786544229333/100000000000000),(51026153211/100000000000000),(-12140011/12500000000000)⟩
def e277 : ℝ := (100775587/50000000000000)
theorem h277 : Model (fun x => f277 ((59/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(953412755034461/50000000000000),(18970457164861/100000000000000),(151195778633/100000000000000),(244290033/100000000000000)⟩
def e278 : ℝ := (699267/160000000000)
theorem h278 : Model (fun x => f278 ((59/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(26114665179033/3125000000000),(128502500181/6250000000000),(503961471/6250000000000),(-7047713/12500000000000)⟩
def e279 : ℝ := (2929397/6250000000000)
theorem h279 : Model (fun x => f279 ((59/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(188957080743027/20000000000000),(2592967965599/100000000000000),(216592497/2000000000000),(-65924773/100000000000000)⟩
def e280 : ℝ := (29583417/50000000000000)
theorem h280 : Model (fun x => f280 ((59/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(208957080743027/20000000000000),(2592967965599/100000000000000),(216592497/2000000000000),(-65924773/100000000000000)⟩
def e281 : ℝ := (29583417/50000000000000)
theorem h281 : Model (fun x => f281 ((59/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(622569831359899/3125000000000),(30955492764057/12500000000000),(142379459543/6250000000000),(7270123667/100000000000000)⟩
def e282 : ℝ := (2863663753/50000000000000)
theorem h282 : Model (fun x => f282 ((59/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(25097586187/5000000000000),(-6239526143/100000000000000),(403267/2000000000000),(139831/50000000000000)⟩
def e283 : ℝ := (37/24414062500)
theorem h283 : Model (fun x => f283 ((59/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (19672299592600451/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(4362121591667/100000000000000),(3075439109/1250000000000),(165558709/25000000000000),(-172489/2000000000000)⟩
def e284 : ℝ := (1074209/12500000000000)
theorem h284 : Model (fun x => f284 ((59/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(13614665179033/6250000000000),(20560400029/2000000000000),(403169177/10000000000000),(-563817/2000000000000)⟩
def e285 : ℝ := (2343517/10000000000000)
theorem h285 : Model (fun x => f285 ((59/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(373951759789/781250000000),(-117766744779/100000000000000),(-86055197/50000000000000),(119731/2500000000000)⟩
def e286 : ℝ := (169757/6250000000000)
theorem h286 : Model (fun x => f286 ((59/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (52100317443161/25000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(52134174747007/50000000000000),(235533489557/100000000000000),(344220783/100000000000000),(-9578481/100000000000000)⟩
def e287 : ℝ := (4316371/25000000000000)
theorem h287 : Model (fun x => f287 ((59/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(2134174747007/50000000000000),(235533489557/100000000000000),(344220783/100000000000000),(-9578481/100000000000000)⟩
def e288 : ℝ := (4316371/25000000000000)
theorem h288 : Model (fun x => f288 ((59/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(96199965306977/25000000000000),(869230735269/100000000000000),(1270338603/100000000000000),(-35349157/100000000000000)⟩
def e289 : ℝ := (31858931/50000000000000)
theorem h289 : Model (fun x => f289 ((59/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2740514146942193/100000000000000),(869230735269/100000000000000),(1270338603/100000000000000),(-35349157/100000000000000)⟩
def e290 : ℝ := (63717863/100000000000000)
theorem h290 : Model (fun x => f290 ((59/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1428744434333291/50000000000000),(1472232228611/20000000000000),(1600663729/12500000000000),(-36671683/12500000000000)⟩
def e291 : ℝ := (270031803/50000000000000)
theorem h291 : Model (fun x => f291 ((59/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4069934910523767/50000000000000),(1472232228611/20000000000000),(1600663729/12500000000000),(-36671683/12500000000000)⟩
def e292 : ℝ := (540063607/100000000000000)
theorem h292 : Model (fun x => f292 ((59/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4243653956683807/50000000000000),(838983770699/3125000000000),(29354504277/50000000000000),(-515036057/50000000000000)⟩
def e293 : ℝ := (493101209/25000000000000)
theorem h293 : Model (fun x => f293 ((59/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(13756355532415233/100000000000000),(838983770699/3125000000000),(29354504277/50000000000000),(-515036057/50000000000000)⟩
def e294 : ℝ := (1972404837/100000000000000)
theorem h294 : Model (fun x => f294 ((59/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(2868704972835569/20000000000000),(3019712459437/5000000000000),(171801957011/100000000000000),(-2160995109/100000000000000)⟩
def e295 : ℝ := (889159783/20000000000000)
theorem h295 : Model (fun x => f295 ((59/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(1667923914989213/10000000000000),(3019712459437/5000000000000),(171801957011/100000000000000),(-2160995109/100000000000000)⟩
def e296 : ℝ := (1111449729/25000000000000)
theorem h296 : Model (fun x => f296 ((59/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(3478233473950387/20000000000000),(102257280819699/100000000000000),(378797155179/100000000000000),(-404788873/12500000000000)⟩
def e297 : ℝ := (7546565201/100000000000000)
theorem h297 : Model (fun x => f297 ((59/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(17793548322132887/100000000000000),(102257280819699/100000000000000),(378797155179/100000000000000),(-404788873/12500000000000)⟩
def e298 : ℝ := (3773282601/50000000000000)
theorem h298 : Model (fun x => f298 ((59/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(9276519575953891/50000000000000),(148531744227289/100000000000000),(348532387417/50000000000000),(-383670009/10000000000000)⟩
def e299 : ℝ := (10992510929/100000000000000)
theorem h299 : Model (fun x => f299 ((59/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(9267710052144367/50000000000000),(148531744227289/100000000000000),(348532387417/50000000000000),(-383670009/10000000000000)⟩
def e300 : ℝ := (1099251093/10000000000000)
theorem h300 : Model (fun x => f300 ((59/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(19326576614523511/100000000000000),(39705743991229/20000000000000),(1140462704117/100000000000000),(-3622777431/100000000000000)⟩
def e301 : ℝ := (14734581981/100000000000000)
theorem h301 : Model (fun x => f301 ((59/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(4832477486964211/25000000000000),(39705743991229/20000000000000),(1140462704117/100000000000000),(-3622777431/100000000000000)⟩
def e302 : ℝ := (7367290991/50000000000000)
theorem h302 : Model (fun x => f302 ((59/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(825068113452709/100000000000000),(54002311042133/100000000000000),(582818123321/100000000000000),(340851041/25000000000000)⟩
def e303 : ℝ := (405930523/10000000000000)
theorem h303 : Model (fun x => f303 ((59/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(54359443531029/50000000000000),(491173764133/100000000000000),(254517381/20000000000000),(-9176569/50000000000000)⟩
def e304 : ℝ := (36130333/100000000000000)
theorem h304 : Model (fun x => f304 ((59/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(102134174747007/50000000000000),(235533489557/100000000000000),(344220783/100000000000000),(-9578481/100000000000000)⟩
def e305 : ℝ := (4316371/25000000000000)
theorem h305 : Model (fun x => f305 ((59/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(208627793025043/50000000000000),(962240743247/100000000000000),(1961028471/100000000000000),(-375101/1000000000000)⟩
def e306 : ℝ := (70661301/100000000000000)
theorem h306 : Model (fun x => f306 ((59/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(170464219759217/20000000000000),(368541240823/12500000000000),(963555017/12500000000000),(-54328449/50000000000000)⟩
def e307 : ℝ := (108443567/50000000000000)
theorem h307 : Model (fun x => f307 ((59/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1741022240900007/100000000000000),(125468851639/1562500000000),(25624074157/100000000000000),(-55057269/20000000000000)⟩
def e308 : ℝ := (591724091/100000000000000)
theorem h308 : Model (fun x => f308 ((59/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1892820003809389/100000000000000),(3456315635631/20000000000000),(11181939313/12500000000000),(-15630917/4000000000000)⟩
def e309 : ℝ := (640342957/50000000000000)
theorem h309 : Model (fun x => f309 ((59/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(52134174747007/6250000000000),(235533489557/12500000000000),(344220783/12500000000000),(-9578481/12500000000000)⟩
def e310 : ℝ := (4316371/3125000000000)
theorem h310 : Model (fun x => f310 ((59/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(94286568301417/10000000000000),(2375441680589/100000000000000),(4026353169/100000000000000),(-47490493/50000000000000)⟩
def e311 : ℝ := (34850841/20000000000000)
theorem h311 : Model (fun x => f311 ((59/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(104286568301417/10000000000000),(2375441680589/100000000000000),(4026353169/100000000000000),(-47490493/50000000000000)⟩
def e312 : ℝ := (34850841/20000000000000)
theorem h312 : Model (fun x => f312 ((59/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(19739570260955623/100000000000000),(112593241806129/50000000000000),(35490657291/2500000000000),(-3052274889/100000000000000)⟩
def e313 : ℝ := (8368547913/50000000000000)
theorem h313 : Model (fun x => f313 ((59/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(253298320779/50000000000000),(-5779189457/100000000000000),(29494939/100000000000000),(31497/20000000000000)⟩
def e314 : ℝ := (44439/10000000000000)
theorem h314 : Model (fun x => f314 ((59/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (1951294436168101/10000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(4179767353317/100000000000000),(225891644677/100000000000000),(74994509/100000000000000),(-9547897/100000000000000)⟩
def e315 : ℝ := (3111087/12500000000000)
theorem h315 : Model (fun x => f315 ((59/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1067736118123/12500000000000),(471926773397/100000000000000),(147445869/20000000000000),(-18172347/100000000000000)⟩
def e316 : ℝ := (261581/781250000000)
theorem h316 : Model (fun x => f316 ((59/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(642091740457/1562500000000),(432488758769/20000000000000),(-631614799/25000000000000),(-53741193/50000000000000)⟩
def e317 : ℝ := (32462909/20000000000000)
theorem h317 : Model (fun x => f317 ((59/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(696506294733/2500000000000),(993855931601/100000000000000),(-18557869483/100000000000000),(120835373/50000000000000)⟩
def e318 : ℝ := (604057/500000000000)
theorem h318 : Model (fun x => f318 ((59/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-9011420567571/12500000000000),(-1084012670711/50000000000000),(13485602663/25000000000000),(-547414269/50000000000000)⟩
def e319 : ℝ := (109148357/50000000000000)
theorem h319 : Model (fun x => f319 ((59/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((59/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-38291/1600),(-649/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((59/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((59/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(5723/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((59/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(190629/1600),(1291/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((59/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((59/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(363429/1600),(1291/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((59/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1817145/32),(6455/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((59/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((59/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(185551291668665221/20000000000000),(5581453124803283/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (120501/100000000000000)
theorem h329 : Model (fun x => f329 ((59/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10778690797/100000000000000),(-64845421/100000000000000),(460817/50000000000000),(-8743/100000000000000)⟩
def e330 : ℝ := (103/100000000000000)
theorem h330 : Model (fun x => f330 ((59/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (230532313900656311/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(61207637775983/10000000000000),(166557544111/25000000000000),(3824378687/50000000000000),(-6601651/50000000000000)⟩
def e331 : ℝ := (11017009/100000000000000)
theorem h331 : Model (fun x => f331 ((59/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((59/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(419/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((59/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((59/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((59/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(545806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((59/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((59/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((59/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2421466708944727/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1027/100000000000000)
theorem h339 : Model (fun x => f339 ((59/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3644193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((59/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((59/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((59/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1026766645527507/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1027/100000000000000)
theorem h343 : Model (fun x => f343 ((59/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4869655653287/100000000000000),(-6681390367/100000000000000),(9167173/100000000000000),(-6289/50000000000000)⟩
def e344 : ℝ := (21/100000000000000)
theorem h344 : Model (fun x => f344 ((59/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1025357874709753/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(117917090484589/100000000000000),(459210847201/50000000000000),(-252023319/20000000000000),(432233/25000000000000)⟩
def e345 : ℝ := (3357/100000000000000)
theorem h345 : Model (fun x => f345 ((59/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(217917090484589/100000000000000),(459210847201/50000000000000),(-252023319/20000000000000),(432233/25000000000000)⟩
def e346 : ℝ := (3357/100000000000000)
theorem h346 : Model (fun x => f346 ((59/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(54479272621147/50000000000000),(459210847201/100000000000000),(-315029149/50000000000000),(432233/50000000000000)⟩
def e347 : ℝ := (21/1250000000000)
theorem h347 : Model (fun x => f347 ((59/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(4479272621147/50000000000000),(459210847201/100000000000000),(-315029149/50000000000000),(432233/50000000000000)⟩
def e348 : ℝ := (21/1250000000000)
theorem h348 : Model (fun x => f348 ((59/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(50263614620701/12500000000000),(1694706698003/100000000000000),(-581303787/25000000000000),(3190291/100000000000000)⟩
def e349 : ℝ := (6203/100000000000000)
theorem h349 : Model (fun x => f349 ((59/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2757823202679893/100000000000000),(1694706698003/100000000000000),(-581303787/25000000000000),(3190291/100000000000000)⟩
def e350 : ℝ := (1551/25000000000000)
theorem h350 : Model (fun x => f350 ((59/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(751221010498613/25000000000000),(14510751057599/100000000000000),(-12127137547/100000000000000),(2980629/50000000000000)⟩
def e351 : ℝ := (48571/50000000000000)
theorem h351 : Model (fun x => f351 ((59/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(2071816248593851/25000000000000),(14510751057599/100000000000000),(-12127137547/100000000000000),(2980629/50000000000000)⟩
def e352 : ℝ := (97143/100000000000000)
theorem h352 : Model (fun x => f352 ((59/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(9029683378245317/100000000000000),(53866723046553/100000000000000),(1206789441/100000000000000),(-13795887/20000000000000)⟩
def e353 : ℝ := (118783/25000000000000)
theorem h353 : Model (fun x => f353 ((59/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(1787341374661617/12500000000000),(53866723046553/100000000000000),(1206789441/100000000000000),(-13795887/20000000000000)⟩
def e354 : ℝ := (475133/100000000000000)
theorem h354 : Model (fun x => f354 ((59/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(15579689282759339/100000000000000),(1554421519411/1250000000000),(158586394323/100000000000000),(-71350343/25000000000000)⟩
def e355 : ℝ := (3611/400000000000)
theorem h355 : Model (fun x => f355 ((59/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(2239425446059203/12500000000000),(1554421519411/1250000000000),(158586394323/100000000000000),(-71350343/25000000000000)⟩
def e356 : ℝ := (902751/100000000000000)
theorem h356 : Model (fun x => f356 ((59/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(19520363102494887/100000000000000),(27220435308117/12500000000000),(78870214959/12500000000000),(-52837907/25000000000000)⟩
def e357 : ℝ := (1264403/50000000000000)
theorem h357 : Model (fun x => f357 ((59/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(19922744054875839/100000000000000),(27220435308117/12500000000000),(78870214959/12500000000000),(-52837907/25000000000000)⟩
def e358 : ℝ := (2528807/100000000000000)
theorem h358 : Model (fun x => f358 ((59/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(21707532094538329/100000000000000),(164379662161417/50000000000000),(390488835351/25000000000000),(2865913/195312500000)⟩
def e359 : ℝ := (6175627/100000000000000)
theorem h359 : Model (fun x => f359 ((59/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(21689913046919281/100000000000000),(164379662161417/50000000000000),(390488835351/25000000000000),(2865913/195312500000)⟩
def e360 : ℝ := (1543907/25000000000000)
theorem h360 : Model (fun x => f360 ((59/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(23633013720241773/100000000000000),(457813810590473/100000000000000),(1537461599411/50000000000000),(3443797659/50000000000000)⟩
def e361 : ℝ := (7392483/100000000000000)
theorem h361 : Model (fun x => f361 ((59/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(11818173526787553/50000000000000),(457813810590473/100000000000000),(1537461599411/50000000000000),(3443797659/50000000000000)⟩
def e362 : ℝ := (1848121/25000000000000)
theorem h362 : Model (fun x => f362 ((59/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(42349456888403/2000000000000),(37388531724827/25000000000000),(139304768637/6250000000000),(2411448699/20000000000000)⟩
def e363 : ℝ := (1083149/6250000000000)
theorem h363 : Model (fun x => f363 ((59/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(11871964581317/10000000000000),(100069891741/10000000000000),(73574131/10000000000000),(-3902773/100000000000000)⟩
def e364 : ℝ := (7799/50000000000000)
theorem h364 : Model (fun x => f364 ((59/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(104479272621147/50000000000000),(459210847201/100000000000000),(-315029149/50000000000000),(432233/50000000000000)⟩
def e365 : ℝ := (21/1250000000000)
theorem h365 : Model (fun x => f365 ((59/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(218318368148879/50000000000000),(479780152953/25000000000000),(-262187643/50000000000000),(-2173841/100000000000000)⟩
def e366 : ℝ := (9479/50000000000000)
theorem h366 : Model (fun x => f366 ((59/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(456194886080613/50000000000000),(6015249767831/100000000000000),(4966017061/100000000000000),(-7633709/50000000000000)⟩
def e367 : ℝ := (56993/100000000000000)
theorem h367 : Model (fun x => f367 ((59/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(953258197423789/50000000000000),(8379585605033/50000000000000),(32251008957/100000000000000),(-39110367/100000000000000)⟩
def e368 : ℝ := (46081/25000000000000)
theorem h368 : Model (fun x => f368 ((59/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1131704755666531/50000000000000),(2435932351581/6250000000000),(220024157169/100000000000000),(325200947/100000000000000)⟩
def e369 : ℝ := (332597/25000000000000)
theorem h369 : Model (fun x => f369 ((59/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(54479272621147/6250000000000),(459210847201/12500000000000),(-315029149/6250000000000),(432233/6250000000000)⟩
def e370 : ℝ := (21/156250000000)
theorem h370 : Model (fun x => f370 ((59/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(495194003875761/50000000000000),(2337192847509/50000000000000),(-2152362537/50000000000000),(602591/20000000000000)⟩
def e371 : ℝ := (14519/50000000000000)
theorem h371 : Model (fun x => f371 ((59/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(545194003875761/50000000000000),(2337192847509/50000000000000),(-2152362537/50000000000000),(602591/20000000000000)⟩
def e372 : ℝ := (14519/50000000000000)
theorem h372 : Model (fun x => f372 ((59/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(12339972938941517/50000000000000),(530778318234691/100000000000000),(4123521441287/100000000000000),(12221162313/100000000000000)⟩
def e373 : ℝ := (22148657/100000000000000)
theorem h373 : Model (fun x => f373 ((59/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(202593637147/50000000000000),(-8714144719/100000000000000),(29927949/25000000000000),(-1319263/100000000000000)⟩
def e374 : ℝ := (3379/25000000000000)
theorem h374 : Model (fun x => f374 ((59/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (12072515897448043/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(8579730502221/100000000000000),(421454642329/100000000000000),(-36659379/2500000000000),(1145161/20000000000000)⟩
def e375 : ℝ := (187267/25000000000000)
theorem h375 : Model (fun x => f375 ((59/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(117917090484589/50000000000000),(459210847201/25000000000000),(-252023319/10000000000000),(432233/12500000000000)⟩
def e376 : ℝ := (3357/50000000000000)
theorem h376 : Model (fun x => f376 ((59/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(45889012090619/100000000000000),(-96700685901/50000000000000),(16882103/1562500000000),(-3018029/50000000000000)⟩
def e377 : ℝ := (17061/50000000000000)
theorem h377 : Model (fun x => f377 ((59/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (216997406941303/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(54110987909379/50000000000000),(386802743601/100000000000000),(-540227297/25000000000000),(2414423/20000000000000)⟩
def e378 : ℝ := (28647/12500000000000)
theorem h378 : Model (fun x => f378 ((59/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(4110987909379/50000000000000),(386802743601/100000000000000),(-540227297/25000000000000),(2414423/20000000000000)⟩
def e379 : ℝ := (28647/12500000000000)
theorem h379 : Model (fun x => f379 ((59/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(49923828130677/12500000000000),(142748631567/10000000000000),(-7974783909/100000000000000),(11137963/25000000000000)⟩
def e380 : ℝ := (211443/25000000000000)
theorem h380 : Model (fun x => f380 ((59/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2755104910759701/100000000000000),(142748631567/10000000000000),(-7974783909/100000000000000),(11137963/25000000000000)⟩
def e381 : ℝ := (845773/100000000000000)
theorem h381 : Model (fun x => f381 ((59/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(2981628970303777/100000000000000),(381302352477/3125000000000),(-15661056909/25000000000000),(319120961/100000000000000)⟩
def e382 : ℝ := (7754849/100000000000000)
theorem h382 : Model (fun x => f382 ((59/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8264009922684729/100000000000000),(381302352477/3125000000000),(-15661056909/25000000000000),(319120961/100000000000000)⟩
def e383 : ℝ := (155097/2000000000000)
theorem h383 : Model (fun x => f383 ((59/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(8943474820187629/100000000000000),(45170311182611/100000000000000),(-12448509741/6250000000000),(837023077/100000000000000)⟩
def e384 : ℝ := (6293081/20000000000000)
theorem h384 : Model (fun x => f384 ((59/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(888282652452203/6250000000000),(45170311182611/100000000000000),(-12448509741/6250000000000),(837023077/100000000000000)⟩
def e385 : ℝ := (15732703/50000000000000)
theorem h385 : Model (fun x => f385 ((59/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(3845268149356181/25000000000000),(25964657493793/25000000000000),(-86988017879/25000000000000),(35003469/4000000000000)⟩
def e386 : ℝ := (79887437/100000000000000)
theorem h386 : Model (fun x => f386 ((59/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(17716786883139009/100000000000000),(25964657493793/25000000000000),(-86988017879/25000000000000),(35003469/4000000000000)⟩
def e387 : ℝ := (39943719/50000000000000)
theorem h387 : Model (fun x => f387 ((59/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(19173456816531587/100000000000000),(180926879159347/100000000000000),(-357676252063/100000000000000),(-252175903/50000000000000)⟩
def e388 : ℝ := (151110693/100000000000000)
theorem h388 : Model (fun x => f388 ((59/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(19575837768912539/100000000000000),(180926879159347/100000000000000),(-357676252063/100000000000000),(-252175903/50000000000000)⟩
def e389 : ℝ := (75555347/50000000000000)
theorem h389 : Model (fun x => f389 ((59/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(21185358416591823/100000000000000),(2121269695207/781250000000),(-55135125747/50000000000000),(-1737884477/50000000000000)⟩
def e390 : ℝ := (59263401/25000000000000)
theorem h390 : Model (fun x => f390 ((59/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(846709574758911/4000000000000),(2121269695207/781250000000),(-55135125747/50000000000000),(-1737884477/50000000000000)⟩
def e391 : ℝ := (47410721/20000000000000)
theorem h391 : Model (fun x => f391 ((59/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(22908145781267433/100000000000000),(375724433641983/100000000000000),(473504290847/100000000000000),(-375001773/5000000000000)⟩
def e392 : ℝ := (4104741/1250000000000)
theorem h392 : Model (fun x => f392 ((59/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(11455739557300383/50000000000000),(375724433641983/100000000000000),(473504290847/100000000000000),(-375001773/5000000000000)⟩
def e393 : ℝ := (328379281/100000000000000)
theorem h393 : Model (fun x => f393 ((59/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(235472034065283/12500000000000),(23902840378811/20000000000000),(498573784353/50000000000000),(-258642951/6250000000000)⟩
def e394 : ℝ := (1759641/2000000000000)
theorem h394 : Model (fun x => f394 ((59/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(58559980250579/50000000000000),(209302785823/25000000000000),(-1590496807/50000000000000),(188249/2000000000000)⟩
def e395 : ℝ := (19951/3125000000000)
theorem h395 : Model (fun x => f395 ((59/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(104110987909379/50000000000000),(386802743601/100000000000000),(-540227297/25000000000000),(2414423/20000000000000)⟩
def e396 : ℝ := (28647/12500000000000)
theorem h396 : Model (fun x => f396 ((59/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(216781956069337/50000000000000),(805408315247/50000000000000),(-750281199/10000000000000),(838917/2500000000000)⟩
def e397 : ℝ := (68549/6250000000000)
theorem h397 : Model (fun x => f397 ((59/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(3611101377169/400000000000),(5031111322247/100000000000000),(-938037143/5000000000000),(14595837/25000000000000)⟩
def e398 : ℝ := (377337/10000000000000)
theorem h398 : Model (fun x => f398 ((59/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(939888329544959/50000000000000),(13967839201099/100000000000000),(-9777917049/25000000000000),(49266223/100000000000000)⟩
def e399 : ℝ := (1119431/10000000000000)
theorem h399 : Model (fun x => f399 ((59/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2201593680636099/100000000000000),(6419365482819/20000000000000),(11337160443/100000000000000),(-537129699/100000000000000)⟩
def e400 : ℝ := (14135971/50000000000000)
theorem h400 : Model (fun x => f400 ((59/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(54110987909379/6250000000000),(386802743601/12500000000000),(-540227297/3125000000000),(2414423/2500000000000)⟩
def e401 : ℝ := (28647/1562500000000)
theorem h401 : Model (fun x => f401 ((59/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(491447883525611/50000000000000),(39316330921/1000000000000),(-10234133559/50000000000000),(10598937/10000000000000)⟩
def e402 : ℝ := (15449/625000000000)
theorem h402 : Model (fun x => f402 ((59/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(541447883525611/50000000000000),(39316330921/1000000000000),(-10234133559/50000000000000),(10598937/10000000000000)⟩
def e403 : ℝ := (15449/625000000000)
theorem h403 : Model (fun x => f403 ((59/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(4768192955055103/20000000000000),(217066885563221/50000000000000),(467035521631/50000000000000),(-4803514161/50000000000000)⟩
def e404 : ℝ := (186594921/50000000000000)
theorem h404 : Model (fun x => f404 ((59/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(419446112783/100000000000000),(-3818967153/50000000000000),(122649933/100000000000000),(-882567/50000000000000)⟩
def e405 : ℝ := (31647/100000000000000)
theorem h405 : Model (fun x => f405 ((59/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (23405886952887647/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(7901426348623/100000000000000),(3574160799/1000000000000),(-329433647/12500000000000),(19813551/100000000000000)⟩
def e406 : ℝ := (1603423/100000000000000)
theorem h406 : Model (fun x => f406 ((59/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(4120289212711/25000000000000),(778870722229/100000000000000),(-256365271/6250000000000),(6384839/25000000000000)⟩
def e407 : ℝ := (2352491/100000000000000)
theorem h407 : Model (fun x => f407 ((59/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(50438633932781/50000000000000),(2438543072209/50000000000000),(-18656744747/100000000000000),(37278103/20000000000000)⟩
def e408 : ℝ := (3313163/20000000000000)
theorem h408 : Model (fun x => f408 ((59/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(2137230251389/3125000000000),(2147323351393/100000000000000),(-12260987887/25000000000000),(191523973/20000000000000)⟩
def e409 : ℝ := (1970909/5000000000000)
theorem h409 : Model (fun x => f409 ((59/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-92499912403/2500000000000),(-20701990029/100000000000000),(153076847/3125000000000),(-137208673/100000000000000)⟩
def e410 : ℝ := (128857447/50000000000000)
theorem h410 : Model (fun x => f410 ((59/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1171502674804687/100000000000000),(22814317626953/25000000000000),(288923/10240000),(177/409600)⟩
def e411 : ℝ := (328125001/100000000000000)
theorem h411 : Model (fun x => f411 ((59/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(32041/1600),(179/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((59/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(5735339/64000),(96123/64000),(537/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((59/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(20996765560661371/20000000000000),(9937495846675857/100000000000000),(199869976177581/50000000000000),(4447106191589/50000000000000)⟩
def e414 : ℝ := (30077569737/25000000000000)
theorem h414 : Model (fun x => f414 ((59/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(23813191539/25000000000000),(-2254094721/25000000000000),(245389659/50000000000000),(-315541/1562500000000)⟩
def e415 : ℝ := (534603/50000000000000)
theorem h415 : Model (fun x => f415 ((59/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (9463757748161371/10000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(4750030495159/100000000000000),(103560296891/100000000000000),(-434784161/10000000000000),(108802779/100000000000000)⟩
def e416 : ℝ := (111305253/100000000000000)
theorem h416 : Model (fun x => f416 ((59/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(1050033999039/100000000000000),(41429153431/50000000000000),(275308747/50000000000000),(-14202947/50000000000000)⟩
def e417 : ℝ := (369020147/100000000000000)
theorem h417 : Model (fun x => f417 ((59/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((59/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((314954555417/600000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (29/20) (3/2) ∧
    SigmaActualBlockSeparable.endpointCellMass (29/20) (3/2) ≤ (787939918763/1500000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(59/40)-(1/40)) (by norm_num : ((59/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel9

