import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel37
open Hf4Quad.Dag

def p0 : Cubic := ⟨(23/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((23/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((23/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((23/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((23/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(503809523809523/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((23/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-503809523809523/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((23/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-51547619047619/12500000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((23/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((23/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(529/64),(23/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((23/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(1000621693121693/100000000000000),(4350529100529/25000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/100000000000000)
theorem h9 : Model (fun x => f9 ((23/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-1000621693121693/100000000000000),(-4350529100529/25000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/100000000000000)
theorem h10 : Model (fun x => f10 ((23/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-282600529100529/20000000000000),(-5445767195767/25000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((23/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((23/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(12167/512),(1587/2560),(69/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((23/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(2893997169777199/12500000000000),(603964626736111/100000000000000),(1312966579861/25000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((23/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-2893997169777199/12500000000000),(-603964626736111/100000000000000),(-1312966579861/25000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((23/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-24564980003720237/100000000000000),(-625747695519179/100000000000000),(-1065505539021/20000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((23/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((23/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(279841/4096),(12167/5120),(1587/51200),(23/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((23/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(19086377728174603/100000000000000),(663874007936507/100000000000000),(2164806547619/25000000000000),(25099206349/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((23/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-2739301137772817/50000000000000),(2382894526083/6250000000000),(3331698495371/100000000000000),(34975611773/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((23/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((23/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(19642160034179687/100000000000000),(213501739501953/25000000000000),(12167/81920),(529/409600)⟩
def e22 : ℝ := (562500001/100000000000000)
theorem h22 : Model (fun x => f22 ((23/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(63982517592818647/50000000000000),(5563697181984227/100000000000000),(9675995099103/10000000000000),(420695439091/50000000000000)⟩
def e23 : ℝ := (1832291671/50000000000000)
theorem h23 : Model (fun x => f23 ((23/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(6124321645504583/5000000000000),(1120364698880311/20000000000000),(100091649486401/100000000000000),(175273297991/20000000000000)⟩
def e24 : ℝ := (754742067/20000000000000)
theorem h24 : Model (fun x => f24 ((23/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((23/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(282356050491333/500000000000),(2946324005126951/100000000000000),(12810104370117/20000000000000),(742614746093/100000000000000)⟩
def e26 : ℝ := (4860009771/100000000000000)
theorem h26 : Model (fun x => f26 ((23/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(1585078145879917/1250000000000),(3307989174010259/50000000000000),(143825616261313/100000000000000),(1667543376941/100000000000000)⟩
def e27 : ℝ := (852591/7812500000)
theorem h27 : Model (fun x => f27 ((23/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(12464634229024251/5000000000000),(12217801842422073/100000000000000),(121958632873857/50000000000000),(158994366681/6250000000000)⟩
def e28 : ℝ := (2937375027/20000000000000)
theorem h28 : Model (fun x => f28 ((23/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((23/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(6494189161300659/4000000000000),(9882461767196649/100000000000000),(51560670089721/20000000000000),(1868140220641/50000000000000)⟩
def e30 : ℝ := (32659396989/100000000000000)
theorem h30 : Model (fun x => f30 ((23/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(19263517452667629/50000000000000),(1172561931901507/50000000000000),(61177144273121/100000000000000),(22165631983/2500000000000)⟩
def e31 : ℝ := (1937531687/25000000000000)
theorem h31 : Model (fun x => f31 ((23/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(143909859742910139/50000000000000),(14562925706225087/100000000000000),(61018882004167/20000000000000),(428816893277/12500000000000)⟩
def e32 : ℝ := (22437001883/100000000000000)
theorem h32 : Model (fun x => f32 ((23/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((23/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1134705/64),(9867/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((23/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((23/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(50807/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((23/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1947617/64),(67007/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((23/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((23/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(2093537/64),(67007/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((23/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-2093537/64),(-67007/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((23/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((23/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(31/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((23/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(961/64),(31/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((23/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((23/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(100905/32),(651/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((23/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(31712997373/100000000000000),(-409199967/100000000000000),(3959999/100000000000000),(-6813/20000000000000)⟩
def e46 : ℝ := (283/100000000000000)
theorem h46 : Model (fun x => f46 ((23/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (248997/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-518690104541237/50000000000000),(104346020691/100000000000000),(-682417587/100000000000000),(2239327/50000000000000)⟩
def e47 : ℝ := (9189631/50000000000000)
theorem h47 : Model (fun x => f47 ((23/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((23/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(39/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((23/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((23/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((23/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(81249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((23/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(131249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((23/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((23/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(131249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((23/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((23/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2756249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((23/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((23/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(31249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((23/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(172265624999993/20000000000000),(14218749999977/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (139/100000000000000)
theorem h60 : Model (fun x => f60 ((23/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(172265624999997/100000000000000),(546874999999/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((23/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((23/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(131249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((23/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1484765624999987/100000000000000),(2630208333329/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((23/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1584765624999987/100000000000000),(2630208333329/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((23/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(3412508010864091/25000000000000),(528600215911/195312500000),(670349121089/50000000000000),(2164713541/100000000000000)⟩
def e66 : ℝ := (1017/160000000000)
theorem h66 : Model (fun x => f66 ((23/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(231249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((23/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(106953124999999/20000000000000),(192708333333/10000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((23/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1236645507812483/100000000000000),(835571289061/12500000000000),(12044270833/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (69/100000000000000)
theorem h69 : Model (fun x => f69 ((23/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(84401254040183801/50000000000000),(2129672165844711/50000000000000),(36315073802841/100000000000000),(9373386139/6250000000000)⟩
def e70 : ℝ := (334027377/100000000000000)
theorem h70 : Model (fun x => f70 ((23/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((23/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3617578124999937/12500000000000),(11484374999979/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((23/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(9043945312499553/100000000000000),(89003906249849/50000000000000),(214192708331/25000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (903/50000000000000)
theorem h73 : Model (fun x => f73 ((23/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(111841543436043349/100000000000000),(1402937250134889/50000000000000),(11791776339119/50000000000000),(47197045201/50000000000000)⟩
def e74 : ℝ := (197541877/100000000000000)
theorem h74 : Model (fun x => f74 ((23/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(280644051516410951/100000000000000),(8831523539949/125000000000),(59898626481079/100000000000000),(122184134313/50000000000000)⟩
def e75 : ℝ := (265784627/50000000000000)
theorem h75 : Model (fun x => f75 ((23/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((23/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1205859374999979/12500000000000),(3828124999993/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((23/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(9765624999999/100000000000000),(130208333333/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((23/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(3051757812499/100000000000000),(122070312499/100000000000000),(813802083/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((23/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(294399261474507/100000000000000),(13645172119039/100000000000000),(58686998139/25000000000000),(45335557/2500000000000)⟩
def e80 : ℝ := (3010269/50000000000000)
theorem h80 : Model (fun x => f80 ((23/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(340399146079897/50000000000000),(512205064293/1562500000000),(299854808307/50000000000000),(2585827829/50000000000000)⟩
def e81 : ℝ := (21503521/100000000000000)
theorem h81 : Model (fun x => f81 ((23/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(56264969961714149/20000000000000),(221812498627311/3125000000000),(60498336097693/100000000000000),(62384981071/25000000000000)⟩
def e82 : ℝ := (22122911/4000000000000)
theorem h82 : Model (fun x => f82 ((23/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(190734863281/20000000000000),(50862630207/100000000000000),(1017252603/100000000000000),(1808449/20000000000000)⟩
def e83 : ℝ := (15073/50000000000000)
theorem h83 : Model (fun x => f83 ((23/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(74505805969/25000000000000),(4967053731/25000000000000),(66227383/12500000000000),(3532127/50000000000000)⟩
def e84 : ℝ := (5903/12500000000000)
theorem h84 : Model (fun x => f84 ((23/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(93132257461/100000000000000),(1862645149/25000000000000),(124176343/50000000000000),(2207579/50000000000000)⟩
def e85 : ℝ := (44391/100000000000000)
theorem h85 : Model (fun x => f85 ((23/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(3637978807/12500000000000),(2716357509/100000000000000),(1086543/1000000000000),(2414539/100000000000000)⟩
def e86 : ℝ := (4057/12500000000000)
theorem h86 : Model (fun x => f86 ((23/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(10913936421/12500000000000),(8149072527/100000000000000),(3259629/1000000000000),(7243617/100000000000000)⟩
def e87 : ℝ := (12171/12500000000000)
theorem h87 : Model (fun x => f87 ((23/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-10913936421/12500000000000),(-8149072527/100000000000000),(-3259629/1000000000000),(-7243617/100000000000000)⟩
def e88 : ℝ := (12171/12500000000000)
theorem h88 : Model (fun x => f88 ((23/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(281324762497079377/100000000000000),(283919672280057/4000000000000),(60498010134793/100000000000000),(249532680667/100000000000000)⟩
def e89 : ℝ := (553170143/100000000000000)
theorem h89 : Model (fun x => f89 ((23/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3617578124999937/10000000000000),(11484374999979/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((23/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1429871368408177/50000000000000),(4122151692701/20000000000000),(55704752603/100000000000000),(13382523/20000000000000)⟩
def e91 : ℝ := (1897/6250000000000)
theorem h91 : Model (fun x => f91 ((23/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(51726713839171471/5000000000000),(438267952948011/3125000000000),(38959055343633/50000000000000),(56824101273/25000000000000)⟩
def e92 : ℝ := (92036649/25000000000000)
theorem h92 : Model (fun x => f92 ((23/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(4833092641/50000000000000),(-65519403/50000000000000),(1048387/100000000000000),(-6467/100000000000000)⟩
def e93 : ℝ := (11/25000000000000)
theorem h93 : Model (fun x => f93 ((23/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (510215778256927057/50000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(13596686393557/50000000000000),(317460429607/100000000000000),(-20156069/4000000000000),(266393/25000000000000)⟩
def e94 : ℝ := (334207/100000000000000)
theorem h94 : Model (fun x => f94 ((23/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(81249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((23/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(19047619047619/50000000000000),(-24187452759/20000000000000),(383927821/100000000000000),(-1218819/100000000000000)⟩
def e96 : ℝ := (777/20000000000000)
theorem h96 : Model (fun x => f96 ((23/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (261666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(123809523809521/100000000000000),(120937263793/50000000000000),(-153571129/20000000000000),(487527/20000000000000)⟩
def e97 : ℝ := (8253/25000000000000)
theorem h97 : Model (fun x => f97 ((23/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2599999999999941/100000000000000),(2539682539653/50000000000000),(-3224993709/20000000000000),(10238067/20000000000000)⟩
def e98 : ℝ := (173313/25000000000000)
theorem h98 : Model (fun x => f98 ((23/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(23809523809521/100000000000000),(120937263793/50000000000000),(-153571129/20000000000000),(487527/20000000000000)⟩
def e99 : ℝ := (8253/25000000000000)
theorem h99 : Model (fun x => f99 ((23/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(619047619047531/100000000000000),(1499622071033/20000000000000),(-5758917353/50000000000000),(-1218849/50000000000000)⟩
def e100 : ℝ := (21859/1562500000000)
theorem h100 : Model (fun x => f100 ((23/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(153287981859403/100000000000000),(598927401641/100000000000000),(-263264793/20000000000000),(1160777/50000000000000)⟩
def e101 : ℝ := (6227/6250000000000)
theorem h101 : Model (fun x => f101 ((23/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(123809523809521/10000000000000),(120937263793/5000000000000),(-153571129/2000000000000),(487527/2000000000000)⟩
def e102 : ℝ := (8253/2500000000000)
theorem h102 : Model (fun x => f102 ((23/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1391383219954613/100000000000000),(3017672677501/100000000000000),(-1798976083/20000000000000),(1668619/6250000000000)⟩
def e103 : ℝ := (53719/12500000000000)
theorem h103 : Model (fun x => f103 ((23/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1491383219954613/100000000000000),(3017672677501/100000000000000),(-1798976083/20000000000000),(1668619/6250000000000)⟩
def e104 : ℝ := (53719/12500000000000)
theorem h104 : Model (fun x => f104 ((23/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(4616186157001717/50000000000000),(130506390511327/100000000000000),(-297304909/25000000000000),(-893099291/100000000000000)⟩
def e105 : ℝ := (26566229/100000000000000)
theorem h105 : Model (fun x => f105 ((23/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(223809523809521/100000000000000),(120937263793/50000000000000),(-153571129/20000000000000),(487527/20000000000000)⟩
def e106 : ℝ := (8253/25000000000000)
theorem h106 : Model (fun x => f106 ((23/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(100181405895689/20000000000000),(1082676456813/100000000000000),(-570407051/20000000000000),(899603/12500000000000)⟩
def e107 : ℝ := (20707/12500000000000)
theorem h107 : Model (fun x => f107 ((23/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(280269409351031/25000000000000),(3634699533587/100000000000000),(-380532543/5000000000000),(13105723/100000000000000)⟩
def e108 : ℝ := (602699/100000000000000)
theorem h108 : Model (fun x => f108 ((23/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(2070041228283643/2000000000000),(899323476420941/50000000000000),(4027539468903/100000000000000),(-9388988791/50000000000000)⟩
def e109 : ℝ := (185280383/50000000000000)
theorem h109 : Model (fun x => f109 ((23/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(3219047619047463/12500000000000),(12577475434461/12500000000000),(-5528560653/2500000000000),(24376317/6250000000000)⟩
def e110 : ℝ := (130767/781250000000)
theorem h110 : Model (fun x => f110 ((23/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1532879818593849/25000000000000),(1347586653693/1562500000000),(-140407903/2000000000000),(-586890829/100000000000000)⟩
def e111 : ℝ := (17663117/100000000000000)
theorem h111 : Model (fun x => f111 ((23/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(537024151704267/781250000000),(237948366019197/20000000000000),(2589413847783/100000000000000),(-6297469777/50000000000000)⟩
def e112 : ℝ := (122836599/50000000000000)
theorem h112 : Model (fun x => f112 ((23/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(86120576416164163/50000000000000),(2988388782937867/100000000000000),(3308476658343/50000000000000),(-1960807321/6250000000000)⟩
def e113 : ℝ := (154058491/25000000000000)
theorem h113 : Model (fun x => f113 ((23/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(1073015873015821/12500000000000),(4192491811487/12500000000000),(-1842853551/2500000000000),(8125439/6250000000000)⟩
def e114 : ℝ := (43589/781250000000)
theorem h114 : Model (fun x => f114 ((23/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(5668934240361/100000000000000),(115178346469/100000000000000),(8775493/4000000000000),(-638429/25000000000000)⟩
def e115 : ℝ := (4201/12500000000000)
theorem h115 : Model (fun x => f115 ((23/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(168718280963/12500000000000),(20567561869/50000000000000),(287292927/100000000000000),(-411801/50000000000000)⟩
def e116 : ℝ := (603/4000000000000)
theorem h116 : Model (fun x => f116 ((23/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(57931965933197/50000000000000),(1991897632017/50000000000000),(18731664679/50000000000000),(-2908821/100000000000000)⟩
def e117 : ℝ := (90613/5000000000000)
theorem h117 : Model (fun x => f117 ((23/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(64828628544291/25000000000000),(367854341913/4000000000000),(11574077159/12500000000000),(2253543/4000000000000)⟩
def e118 : ℝ := (268657/6250000000000)
theorem h118 : Model (fun x => f118 ((23/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(17250046734650549/10000000000000),(749396285371423/25000000000000),(3354772966979/50000000000000),(-31316578561/100000000000000)⟩
def e119 : ℝ := (155133119/25000000000000)
theorem h119 : Model (fun x => f119 ((23/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(64273630843/20000000000000),(81617309/625000000000),(157534361/100000000000000),(53959/25000000000000)⟩
def e120 : ℝ := (57/781250000000)
theorem h120 : Model (fun x => f120 ((23/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(38258113597/50000000000000),(3886538523/100000000000000),(33313187/50000000000000),(169993/50000000000000)⟩
def e121 : ℝ := (2239/100000000000000)
theorem h121 : Model (fun x => f121 ((23/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(18218149331/100000000000000),(555219789/50000000000000),(12338217/50000000000000),(214123/100000000000000)⟩
def e122 : ℝ := (487/50000000000000)
theorem h122 : Model (fun x => f122 ((23/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(2168827301/50000000000000),(154227719/50000000000000),(4210661/50000000000000),(20517/20000000000000)⟩
def e123 : ℝ := (3/500000000000)
theorem h123 : Model (fun x => f123 ((23/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(6506481903/50000000000000),(462683157/50000000000000),(12631983/50000000000000),(61551/20000000000000)⟩
def e124 : ℝ := (9/500000000000)
theorem h124 : Model (fun x => f124 ((23/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-6506481903/50000000000000),(-462683157/50000000000000),(-12631983/50000000000000),(-61551/20000000000000)⟩
def e125 : ℝ := (9/500000000000)
theorem h125 : Model (fun x => f125 ((23/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(43125113583385421/25000000000000),(1498792108059689/50000000000000),(838690083749/12500000000000),(-7829221579/25000000000000)⟩
def e126 : ℝ := (155133569/25000000000000)
theorem h126 : Model (fun x => f126 ((23/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(3219047619047463/10000000000000),(12577475434461/10000000000000),(-5528560653/2000000000000),(24376317/5000000000000)⟩
def e127 : ℝ := (130767/625000000000)
theorem h127 : Model (fun x => f127 ((23/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1254539260904599/50000000000000),(10846404957371/100000000000000),(-16850207047/100000000000000),(2068433/20000000000000)⟩
def e128 : ℝ := (1900681/100000000000000)
theorem h128 : Model (fun x => f128 ((23/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(403842162081651339/50000000000000),(3323648376221931/50000000000000),(1282080907363/100000000000000),(-3561419951/10000000000000)⟩
def e129 : ℝ := (125405087/10000000000000)
theorem h129 : Model (fun x => f129 ((23/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(309526869/2500000000000),(-20379417/20000000000000),(409483/50000000000000),(-6033/100000000000000)⟩
def e130 : ℝ := (33/50000000000000)
theorem h130 : Model (fun x => f130 ((23/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (801035708461701073/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(170859281699/800000000000),(97680104107/50000000000000),(-12672189/1562500000000),(342807/10000000000000)⟩
def e131 : ℝ := (287949/100000000000000)
theorem h131 : Model (fun x => f131 ((23/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(48550782999489/100000000000000),(512820637821/100000000000000),(-1314921821/100000000000000),(2246821/50000000000000)⟩
def e132 : ℝ := (155539/25000000000000)
theorem h132 : Model (fun x => f132 ((23/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-251828107095639/50000000000000),(-1317309748693/25000000000000),(6922263791/50000000000000),(-49313379/100000000000000)⟩
def e133 : ℝ := (15509271/100000000000000)
theorem h133 : Model (fun x => f133 ((23/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(8695652173913/25000000000000),(-302457466919/100000000000000),(2630064929/100000000000000),(-2287013/10000000000000)⟩
def e134 : ℝ := (200617/100000000000000)
theorem h134 : Model (fun x => f134 ((23/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (57/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-10949048134593/6250000000000),(-38679119171/12500000000000),(7506209191/100000000000000),(-82423863/100000000000000)⟩
def e135 : ℝ := (81857/1000000000000)
theorem h135 : Model (fun x => f135 ((23/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(1399205/2048),(12167/512),(1587/5120),(23/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((23/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((23/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(109503/256),(14283/1280),(621/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((23/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(2275229/2048),(89401/2560),(10419/25600),(133/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((23/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-529/64),(-23/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((23/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(2258301/2048),(89033/2560),(10403/25600),(133/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((23/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((23/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(69/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((23/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-69/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((23/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(2222973/2048),(88649/2560),(10403/25600),(133/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((23/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(2229117/2048),(88649/2560),(10403/25600),(133/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((23/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((23/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(2229117/32),(88649/40),(10403/400),(133/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((23/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((23/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(264449745/4096),(2299563/1024),(299943/10240),(4347/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((23/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1548876517/100000000000000),(-26936983/50000000000000),(1171173/100000000000000),(-20369/100000000000000)⟩
def e151 : ℝ := (87/25000000000000)
theorem h151 : Model (fun x => f151 ((23/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (15945676173/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(53947296483523/50000000000000),(-80049140497/25000000000000),(24693771/1000000000000),(-18446343/100000000000000)⟩
def e152 : ℝ := (47647911/100000000000000)
theorem h152 : Model (fun x => f152 ((23/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(47/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((23/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(1833/64),(43/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((23/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(93/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((23/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(4301075268817/100000000000000),(-27748872703/100000000000000),(35804997/20000000000000),(-231/20000000000)⟩
def e156 : ℝ := (3751/50000000000000)
theorem h156 : Model (fun x => f156 ((23/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (231/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(123185483870961/100000000000000),(72233784247/20000000000000),(71609993/20000000000000),(-2310003/100000000000000)⟩
def e157 : ℝ := (208061/50000000000000)
theorem h157 : Model (fun x => f157 ((23/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(223185483870961/100000000000000),(72233784247/20000000000000),(71609993/20000000000000),(-2310003/100000000000000)⟩
def e158 : ℝ := (208061/50000000000000)
theorem h158 : Model (fun x => f158 ((23/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(2789818548387/2500000000000),(180584460617/100000000000000),(89512491/50000000000000),(-577501/50000000000000)⟩
def e159 : ℝ := (208063/100000000000000)
theorem h159 : Model (fun x => f159 ((23/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(289818548387/2500000000000),(180584460617/100000000000000),(89512491/50000000000000),(-577501/50000000000000)⟩
def e160 : ℝ := (208063/100000000000000)
theorem h160 : Model (fun x => f160 ((23/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((23/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((23/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(205915178571421/50000000000000),(666442652277/100000000000000),(660687433/100000000000000),(-1065627/25000000000000)⟩
def e163 : ℝ := (383927/50000000000000)
theorem h163 : Model (fun x => f163 ((23/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2767544642857127/100000000000000),(666442652277/100000000000000),(660687433/100000000000000),(-1065627/25000000000000)⟩
def e164 : ℝ := (153571/20000000000000)
theorem h164 : Model (fun x => f164 ((23/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((23/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(617675790250551/20000000000000),(5741457194741/100000000000000),(6895367389/100000000000000),(-1072989/3125000000000)⟩
def e166 : ℝ := (6632113/100000000000000)
theorem h166 : Model (fun x => f166 ((23/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8370759903633707/100000000000000),(5741457194741/100000000000000),(6895367389/100000000000000),(-1072989/3125000000000)⟩
def e167 : ℝ := (3316057/50000000000000)
theorem h167 : Model (fun x => f167 ((23/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((23/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(2335290124325149/25000000000000),(2690417641523/12500000000000),(33048660453/100000000000000),(-112267931/100000000000000)⟩
def e169 : ℝ := (24957479/100000000000000)
theorem h169 : Model (fun x => f169 ((23/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(2922041623269643/20000000000000),(2690417641523/12500000000000),(33048660453/100000000000000),(-112267931/100000000000000)⟩
def e170 : ℝ := (623937/2500000000000)
theorem h170 : Model (fun x => f170 ((23/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((23/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(16303931839513017/100000000000000),(50402252047459/100000000000000),(101903638313/100000000000000),(-48954539/25000000000000)⟩
def e172 : ℝ := (58731893/100000000000000)
theorem h172 : Model (fun x => f172 ((23/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(9319823062613651/50000000000000),(50402252047459/100000000000000),(101903638313/100000000000000),(-48954539/25000000000000)⟩
def e173 : ℝ := (29365947/50000000000000)
theorem h173 : Model (fun x => f173 ((23/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((23/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(52001230495529/250000000000),(1798111189463/2000000000000),(59526330561/25000000000000),(-159552377/100000000000000)⟩
def e175 : ℝ := (105288849/100000000000000)
theorem h175 : Model (fun x => f175 ((23/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(2650359143824069/12500000000000),(1798111189463/2000000000000),(59526330561/25000000000000),(-159552377/100000000000000)⟩
def e176 : ℝ := (2105777/2000000000000)
theorem h176 : Model (fun x => f176 ((23/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((23/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(5915216879461981/25000000000000),(69308586541413/50000000000000),(466022167267/100000000000000),(83996071/50000000000000)⟩
def e178 : ℝ := (81445619/50000000000000)
theorem h178 : Model (fun x => f178 ((23/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(5910812117557219/25000000000000),(69308586541413/50000000000000),(466022167267/100000000000000),(83996071/50000000000000)⟩
def e179 : ℝ := (162891239/100000000000000)
theorem h179 : Model (fun x => f179 ((23/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((23/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(1649009328159177/6250000000000),(1579061895671/800000000000),(203173827533/25000000000000),(1004110031/100000000000000)⟩
def e181 : ℝ := (7250623/3125000000000)
theorem h181 : Model (fun x => f181 ((23/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(5277496516776033/20000000000000),(1579061895671/800000000000),(203173827533/25000000000000),(1004110031/100000000000000)⟩
def e182 : ℝ := (232019937/100000000000000)
theorem h182 : Model (fun x => f182 ((23/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(3059032759218957/100000000000000),(35266882207667/50000000000000),(497896406859/100000000000000),(204074223/12500000000000)⟩
def e183 : ℝ := (83627867/100000000000000)
theorem h183 : Model (fun x => f183 ((23/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(62264700263393/50000000000000),(403038302223/100000000000000),(362832623/50000000000000),(-386243/20000000000000)⟩
def e184 : ℝ := (468977/100000000000000)
theorem h184 : Model (fun x => f184 ((23/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(5289818548387/2500000000000),(180584460617/100000000000000),(89512491/50000000000000),(-577501/50000000000000)⟩
def e185 : ℝ := (208063/100000000000000)
theorem h185 : Model (fun x => f185 ((23/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(223857442198873/50000000000000),(764207223457/100000000000000),(108371521/10000000000000),(-4241219/100000000000000)⟩
def e186 : ℝ := (885103/100000000000000)
theorem h186 : Model (fun x => f186 ((23/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(189466439990091/20000000000000),(2425510527273/100000000000000),(4474623711/100000000000000),(-2164017/20000000000000)⟩
def e187 : ℝ := (2822103/100000000000000)
theorem h187 : Model (fun x => f187 ((23/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(2004486177112871/100000000000000),(3421469487061/50000000000000),(3886008851/25000000000000),(-5353369/25000000000000)⟩
def e188 : ℝ := (7992187/100000000000000)
theorem h188 : Model (fun x => f188 ((23/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(624043655000237/25000000000000),(8300158969709/50000000000000),(61482418717/100000000000000),(9385647/20000000000000)⟩
def e189 : ℝ := (19523753/100000000000000)
theorem h189 : Model (fun x => f189 ((23/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((23/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(2789818548387/312500000000),(180584460617/12500000000000),(89512491/6250000000000),(-577501/6250000000000)⟩
def e191 : ℝ := (208063/12500000000000)
theorem h191 : Model (fun x => f191 ((23/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(508635668005313/50000000000000),(1847713987159/100000000000000),(1078932551/50000000000000),(-11171231/100000000000000)⟩
def e192 : ℝ := (2133481/100000000000000)
theorem h192 : Model (fun x => f192 ((23/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(558635668005313/50000000000000),(1847713987159/100000000000000),(1078932551/50000000000000),(-11171231/100000000000000)⟩
def e193 : ℝ := (2133481/100000000000000)
theorem h193 : Model (fun x => f193 ((23/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(13944521763021379/50000000000000),(231592761621417/100000000000000),(2095031837/200000000000),(1739694003/100000000000000)⟩
def e194 : ℝ := (136225281/50000000000000)
theorem h194 : Model (fun x => f194 ((23/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(179281874451/50000000000000),(-2977540939/100000000000000),(1125803/10000000000000),(-2009/50000000000000)⟩
def e195 : ℝ := (377/10000000000000)
theorem h195 : Model (fun x => f195 ((23/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (6914100309089569/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2193716508319/20000000000000),(80912278593/50000000000000),(460799/1562500000000),(-57669/5000000000000)⟩
def e196 : ℝ := (425137/100000000000000)
theorem h196 : Model (fun x => f196 ((23/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(123185483870961/50000000000000),(72233784247/10000000000000),(71609993/10000000000000),(-2310003/50000000000000)⟩
def e197 : ℝ := (208061/25000000000000)
theorem h197 : Model (fun x => f197 ((23/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(11201445347787/25000000000000),(-36253378691/50000000000000),(4545313/10000000000000),(31657/6250000000000)⟩
def e198 : ℝ := (42729/50000000000000)
theorem h198 : Model (fun x => f198 ((23/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (55705988543409/25000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(110388437217701/100000000000000),(72506757381/50000000000000),(-45453131/50000000000000),(-1013027/100000000000000)⟩
def e199 : ℝ := (147999/25000000000000)
theorem h199 : Model (fun x => f199 ((23/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(10388437217701/100000000000000),(72506757381/50000000000000),(-45453131/50000000000000),(-1013027/100000000000000)⟩
def e200 : ℝ := (147999/25000000000000)
theorem h200 : Model (fun x => f200 ((23/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(407385899255801/100000000000000),(267584461763/50000000000000),(-83871849/25000000000000),(-3738553/100000000000000)⟩
def e201 : ℝ := (8739/400000000000)
theorem h201 : Model (fun x => f201 ((23/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1381550092485043/50000000000000),(267584461763/50000000000000),(-83871849/25000000000000),(-3738553/100000000000000)⟩
def e202 : ℝ := (2184751/100000000000000)
theorem h202 : Model (fun x => f202 ((23/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(3050143112947883/100000000000000),(183905332231/4000000000000),(-1053051561/50000000000000),(-16545443/50000000000000)⟩
def e203 : ℝ := (18786043/100000000000000)
theorem h203 : Model (fun x => f203 ((23/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1666504813065767/20000000000000),(183905332231/4000000000000),(-1053051561/50000000000000),(-16545443/50000000000000)⟩
def e204 : ℝ := (4696511/25000000000000)
theorem h204 : Model (fun x => f204 ((23/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(2299535774126337/25000000000000),(1072408848173/6250000000000),(-3232490829/100000000000000),(-64086451/50000000000000)⟩
def e205 : ℝ := (70213021/100000000000000)
theorem h205 : Model (fun x => f205 ((23/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14467190715552967/100000000000000),(1072408848173/6250000000000),(-3232490829/100000000000000),(-64086451/50000000000000)⟩
def e206 : ℝ := (35106511/50000000000000)
theorem h206 : Model (fun x => f206 ((23/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3194021148040651/20000000000000),(7984085526653/20000000000000),(510145363/6250000000000),(-308330349/100000000000000)⟩
def e207 : ℝ := (163712631/100000000000000)
theorem h207 : Model (fun x => f207 ((23/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(915291001295877/5000000000000),(7984085526653/20000000000000),(510145363/6250000000000),(-308330349/100000000000000)⟩
def e208 : ℝ := (20464079/12500000000000)
theorem h208 : Model (fun x => f208 ((23/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(505187716162383/2500000000000),(70613449220573/100000000000000),(10051828481/20000000000000),(-550257647/100000000000000)⟩
def e209 : ℝ := (290422621/100000000000000)
theorem h209 : Model (fun x => f209 ((23/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(1288118099929767/6250000000000),(70613449220573/100000000000000),(10051828481/20000000000000),(-550257647/100000000000000)⟩
def e210 : ℝ := (145211311/50000000000000)
theorem h210 : Model (fun x => f210 ((23/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(22750935040493021/100000000000000),(107836208356003/100000000000000),(17392955779/12500000000000),(-403757031/50000000000000)⟩
def e211 : ℝ := (222500727/50000000000000)
theorem h211 : Model (fun x => f211 ((23/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(22733315992873973/100000000000000),(107836208356003/100000000000000),(17392955779/12500000000000),(-403757031/50000000000000)⟩
def e212 : ℝ := (89000291/20000000000000)
theorem h212 : Model (fun x => f212 ((23/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(12547476126147633/50000000000000),(76002542851117/50000000000000),(18081847793/6250000000000),(-1017949557/100000000000000)⟩
def e213 : ℝ := (314743001/50000000000000)
theorem h213 : Model (fun x => f213 ((23/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(25098285585628599/100000000000000),(76002542851117/50000000000000),(18081847793/6250000000000),(-1017949557/100000000000000)⟩
def e214 : ℝ := (629486003/100000000000000)
theorem h214 : Model (fun x => f214 ((23/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(1303659820391163/50000000000000),(52186858968613/100000000000000),(113833373317/50000000000000),(-39322817/50000000000000)⟩
def e215 : ℝ := (109535323/50000000000000)
theorem h215 : Model (fun x => f215 ((23/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(121856070713663/100000000000000),(1600781527/500000000000),(958919/10000000000000),(-2500183/100000000000000)⟩
def e216 : ℝ := (81973/6250000000000)
theorem h216 : Model (fun x => f216 ((23/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(210388437217701/100000000000000),(72506757381/50000000000000),(-45453131/50000000000000),(-1013027/100000000000000)⟩
def e217 : ℝ := (147999/25000000000000)
theorem h217 : Model (fun x => f217 ((23/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(88526589029813/20000000000000),(152545833731/25000000000000),(-86111667/50000000000000),(-4526237/100000000000000)⟩
def e218 : ℝ := (62389/2500000000000)
theorem h218 : Model (fun x => f218 ((23/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(931248535909801/100000000000000),(481408193441/25000000000000),(60064627/50000000000000),(-14811113/100000000000000)⟩
def e219 : ℝ := (7890571/100000000000000)
theorem h219 : Model (fun x => f219 ((23/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1959239241313351/100000000000000),(2700872466183/50000000000000),(68706331/3125000000000),(-21085493/50000000000000)⟩
def e220 : ℝ := (22177763/100000000000000)
theorem h220 : Model (fun x => f220 ((23/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2387451955344631/100000000000000),(12854982093491/100000000000000),(4032206581/20000000000000),(-3712621/4000000000000)⟩
def e221 : ℝ := (53133507/100000000000000)
theorem h221 : Model (fun x => f221 ((23/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(110388437217701/12500000000000),(72506757381/6250000000000),(-45453131/6250000000000),(-1013027/12500000000000)⟩
def e222 : ℝ := (147999/3125000000000)
theorem h222 : Model (fun x => f222 ((23/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(1004963568455271/100000000000000),(185033052937/12500000000000),(-358830453/50000000000000),(-10604399/100000000000000)⟩
def e223 : ℝ := (377971/6250000000000)
theorem h223 : Model (fun x => f223 ((23/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1104963568455271/100000000000000),(185033052937/12500000000000),(-358830453/50000000000000),(-10604399/100000000000000)⟩
def e224 : ℝ := (377971/6250000000000)
theorem h224 : Model (fun x => f224 ((23/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(26380474320931177/100000000000000),(3547669415751/2000000000000),(98981496467/25000000000000),(-268142813/25000000000000)⟩
def e225 : ℝ := (735936733/100000000000000)
theorem h225 : Model (fun x => f225 ((23/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(379068241091/100000000000000),(-2548871543/100000000000000),(2289911/20000000000000),(-11661/50000000000000)⟩
def e226 : ℝ := (10843/100000000000000)
theorem h226 : Model (fun x => f226 ((23/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (13101346557824887/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(9883520701933/100000000000000),(65683290007/50000000000000),(-16863717/10000000000000),(-73397/10000000000000)⟩
def e227 : ℝ := (285099/25000000000000)
theorem h227 : Model (fun x => f227 ((23/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(2606512905441/12500000000000),(732977843/250000000000),(-69573017/50000000000000),(-37747/2000000000000)⟩
def e228 : ℝ := (1565533/100000000000000)
theorem h228 : Model (fun x => f228 ((23/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(2812286489959/12500000000000),(249569666409/100000000000000),(-574001927/100000000000000),(112671/6250000000000)⟩
def e229 : ℝ := (2955259/25000000000000)
theorem h229 : Model (fun x => f229 ((23/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(62603942733/800000000000),(18759076649/100000000000000),(-1451101/400000000000),(756321/20000000000000)⟩
def e230 : ℝ := (4271177/100000000000000)
theorem h230 : Model (fun x => f230 ((23/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-167359277311863/100000000000000),(-290673876719/100000000000000),(7143433941/100000000000000),(-39321129/50000000000000)⟩
def e231 : ℝ := (12456877/100000000000000)
theorem h231 : Model (fun x => f231 ((23/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((23/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2645/64),(-23/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((23/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(483/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((23/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1219/64),(-31/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((23/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((23/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2883/64),(-31/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((23/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((23/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(360375/32),(-775/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((23/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(575/64),(1/160),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((23/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(959/64),(1/160),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((23/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((23/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(181251/64),(189/160),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((23/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(8827537503/25000000000000),(-2945581/20000000000000),(1478933/100000000000000),(-77/6250000000000)⟩
def e244 : ℝ := (33/50000000000000)
theorem h244 : Model (fun x => f244 ((23/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1132299/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(397652978455453/100000000000000),(-1876196915093/100000000000000),(-10217344303/100000000000000),(-74004079/100000000000000)⟩
def e245 : ℝ := (1843227/100000000000000)
theorem h245 : Model (fun x => f245 ((23/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(207/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((23/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(3841/64),(19/32),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((23/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(5185/64),(19/32),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((23/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(1521/64),(39/160),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((23/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(7886385/4096),(34671/1024),(10763/51200),(67/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((23/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((23/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(43245/32),(279/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((23/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(4624812117/6250000000000),(-954799921/100000000000000),(9239999/100000000000000),(-19871/25000000000000)⟩
def e253 : ℝ := (327/50000000000000)
theorem h253 : Model (fun x => f253 ((23/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (106713/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(71236423647123/50000000000000),(667060381633/100000000000000),(1017843963/100000000000000),(-433241/20000000000000)⟩
def e254 : ℝ := (102851/4000000000000)
theorem h254 : Model (fun x => f254 ((23/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(121236423647123/50000000000000),(667060381633/100000000000000),(1017843963/100000000000000),(-433241/20000000000000)⟩
def e255 : ℝ := (102851/4000000000000)
theorem h255 : Model (fun x => f255 ((23/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(121236423647123/100000000000000),(10422818463/3125000000000),(508921981/100000000000000),(-1083103/100000000000000)⟩
def e256 : ℝ := (1285639/100000000000000)
theorem h256 : Model (fun x => f256 ((23/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(21236423647123/100000000000000),(10422818463/3125000000000),(508921981/100000000000000),(-1083103/100000000000000)⟩
def e257 : ℝ := (1285639/100000000000000)
theorem h257 : Model (fun x => f257 ((23/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(1747734901907/390625000000),(1230885228011/100000000000000),(1878164453/100000000000000),(-1998583/50000000000000)⟩
def e258 : ℝ := (2372311/50000000000000)
theorem h258 : Model (fun x => f258 ((23/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2803134420602477/100000000000000),(1230885228011/100000000000000),(1878164453/100000000000000),(-1998583/50000000000000)⟩
def e259 : ℝ := (4744623/100000000000000)
theorem h259 : Model (fun x => f259 ((23/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(679683984311989/20000000000000),(2168316162301/20000000000000),(10324080243/50000000000000),(-5669591/25000000000000)⟩
def e260 : ℝ := (41839247/100000000000000)
theorem h260 : Model (fun x => f260 ((23/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8680800873940897/100000000000000),(2168316162301/20000000000000),(10324080243/50000000000000),(-5669591/25000000000000)⟩
def e261 : ℝ := (2614953/6250000000000)
theorem h261 : Model (fun x => f261 ((23/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(10524292523494141/100000000000000),(42097036561893/100000000000000),(13171442533/12500000000000),(315823/12500000000000)⟩
def e262 : ℝ := (162695903/100000000000000)
theorem h262 : Model (fun x => f262 ((23/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(49354187945443/312500000000),(42097036561893/100000000000000),(13171442533/12500000000000),(315823/12500000000000)⟩
def e263 : ℝ := (5084247/3125000000000)
theorem h263 : Model (fun x => f263 ((23/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(19147280763243067/100000000000000),(1037124991027/1000000000000),(6970615857/2000000000000),(39769197/10000000000000)⟩
def e264 : ℝ := (401467941/100000000000000)
theorem h264 : Model (fun x => f264 ((23/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(2685374381119669/12500000000000),(1037124991027/1000000000000),(6970615857/2000000000000),(39769197/10000000000000)⟩
def e265 : ℝ := (200733971/50000000000000)
theorem h265 : Model (fun x => f265 ((23/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(13022607444822197/50000000000000),(197389599166947/100000000000000),(438895224349/50000000000000),(1939735681/100000000000000)⟩
def e266 : ℝ := (383788339/50000000000000)
theorem h266 : Model (fun x => f266 ((23/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(13223797921012673/50000000000000),(197389599166947/100000000000000),(438895224349/50000000000000),(1939735681/100000000000000)⟩
def e267 : ℝ := (767576679/100000000000000)
theorem h267 : Model (fun x => f267 ((23/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(6412823867903347/20000000000000),(327518807559549/100000000000000),(464288320639/25000000000000),(149936667/2500000000000)⟩
def e268 : ℝ := (1284515501/100000000000000)
theorem h268 : Model (fun x => f268 ((23/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(32046500291897687/100000000000000),(327518807559549/100000000000000),(464288320639/25000000000000),(149936667/2500000000000)⟩
def e269 : ℝ := (642257751/50000000000000)
theorem h269 : Model (fun x => f269 ((23/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(9713007714490397/25000000000000),(125989210657579/25000000000000),(1753506004677/50000000000000),(3696249899/25000000000000)⟩
def e270 : ℝ := (500936593/25000000000000)
theorem h270 : Model (fun x => f270 ((23/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(38855364191294921/100000000000000),(125989210657579/25000000000000),(1753506004677/50000000000000),(3696249899/25000000000000)⟩
def e271 : ℝ := (2003746373/100000000000000)
theorem h271 : Model (fun x => f271 ((23/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(8251489749295917/100000000000000),(59154195107279/25000000000000),(655838908921/25000000000000),(1061290783/6250000000000)⟩
def e272 : ℝ := (500010457/50000000000000)
theorem h272 : Model (fun x => f272 ((23/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(73491352093723/50000000000000),(808720150257/100000000000000),(2346421499/100000000000000),(384293/50000000000000)⟩
def e273 : ℝ := (3130563/100000000000000)
theorem h273 : Model (fun x => f273 ((23/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(221236423647123/100000000000000),(10422818463/3125000000000),(508921981/100000000000000),(-1083103/100000000000000)⟩
def e274 : ℝ := (1285639/100000000000000)
theorem h274 : Model (fun x => f274 ((23/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(122363887870423/25000000000000),(1475780531889/100000000000000),(3364265461/100000000000000),(-69881/5000000000000)⟩
def e275 : ℝ := (5701841/100000000000000)
theorem h275 : Model (fun x => f275 ((23/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(541426978720199/50000000000000),(38261297691/781250000000),(148561011/1000000000000),(516903/5000000000000)⟩
def e276 : ℝ := (18948813/100000000000000)
theorem h276 : Model (fun x => f276 ((23/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(95826694750499/4000000000000),(2889315896407/20000000000000),(10942489983/20000000000000),(21404223/25000000000000)⟩
def e277 : ℝ := (89643/160000000000)
theorem h277 : Model (fun x => f277 ((23/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(3521216681943319/100000000000000),(40608217929597/100000000000000),(253462691891/100000000000000),(925703041/100000000000000)⟩
def e278 : ℝ := (160345737/100000000000000)
theorem h278 : Model (fun x => f278 ((23/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(121236423647123/12500000000000),(10422818463/390625000000),(508921981/12500000000000),(-1083103/12500000000000)⟩
def e279 : ℝ := (1285639/12500000000000)
theorem h279 : Model (fun x => f279 ((23/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(111687409336443/10000000000000),(695392335357/20000000000000),(6417797347/100000000000000),(-3948119/50000000000000)⟩
def e280 : ℝ := (536627/4000000000000)
theorem h280 : Model (fun x => f280 ((23/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(121687409336443/10000000000000),(695392335357/20000000000000),(6417797347/100000000000000),(-3948119/50000000000000)⟩
def e281 : ℝ := (536627/4000000000000)
theorem h281 : Model (fun x => f281 ((23/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(42848773573794827/100000000000000),(154145559587491/25000000000000),(2361119279899/50000000000000),(2800693829/12500000000000)⟩
def e282 : ℝ := (619988553/25000000000000)
theorem h282 : Model (fun x => f282 ((23/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(233378908331/100000000000000),(-1679129619/50000000000000),(2260443/10000000000000),(-38601/50000000000000)⟩
def e283 : ℝ := (3573/25000000000000)
theorem h283 : Model (fun x => f283 ((23/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (42227444211380221/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(19257236697951/100000000000000),(55021448463/20000000000000),(41356081/100000000000000),(-1354263/100000000000000)⟩
def e284 : ℝ := (1871453/50000000000000)
theorem h284 : Model (fun x => f284 ((23/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(71236423647123/25000000000000),(667060381633/50000000000000),(1017843963/50000000000000),(-433241/10000000000000)⟩
def e285 : ℝ := (102851/2000000000000)
theorem h285 : Model (fun x => f285 ((23/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(8248346247087/20000000000000),(-1418237407/1250000000000),(139010829/100000000000000),(46229/10000000000000)⟩
def e286 : ℝ := (5533/1250000000000)
theorem h286 : Model (fun x => f286 ((23/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (24180476433117/10000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(117516537529129/100000000000000),(226917985119/100000000000000),(-278021663/100000000000000),(-184917/20000000000000)⟩
def e287 : ℝ := (851959/25000000000000)
theorem h287 : Model (fun x => f287 ((23/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(17516537529129/100000000000000),(226917985119/100000000000000),(-278021663/100000000000000),(-184917/20000000000000)⟩
def e288 : ℝ := (851959/25000000000000)
theorem h288 : Model (fun x => f288 ((23/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(108422995934613/25000000000000),(104679427659/12500000000000),(-128254041/12500000000000),(-3412159/100000000000000)⟩
def e289 : ℝ := (12576539/100000000000000)
theorem h289 : Model (fun x => f289 ((23/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2789406269452737/100000000000000),(104679427659/12500000000000),(-128254041/12500000000000),(-3412159/100000000000000)⟩
def e290 : ℝ := (628827/5000000000000)
theorem h290 : Model (fun x => f290 ((23/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1639006832740651/50000000000000),(3656894807273/50000000000000),(-353030989/5000000000000),(-34456787/100000000000000)⟩
def e291 : ℝ := (27476927/25000000000000)
theorem h291 : Model (fun x => f291 ((23/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4280197308931127/50000000000000),(3656894807273/50000000000000),(-353030989/5000000000000),(-34456787/100000000000000)⟩
def e292 : ℝ := (109907709/100000000000000)
theorem h292 : Model (fun x => f292 ((23/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(5029939676870817/50000000000000),(28019987302267/100000000000000),(-15500843341/100000000000000),(-38999071/25000000000000)⟩
def e293 : ℝ := (105377371/25000000000000)
theorem h293 : Model (fun x => f293 ((23/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(15328926972789253/100000000000000),(28019987302267/100000000000000),(-15500843341/100000000000000),(-38999071/25000000000000)⟩
def e294 : ℝ := (84301897/20000000000000)
theorem h294 : Model (fun x => f294 ((23/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(900701210939533/5000000000000),(33856105560371/50000000000000),(171787409/6250000000000),(-109531557/25000000000000)⟩
def e295 : ℝ := (1020211661/100000000000000)
theorem h295 : Model (fun x => f295 ((23/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(4069947700900989/20000000000000),(33856105560371/50000000000000),(171787409/6250000000000),(-109531557/25000000000000)⟩
def e296 : ℝ := (510105831/50000000000000)
theorem h296 : Model (fun x => f296 ((23/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(2989288510840771/12500000000000),(125750262584917/100000000000000),(100304561587/100000000000000),(-442519477/50000000000000)⟩
def e297 : ℝ := (949328887/50000000000000)
theorem h297 : Model (fun x => f297 ((23/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(303958612988839/1250000000000),(125750262584917/100000000000000),(100304561587/100000000000000),(-442519477/50000000000000)⟩
def e298 : ℝ := (75946311/4000000000000)
theorem h298 : Model (fun x => f298 ((23/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(7144032750120979/25000000000000),(25369536917347/12500000000000),(335618746647/100000000000000),(-346724869/25000000000000)⟩
def e299 : ℝ := (1535981861/50000000000000)
theorem h299 : Model (fun x => f299 ((23/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(7139627988216217/25000000000000),(25369536917347/12500000000000),(335618746647/100000000000000),(-346724869/25000000000000)⟩
def e300 : ℝ := (3071963723/100000000000000)
theorem h300 : Model (fun x => f300 ((23/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(33560974416849233/100000000000000),(75827902720733/25000000000000),(775553016553/100000000000000),(-1696567131/100000000000000)⟩
def e301 : ℝ := (1150789389/25000000000000)
theorem h301 : Model (fun x => f301 ((23/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(16782153875091283/50000000000000),(75827902720733/25000000000000),(775553016553/100000000000000),(-1696567131/100000000000000)⟩
def e302 : ℝ := (4603157557/100000000000000)
theorem h302 : Model (fun x => f302 ((23/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(2939652281726541/50000000000000),(129293143016369/100000000000000),(182700646167/25000000000000),(309086921/100000000000000)⟩
def e303 : ℝ := (197976449/10000000000000)
theorem h303 : Model (fun x => f303 ((23/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(138101365928351/100000000000000),(106666463657/20000000000000),(-27705029/20000000000000),(-3434843/100000000000000)⟩
def e304 : ℝ := (4014229/50000000000000)
theorem h304 : Model (fun x => f304 ((23/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(217516537529129/100000000000000),(226917985119/100000000000000),(-278021663/100000000000000),(-184917/20000000000000)⟩
def e305 : ℝ := (851959/25000000000000)
theorem h305 : Model (fun x => f305 ((23/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(473134440986609/100000000000000),(987168288523/100000000000000),(-694568471/100000000000000),(-5284013/100000000000000)⟩
def e306 : ℝ := (1484413/10000000000000)
theorem h306 : Model (fun x => f306 ((23/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(32160801684121/3125000000000),(3220881421171/100000000000000),(-29307757/5000000000000),(-807551/4000000000000)⟩
def e307 : ℝ := (12124671/25000000000000)
theorem h307 : Model (fun x => f307 ((23/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(2238561992477113/100000000000000),(9341266327001/100000000000000),(3172526997/100000000000000),(-63714091/100000000000000)⟩
def e308 : ℝ := (140858253/100000000000000)
theorem h308 : Model (fun x => f308 ((23/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(3091484688763803/100000000000000),(12419695481659/50000000000000),(5110032413/10000000000000),(-160901011/100000000000000)⟩
def e309 : ℝ := (376415939/100000000000000)
theorem h309 : Model (fun x => f309 ((23/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(117516537529129/12500000000000),(226917985119/12500000000000),(-278021663/12500000000000),(-184917/2500000000000)⟩
def e310 : ℝ := (851959/3125000000000)
theorem h310 : Model (fun x => f310 ((23/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1078233666161383/100000000000000),(2348676199237/100000000000000),(-2362698449/100000000000000),(-10831523/100000000000000)⟩
def e311 : ℝ := (17645573/50000000000000)
theorem h311 : Model (fun x => f311 ((23/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1178233666161383/100000000000000),(2348676199237/100000000000000),(-2362698449/100000000000000),(-10831523/100000000000000)⟩
def e312 : ℝ := (17645573/50000000000000)
theorem h312 : Model (fun x => f312 ((23/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(4553114173404947/12500000000000),(22829689492957/6250000000000),(222487125043/20000000000000),(-1617343511/100000000000000)⟩
def e313 : ℝ := (5551392377/100000000000000)
theorem h313 : Model (fun x => f313 ((23/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(274537372091/100000000000000),(-1376552997/50000000000000),(19224087/100000000000000),(-96511/100000000000000)⟩
def e314 : ℝ := (42961/100000000000000)
theorem h314 : Model (fun x => f314 ((23/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (36058518750991161/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1614088824573/10000000000000),(193094510789/100000000000000),(-84601687/20000000000000),(-2249/2500000000000)⟩
def e315 : ℝ := (1615919/20000000000000)
theorem h315 : Model (fun x => f315 ((23/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(35398124943681/100000000000000),(29262609569/6250000000000),(-190826177/50000000000000),(-1444223/100000000000000)⟩
def e316 : ℝ := (11822501/100000000000000)
theorem h316 : Model (fun x => f316 ((23/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(14076169815593/10000000000000),(299419922051/25000000000000),(-434962097/3125000000000),(-2269259/3125000000000)⟩
def e317 : ℝ := (48177493/100000000000000)
theorem h317 : Model (fun x => f317 ((23/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(48960590662931/100000000000000),(-458001363/5000000000000),(-1190416211/25000000000000),(16147941/100000000000000)⟩
def e318 : ℝ := (352217/2000000000000)
theorem h318 : Model (fun x => f318 ((23/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-29599671662233/25000000000000),(-299833903979/100000000000000),(2381769097/100000000000000),(-62494317/100000000000000)⟩
def e319 : ℝ := (30067727/100000000000000)
theorem h319 : Model (fun x => f319 ((23/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((23/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-5819/64),(-253/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((23/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((23/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(2231/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((23/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(12029/64),(27/32),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((23/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((23/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(18941/64),(27/32),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((23/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2367625/32),(3375/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((23/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((23/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1096847038255399347/100000000000000),(11437403944269/2500000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (14167/10000000000000)
theorem h329 : Model (fun x => f329 ((23/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(911704153/10000000000000),(-3802729/100000000000000),(190929/50000000000000),(-159/50000000000000)⟩
def e330 : ℝ := (9/50000000000000)
theorem h330 : Model (fun x => f330 ((23/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (13704297406021373/1250000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(67455423288957/10000000000000),(410442141241/25000000000000),(11780963823/100000000000000),(31777919/50000000000000)⟩
def e331 : ℝ := (2059563/100000000000000)
theorem h331 : Model (fun x => f331 ((23/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((23/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(95/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((23/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((23/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((23/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(825806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((23/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((23/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((23/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3663684377413777/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1097/100000000000000)
theorem h339 : Model (fun x => f339 ((23/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3924193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((23/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((23/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((23/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(552828905646491/25000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1097/100000000000000)
theorem h343 : Model (fun x => f343 ((23/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4522194795651/100000000000000),(-576194189/10000000000000),(3670781/50000000000000),(-1871/20000000000000)⟩
def e344 : ℝ := (1/6250000000000)
theorem h344 : Model (fun x => f344 ((23/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1104249040475193/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(41419736061121/25000000000000),(792034612893/100000000000000),(-1009168701/100000000000000),(1285801/100000000000000)⟩
def e345 : ℝ := (679/25000000000000)
theorem h345 : Model (fun x => f345 ((23/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(66419736061121/25000000000000),(792034612893/100000000000000),(-1009168701/100000000000000),(1285801/100000000000000)⟩
def e346 : ℝ := (679/25000000000000)
theorem h346 : Model (fun x => f346 ((23/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(66419736061121/50000000000000),(198008653223/50000000000000),(-504584351/100000000000000),(6429/1000000000000)⟩
def e347 : ℝ := (17/1250000000000)
theorem h347 : Model (fun x => f347 ((23/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(16419736061121/50000000000000),(198008653223/50000000000000),(-504584351/100000000000000),(6429/1000000000000)⟩
def e348 : ℝ := (17/1250000000000)
theorem h348 : Model (fun x => f348 ((23/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(490240909022559/100000000000000),(292298488091/20000000000000),(-931078267/50000000000000),(2372607/100000000000000)⟩
def e349 : ℝ := (5021/100000000000000)
theorem h349 : Model (fun x => f349 ((23/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(711488798684211/25000000000000),(292298488091/20000000000000),(-931078267/50000000000000),(2372607/100000000000000)⟩
def e350 : ℝ := (2511/50000000000000)
theorem h350 : Model (fun x => f350 ((23/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3780551857523947/100000000000000),(13211913947863/100000000000000),(-11046160463/100000000000000),(167487/2500000000000)⟩
def e351 : ℝ := (73631/100000000000000)
theorem h351 : Model (fun x => f351 ((23/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(9062932809904899/100000000000000),(13211913947863/100000000000000),(-11046160463/100000000000000),(167487/2500000000000)⟩
def e352 : ℝ := (2301/3125000000000)
theorem h352 : Model (fun x => f352 ((23/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(12039152103471141/100000000000000),(26720709572191/50000000000000),(-8082336203/100000000000000),(-43244809/100000000000000)⟩
def e353 : ℝ := (77771/20000000000000)
theorem h353 : Model (fun x => f353 ((23/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(432704993062969/2500000000000),(26720709572191/50000000000000),(-8082336203/100000000000000),(-43244809/100000000000000)⟩
def e354 : ℝ := (48607/12500000000000)
theorem h354 : Model (fun x => f354 ((23/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(919684845810291/4000000000000),(34883691355361/25000000000000),(22713253727/20000000000000),(-247836249/100000000000000)⟩
def e355 : ℝ := (241871/25000000000000)
theorem h355 : Model (fun x => f355 ((23/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(633195885774289/2500000000000),(34883691355361/25000000000000),(22713253727/20000000000000),(-247836249/100000000000000)⟩
def e356 : ℝ := (193497/20000000000000)
theorem h356 : Model (fun x => f356 ((23/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(33645362886492797/100000000000000),(17853741091729/6250000000000),(575642357309/100000000000000),(-13147507/3125000000000)⟩
def e357 : ℝ := (286853/12500000000000)
theorem h357 : Model (fun x => f357 ((23/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(34047743838873749/100000000000000),(17853741091729/6250000000000),(575642357309/100000000000000),(-13147507/3125000000000)⟩
def e358 : ℝ := (91793/4000000000000)
theorem h358 : Model (fun x => f358 ((23/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(45228843185093061/100000000000000),(102860800956307/20000000000000),(862071577311/50000000000000),(12456471/2500000000000)⟩
def e359 : ℝ := (1566131/25000000000000)
theorem h359 : Model (fun x => f359 ((23/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(45211224137474013/100000000000000),(102860800956307/20000000000000),(862071577311/50000000000000),(12456471/2500000000000)⟩
def e360 : ℝ := (250581/4000000000000)
theorem h360 : Model (fun x => f360 ((23/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(60058351484224137/100000000000000),(862242997095829/100000000000000),(2049473385009/50000000000000),(648169391/12500000000000)⟩
def e361 : ℝ := (6198587/50000000000000)
theorem h361 : Model (fun x => f361 ((23/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(6006168481755747/10000000000000),(862242997095829/100000000000000),(2049473385009/50000000000000),(648169391/12500000000000)⟩
def e362 : ℝ := (495887/4000000000000)
theorem h362 : Model (fun x => f362 ((23/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(19723940241810641/100000000000000),(104202143015569/20000000000000),(4457642111427/100000000000000),(13970775183/100000000000000)⟩
def e363 : ℝ := (10344789/100000000000000)
theorem h363 : Model (fun x => f363 ((23/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(176463253537159/100000000000000),(1052134598791/100000000000000),(227722693/100000000000000),(-2288433/100000000000000)⟩
def e364 : ℝ := (1127/10000000000000)
theorem h364 : Model (fun x => f364 ((23/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(116419736061121/50000000000000),(198008653223/50000000000000),(-504584351/100000000000000),(6429/1000000000000)⟩
def e365 : ℝ := (17/1250000000000)
theorem h365 : Model (fun x => f365 ((23/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(542142197781643/100000000000000),(1844169211683/100000000000000),(-781446009/100000000000000),(-1002633/100000000000000)⟩
def e366 : ℝ := (1399/10000000000000)
theorem h366 : Model (fun x => f366 ((23/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(631160515733349/50000000000000),(1288186157257/20000000000000),(549629957/20000000000000),(-1406143/12500000000000)⟩
def e367 : ℝ := (2593/5000000000000)
theorem h367 : Model (fun x => f367 ((23/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2939181626155099/100000000000000),(999801949503/5000000000000),(12768251839/50000000000000),(-19846883/50000000000000)⟩
def e368 : ℝ := (31059/20000000000000)
theorem h368 : Model (fun x => f368 ((23/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1037315104975933/20000000000000),(8276225973813/12500000000000),(262140973383/100000000000000),(35381559/20000000000000)⟩
def e369 : ℝ := (89183/6250000000000)
theorem h369 : Model (fun x => f369 ((23/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(66419736061121/6250000000000),(198008653223/6250000000000),(-504584351/12500000000000),(6429/125000000000)⟩
def e370 : ℝ := (17/156250000000)
theorem h370 : Model (fun x => f370 ((23/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(247835806103019/20000000000000),(4220273050359/100000000000000),(-761790423/20000000000000),(2854767/100000000000000)⟩
def e371 : ℝ := (443/2000000000000)
theorem h371 : Model (fun x => f371 ((23/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(267835806103019/20000000000000),(4220273050359/100000000000000),(-761790423/20000000000000),(2854767/100000000000000)⟩
def e372 : ℝ := (443/2000000000000)
theorem h372 : Model (fun x => f372 ((23/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(69457531831016697/100000000000000),(1105555511187791/100000000000000),(6107217442659/100000000000000),(11058341719/100000000000000)⟩
def e373 : ℝ := (4192479/20000000000000)
theorem h373 : Model (fun x => f373 ((23/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(35993216777/25000000000000),(-2291616079/100000000000000),(11908249/50000000000000),(-100257/50000000000000)⟩
def e374 : ℝ := (387/25000000000000)
theorem h374 : Model (fun x => f374 ((23/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (68345858023082133/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(28397122272803/100000000000000),(298117078443/100000000000000),(-412109167/50000000000000),(2499327/100000000000000)⟩
def e375 : ℝ := (637437/100000000000000)
theorem h375 : Model (fun x => f375 ((23/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(41419736061121/12500000000000),(792034612893/50000000000000),(-1009168701/50000000000000),(1285801/50000000000000)⟩
def e376 : ℝ := (679/12500000000000)
theorem h376 : Model (fun x => f376 ((23/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(2352463428283/6250000000000),(-28052391823/25000000000000),(477487521/100000000000000),(-1015929/50000000000000)⟩
def e377 : ℝ := (8839/100000000000000)
theorem h377 : Model (fun x => f377 ((23/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (264885899174373/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(124721170294939/100000000000000),(224419134583/100000000000000),(-190995009/20000000000000),(2031857/50000000000000)⟩
def e378 : ℝ := (15249/20000000000000)
theorem h378 : Model (fun x => f378 ((23/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(24721170294939/100000000000000),(224419134583/100000000000000),(-190995009/20000000000000),(2031857/50000000000000)⟩
def e379 : ℝ := (15249/20000000000000)
theorem h379 : Model (fun x => f379 ((23/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(230140254710899/50000000000000),(165642694573/20000000000000),(-3524312667/100000000000000),(14997039/100000000000000)⟩
def e380 : ℝ := (35173/12500000000000)
theorem h380 : Model (fun x => f380 ((23/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2815994795136083/100000000000000),(165642694573/20000000000000),(-3524312667/100000000000000),(14997039/100000000000000)⟩
def e381 : ℝ := (56277/20000000000000)
theorem h381 : Model (fun x => f381 ((23/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(878035415984573/25000000000000),(1838147171261/25000000000000),(-29428942057/100000000000000),(117319993/100000000000000)⟩
def e382 : ℝ := (162533/6250000000000)
theorem h382 : Model (fun x => f382 ((23/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2198630654079811/25000000000000),(1838147171261/25000000000000),(-29428942057/100000000000000),(117319993/100000000000000)⟩
def e383 : ℝ := (2600529/100000000000000)
theorem h383 : Model (fun x => f383 ((23/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(10968631528926449/100000000000000),(2890682620121/10000000000000),(-26047250339/25000000000000),(7348951/2000000000000)⟩
def e384 : ℝ := (10805723/100000000000000)
theorem h384 : Model (fun x => f384 ((23/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(4059419786993517/25000000000000),(2890682620121/10000000000000),(-26047250339/25000000000000),(7348951/2000000000000)⟩
def e385 : ℝ := (2701431/25000000000000)
theorem h385 : Model (fun x => f385 ((23/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(20251823462090537/100000000000000),(906167386919/1250000000000),(-55034769091/25000000000000),(608264693/100000000000000)⟩
def e386 : ℝ := (2890597/10000000000000)
theorem h386 : Model (fun x => f386 ((23/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(11293768873902411/50000000000000),(906167386919/1250000000000),(-55034769091/25000000000000),(608264693/100000000000000)⟩
def e387 : ℝ := (28905971/100000000000000)
theorem h387 : Model (fun x => f387 ((23/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(28171441419873281/100000000000000),(141105362320947/100000000000000),(-163788170241/50000000000000),(245099887/50000000000000)⟩
def e388 : ℝ := (14955591/25000000000000)
theorem h388 : Model (fun x => f388 ((23/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(28573822372254233/100000000000000),(141105362320947/100000000000000),(-163788170241/50000000000000),(245099887/50000000000000)⟩
def e389 : ℝ := (11964473/20000000000000)
theorem h389 : Model (fun x => f389 ((23/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(1781880283033629/5000000000000),(48022676824139/20000000000000),(-182381242773/50000000000000),(-310123671/100000000000000)⟩
def e390 : ℝ := (26655109/25000000000000)
theorem h390 : Model (fun x => f390 ((23/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(8904996653263383/25000000000000),(48022676824139/20000000000000),(-182381242773/50000000000000),(-310123671/100000000000000)⟩
def e391 : ℝ := (106620437/100000000000000)
theorem h391 : Model (fun x => f391 ((23/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(4442566416270097/10000000000000),(94852572101427/25000000000000),(-16014852831/6250000000000),(-2050915201/100000000000000)⟩
def e392 : ℝ := (173117179/100000000000000)
theorem h392 : Model (fun x => f392 ((23/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(44428997496034303/100000000000000),(94852572101427/25000000000000),(-16014852831/6250000000000),(-2050915201/100000000000000)⟩
def e393 : ℝ := (8655859/5000000000000)
theorem h393 : Model (fun x => f393 ((23/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(1372921016416103/12500000000000),(193501835197797/100000000000000),(181919251137/50000000000000),(-2899862727/100000000000000)⟩
def e394 : ℝ := (5663931/6250000000000)
theorem h394 : Model (fun x => f394 ((23/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(155553703197391/100000000000000),(111959268407/20000000000000),(-15027781/800000000000),(5850329/100000000000000)⟩
def e395 : ℝ := (217971/100000000000000)
theorem h395 : Model (fun x => f395 ((23/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(224721170294939/100000000000000),(224419134583/100000000000000),(-190995009/20000000000000),(2031857/50000000000000)⟩
def e396 : ℝ := (15249/20000000000000)
theorem h396 : Model (fun x => f396 ((23/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(504996043787269/100000000000000),(1008634611201/100000000000000),(-757684543/20000000000000),(13977757/100000000000000)⟩
def e397 : ℝ := (370461/100000000000000)
theorem h397 : Model (fun x => f397 ((23/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1134833019541893/100000000000000),(849980813359/25000000000000),(-21625791/195312500000),(33798419/100000000000000)⟩
def e398 : ℝ := (1327971/100000000000000)
theorem h398 : Model (fun x => f398 ((23/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(510042008481587/20000000000000),(10187129765669/100000000000000),(-7022332969/25000000000000),(16187889/25000000000000)⟩
def e399 : ℝ := (4175609/100000000000000)
theorem h399 : Model (fun x => f399 ((23/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1983473080138649/50000000000000),(3012244013163/10000000000000),(-34571813677/100000000000000),(-12335797/12500000000000)⟩
def e400 : ℝ := (13588727/100000000000000)
theorem h400 : Model (fun x => f400 ((23/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(124721170294939/12500000000000),(224419134583/12500000000000),(-190995009/2500000000000),(2031857/6250000000000)⟩
def e401 : ℝ := (15249/2500000000000)
theorem h401 : Model (fun x => f401 ((23/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1153323065556903/100000000000000),(2355149418699/100000000000000),(-1903654597/20000000000000),(38360041/100000000000000)⟩
def e402 : ℝ := (827931/100000000000000)
theorem h402 : Model (fun x => f402 ((23/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1253323065556903/100000000000000),(2355149418699/100000000000000),(-1903654597/20000000000000),(38360041/100000000000000)⟩
def e403 : ℝ := (827931/100000000000000)
theorem h403 : Model (fun x => f403 ((23/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(9943730244995857/20000000000000),(470958999512161/100000000000000),(-101452806041/100000000000000),(-339649089/10000000000000)⟩
def e404 : ℝ := (108125279/50000000000000)
theorem h404 : Model (fun x => f404 ((23/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(40226352701/20000000000000),(-1905216891/100000000000000),(4614387/25000000000000),(-164987/100000000000000)⟩
def e405 : ℝ := (2379/100000000000000)
theorem h405 : Model (fun x => f405 ((23/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (9849517431983927/20000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(22091042014787/100000000000000),(179936668709/100000000000000),(-115946801/12500000000000),(2415053/50000000000000)⟩
def e406 : ℝ := (647913/100000000000000)
theorem h406 : Model (fun x => f406 ((23/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(5048816428759/10000000000000),(29878359197/6250000000000),(-875896371/50000000000000),(7329433/100000000000000)⟩
def e407 : ℝ := (25707/2000000000000)
theorem h407 : Model (fun x => f407 ((23/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(170285024655089/50000000000000),(2026815298601/50000000000000),(1979736421/100000000000000),(27272033/25000000000000)⟩
def e408 : ℝ := (9959397/100000000000000)
theorem h408 : Model (fun x => f408 ((23/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(29614786896537/25000000000000),(379878924363/100000000000000),(-104587641/4000000000000),(60680141/100000000000000)⟩
def e409 : ℝ := (2696647/50000000000000)
theorem h409 : Model (fun x => f409 ((23/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(14760971/24414062500),(2501406887/3125000000000),(-29115241/12500000000000),(-56693/3125000000000)⟩
def e410 : ℝ := (35461021/100000000000000)
theorem h410 : Model (fun x => f410 ((23/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(26474215698242187/100000000000000),(272910919189453/25000000000000),(73531/409600),(3013/2048000)⟩
def e411 : ℝ := (601562501/100000000000000)
theorem h411 : Model (fun x => f411 ((23/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(2209/64),(47/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((23/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(103823/512),(6627/2560),(141/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((23/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(5368422844606637853/100000000000000),(289895794801711933/100000000000000),(6757811846733091/100000000000000),(44371551322937/50000000000000)⟩
def e414 : ℝ := (721103271249/100000000000000)
theorem h414 : Model (fun x => f414 ((23/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(465686119/25000000000000),(-12573567/12500000000000),(3086961/100000000000000),(-17717/25000000000000)⟩
def e415 : ℝ := (1011/50000000000000)
theorem h415 : Model (fun x => f415 ((23/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (2535839886876137853/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(134033648139/2500000000000),(-9121774007/50000000000000),(-80622007/100000000000000),(2591861/100000000000000)⟩
def e416 : ℝ := (11027421/100000000000000)
theorem h416 : Model (fun x => f416 ((23/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(677725857847/12500000000000),(6180147237/10000000000000),(-62708787/20000000000000),(155537/20000000000000)⟩
def e417 : ℝ := (23244221/50000000000000)
theorem h417 : Model (fun x => f417 ((23/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((23/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((5421655859689/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (57/20) (29/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (57/20) (29/10) ≤ (5421748836573/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(23/8)-(1/40)) (by norm_num : ((23/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel37


noncomputable section
namespace Hf4Quad.Panel38
open Hf4Quad.Dag

def p0 : Cubic := ⟨(117/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((117/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((117/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((117/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((117/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(128142857142857/25000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((117/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-128142857142857/25000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((117/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-421142857142857/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((117/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((117/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(13689/1600),(117/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((117/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(1035728571428571/100000000000000),(17704761904761/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((117/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-1035728571428571/100000000000000),(-17704761904761/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((117/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-364217857142857/25000000000000),(-22085714285713/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((117/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((117/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1601613/64000),(41067/64000),(351/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((117/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(312077259/1280000),(8001981/1280000),(68393/1280000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/100000000000000)
theorem h14 : Model (fun x => f14 ((117/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-312077259/1280000),(-8001981/1280000),(-68393/1280000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/100000000000000)
theorem h15 : Model (fun x => f15 ((117/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-6459476821986607/25000000000000),(-647240479910713/100000000000000),(-5418864500661/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/20000000000000)
theorem h16 : Model (fun x => f16 ((117/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((117/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(187388721/2560000),(1601613/640000),(41067/1280000),(117/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((117/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(20449165982142857/100000000000000),(139823357142857/20000000000000),(1792607142857/20000000000000),(51071428571/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((117/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-5388741305803571/100000000000000),(12969076450893/25000000000000),(443021401703/12500000000000),(17924313823/50000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((117/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((117/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(5352656337158203/25000000000000),(228745997314453/25000000000000),(1601613/10240000),(13689/10240000)⟩
def e22 : ℝ := (286132813/50000000000000)
theorem h22 : Model (fun x => f22 ((117/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(34871564803930663/25000000000000),(372559453033447/6250000000000),(50948301269531/50000000000000),(217727783203/25000000000000)⟩
def e23 : ℝ := (1864102291/50000000000000)
theorem h23 : Model (fun x => f23 ((117/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(134097517909919081/100000000000000),(1503206888584681/25000000000000),(52720386876343/50000000000000),(453379880229/50000000000000)⟩
def e24 : ℝ := (1918665787/50000000000000)
theorem h24 : Model (fun x => f24 ((117/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((117/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(2505043165790039/4000000000000),(80289845057373/2500000000000),(13724759838867/20000000000000),(97754699707/12500000000000)⟩
def e26 : ℝ := (2515112307/50000000000000)
theorem h26 : Model (fun x => f26 ((117/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(140627026396996369/100000000000000),(7211642379333143/100000000000000),(154094922635321/100000000000000),(1756067494419/100000000000000)⟩
def e27 : ℝ := (282384567/2500000000000)
theorem h27 : Model (fun x => f27 ((117/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(5494490886138309/2000000000000),(13224469933671867/100000000000000),(259535696388007/100000000000000),(2662827254877/100000000000000)⟩
def e28 : ℝ := (7566357127/50000000000000)
theorem h28 : Model (fun x => f28 ((117/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((117/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(183181281498396601/100000000000000),(2191912770066283/20000000000000),(140507228850401/50000000000000),(2001527476501/50000000000000)⟩
def e30 : ℝ := (6878020511/20000000000000)
theorem h30 : Model (fun x => f30 ((117/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(43469208863508399/100000000000000),(130036094890837/5000000000000),(13337035373419/20000000000000),(474965647201/50000000000000)⟩
def e31 : ℝ := (8160825927/100000000000000)
theorem h31 : Model (fun x => f31 ((117/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(318193753170423849/100000000000000),(15825191831488607/100000000000000),(163110436627551/50000000000000),(3612758549279/100000000000000)⟩
def e32 : ℝ := (23293540181/100000000000000)
theorem h32 : Model (fun x => f32 ((117/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((117/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(5872581/320),(50193/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((117/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((117/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(258453/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((117/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(10007829/320),(13573/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((117/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((117/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(10737429/320),(13573/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((117/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-10737429/320),(-13573/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((117/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((117/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(157/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((117/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(24649/1600),(157/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((117/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((117/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(517629/160),(3297/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((117/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(7727542313/25000000000000),(-196880059/50000000000000),(3762039/100000000000000),(-639/2000000000000)⟩
def e46 : ℝ := (261/100000000000000)
theorem h46 : Model (fun x => f46 ((117/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (255507/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-518587105814583/50000000000000),(101668867133/100000000000000),(-656338909/100000000000000),(106437/2500000000000)⟩
def e47 : ℝ := (8709957/50000000000000)
theorem h47 : Model (fun x => f47 ((117/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((117/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(197/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((117/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((117/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((117/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(32833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((117/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(52833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((117/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((117/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(33020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((117/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((117/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(693437499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((117/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((117/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(8020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((117/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(889911458333287/100000000000000),(1436458333331/10000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (7/5000000000000)
theorem h60 : Model (fun x => f60 ((117/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(4361501736111/2500000000000),(550347222221/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (13/100000000000000)
theorem h61 : Model (fun x => f61 ((117/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((117/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(33020833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((117/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(9345583767361/625000000000),(2633680555551/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (53/100000000000000)
theorem h64 : Model (fun x => f64 ((117/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(9970583767361/625000000000),(2633680555551/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (53/100000000000000)
theorem h65 : Model (fun x => f65 ((117/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(7098349392677141/50000000000000),(34504012541537/12500000000000),(1692127143/125000000000),(2169777199/100000000000000)⟩
def e66 : ℝ := (635679/100000000000000)
theorem h66 : Model (fun x => f66 ((117/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(58020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((117/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(1052005343967/195312500000),(967013888887/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (21/100000000000000)
theorem h68 : Model (fun x => f68 ((117/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(62503144169559/5000000000000),(210401068793/3125000000000),(1208767361/10000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (73/100000000000000)
theorem h69 : Model (fun x => f69 ((117/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(35493532436512073/20000000000000),(2203207511892899/50000000000000),(18611478477031/50000000000000),(38164722751/25000000000000)⟩
def e70 : ℝ := (169023167/50000000000000)
theorem h70 : Model (fun x => f70 ((117/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((117/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(91591536458331/312500000000),(11557291666641/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (273/12500000000000)
theorem h72 : Model (fun x => f72 ((117/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(376135909722197/4000000000000),(181449479166333/100000000000000),(864062499991/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (473/25000000000000)
theorem h73 : Model (fun x => f73 ((117/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(117548384963573539/100000000000000),(2901347770500761/100000000000000),(24154669220649/100000000000000),(95980875359/100000000000000)⟩
def e74 : ℝ := (199633647/100000000000000)
theorem h74 : Model (fun x => f74 ((117/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(18438502946633369/6250000000000),(7307762794286559/100000000000000),(61377626174711/100000000000000),(248639766363/100000000000000)⟩
def e75 : ℝ := (537679981/100000000000000)
theorem h75 : Model (fun x => f75 ((117/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((117/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(30530512152777/312500000000),(3852430555547/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (91/12500000000000)
theorem h77 : Model (fun x => f77 ((117/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(643337673611/6250000000000),(26736111111/10000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/20000000000000)
theorem h78 : Model (fun x => f78 ((117/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(412808340567/12500000000000),(128667534721/100000000000000),(52218967/3125000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((117/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(322643201496281/100000000000000),(730305906941/5000000000000),(49154680659/20000000000000),(1861808339/100000000000000)⟩
def e80 : ℝ := (48727/800000000000)
theorem h80 : Model (fun x => f80 ((117/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(748801096805947/100000000000000),(8810678130019/25000000000000),(78907241549/12500000000000),(53450027/1000000000000)⟩
def e81 : ℝ := (4383767/20000000000000)
theorem h81 : Model (fun x => f81 ((117/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(295764848242939851/100000000000000),(1468601101361327/20000000000000),(62008884107103/100000000000000),(253984769063/100000000000000)⟩
def e82 : ℝ := (17487463/3125000000000)
theorem h82 : Model (fun x => f82 ((117/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(211908281491/20000000000000),(2201644483/4000000000000),(214445891/20000000000000),(9283371/100000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((117/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(169968100779/50000000000000),(22073779321/100000000000000),(573344917/100000000000000),(7446037/100000000000000)⟩
def e84 : ℝ := (303/625000000000)
theorem h84 : Model (fun x => f84 ((117/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(54531432333/50000000000000),(4249202519/50000000000000),(275922241/100000000000000),(2388937/50000000000000)⟩
def e85 : ℝ := (46783/100000000000000)
theorem h85 : Model (fun x => f85 ((117/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(34991002413/100000000000000),(3181000219/100000000000000),(123935073/100000000000000),(2682577/100000000000000)⟩
def e86 : ℝ := (17557/50000000000000)
theorem h86 : Model (fun x => f86 ((117/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(104973007239/100000000000000),(9543000657/100000000000000),(371805219/100000000000000),(8047731/100000000000000)⟩
def e87 : ℝ := (52671/50000000000000)
theorem h87 : Model (fun x => f87 ((117/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-104973007239/100000000000000),(-9543000657/100000000000000),(-371805219/100000000000000),(-8047731/100000000000000)⟩
def e88 : ℝ := (52671/50000000000000)
theorem h88 : Model (fun x => f88 ((117/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(73941185817483153/25000000000000),(3671497981902989/50000000000000),(15502128075471/25000000000000),(63494180333/25000000000000)⟩
def e89 : ℝ := (279852079/50000000000000)
theorem h89 : Model (fun x => f89 ((117/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(91591536458331/250000000000),(11557291666641/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (273/10000000000000)
theorem h90 : Model (fun x => f90 ((117/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2901187608537013/100000000000000),(10417190694907/50000000000000),(2244278067/4000000000000),(67153741/100000000000000)⟩
def e91 : ℝ := (7591/25000000000000)
theorem h91 : Model (fun x => f91 ((117/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(212579384495820761/20000000000000),(14338986284909077/100000000000000),(7929073861163/10000000000000),(11512521021/5000000000000)⟩
def e92 : ℝ := (185649457/50000000000000)
theorem h92 : Model (fun x => f92 ((117/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(9408250027/100000000000000),(-126921779/100000000000000),(126299/12500000000000),(-6201/100000000000000)⟩
def e93 : ℝ := (41/100000000000000)
theorem h93 : Model (fun x => f93 ((117/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (262119603708465941/25000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(27826286538549/100000000000000),(157728772967/50000000000000),(-497561929/100000000000000),(104513/10000000000000)⟩
def e94 : ℝ := (330133/100000000000000)
theorem h94 : Model (fun x => f94 ((117/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(32833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((117/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(7570977917981/20000000000000),(-119416055489/100000000000000),(376706799/100000000000000),(-23767/2000000000000)⟩
def e96 : ℝ := (941/25000000000000)
theorem h96 : Model (fun x => f96 ((117/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (131666666666663/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(62145110410093/50000000000000),(9553284439/4000000000000),(-376706801/50000000000000),(2376697/100000000000000)⟩
def e97 : ℝ := (6447/20000000000000)
theorem h97 : Model (fun x => f97 ((117/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1305047318611953/50000000000000),(200618973219/4000000000000),(-7910842821/50000000000000),(49910637/100000000000000)⟩
def e98 : ℝ := (135387/20000000000000)
theorem h98 : Model (fun x => f98 ((117/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(12145110410093/50000000000000),(9553284439/4000000000000),(-376706801/50000000000000),(2376697/100000000000000)⟩
def e99 : ℝ := (6447/20000000000000)
theorem h99 : Model (fun x => f99 ((117/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(633997750997519/100000000000000),(7452013910579/100000000000000),(-11529367183/100000000000000),(-1417087/100000000000000)⟩
def e100 : ℝ := (1367399/100000000000000)
theorem h100 : Model (fun x => f100 ((117/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(30896117983061/20000000000000),(7421123953/1250000000000),(-1302431087/100000000000000),(72163/3125000000000)⟩
def e101 : ℝ := (12169/12500000000000)
theorem h101 : Model (fun x => f101 ((117/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(62145110410093/5000000000000),(9553284439/400000000000),(-376706801/5000000000000),(2376697/10000000000000)⟩
def e102 : ℝ := (6447/2000000000000)
theorem h102 : Model (fun x => f102 ((117/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(279476559623433/20000000000000),(298201102599/10000000000000),(-8836567107/100000000000000),(13038093/50000000000000)⟩
def e103 : ℝ := (209851/50000000000000)
theorem h103 : Model (fun x => f103 ((117/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(299476559623433/20000000000000),(298201102599/10000000000000),(-8836567107/100000000000000),(13038093/50000000000000)⟩
def e104 : ℝ := (209851/50000000000000)
theorem h104 : Model (fun x => f104 ((117/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(4746686631943273/50000000000000),(65245528624791/50000000000000),(-3221260591/50000000000000),(-171641199/20000000000000)⟩
def e105 : ℝ := (6532737/25000000000000)
theorem h105 : Model (fun x => f105 ((117/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(112145110410093/50000000000000),(9553284439/4000000000000),(-376706801/50000000000000),(2376697/100000000000000)⟩
def e106 : ℝ := (6447/20000000000000)
theorem h106 : Model (fun x => f106 ((117/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(503061031555677/100000000000000),(107135413819/10000000000000),(-2809258291/100000000000000),(706261/10000000000000)⟩
def e107 : ℝ := (80911/50000000000000)
theorem h107 : Model (fun x => f107 ((117/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(1128316698536533/100000000000000),(3604413843469/100000000000000),(-7532284159/100000000000000),(13015841/100000000000000)⟩
def e108 : ℝ := (294733/50000000000000)
theorem h108 : Model (fun x => f108 ((117/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(53557657895417291/50000000000000),(453633212294903/25000000000000),(3915677839179/100000000000000),(-925440577/5000000000000)⟩
def e109 : ℝ := (714923/195312500000)
theorem h109 : Model (fun x => f109 ((117/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(648818477644281/2500000000000),(155843603013/156250000000),(-27351052827/12500000000000),(1515423/390625000000)⟩
def e110 : ℝ := (255549/1562500000000)
theorem h110 : Model (fun x => f110 ((117/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(6303977637678599/100000000000000),(43105259028991/50000000000000),(-1308699091/12500000000000),(-281493663/50000000000000)⟩
def e111 : ℝ := (17363699/100000000000000)
theorem h111 : Model (fun x => f111 ((117/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(17782208089484123/25000000000000),(1199949113804741/100000000000000),(2514420175399/100000000000000),(-12402752949/100000000000000)⟩
def e112 : ℝ := (1940293/800000000000)
theorem h112 : Model (fun x => f112 ((117/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(89122074074385537/50000000000000),(3014481962984353/100000000000000),(3215049007289/50000000000000),(-30911564489/100000000000000)⟩
def e113 : ℝ := (608577201/100000000000000)
theorem h113 : Model (fun x => f113 ((117/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(216272825881427/2500000000000),(51947867671/156250000000),(-9117017609/12500000000000),(505141/390625000000)⟩
def e114 : ℝ := (85183/1562500000000)
theorem h114 : Model (fun x => f114 ((117/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(5900148274933/100000000000000),(11602569429/10000000000000),(204396117/100000000000000),(-1222089/50000000000000)⟩
def e115 : ℝ := (16441/50000000000000)
theorem h115 : Model (fun x => f115 ((117/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(1433159044699/100000000000000),(21137173013/50000000000000),(282302363/100000000000000),(-419729/50000000000000)⟩
def e116 : ℝ := (3663/25000000000000)
theorem h116 : Model (fun x => f116 ((117/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(123981342613831/100000000000000),(516699258991/12500000000000),(2339452417/6250000000000),(-1936179/25000000000000)⟩
def e117 : ℝ := (1784171/100000000000000)
theorem h117 : Model (fun x => f117 ((117/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(34759753390549/12500000000000),(9567354529517/100000000000000),(18578573111/20000000000000),(43830777/100000000000000)⟩
def e118 : ℝ := (2125261/50000000000000)
theorem h118 : Model (fun x => f118 ((117/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(89261113087947733/50000000000000),(302404931751387/10000000000000),(6522990880133/100000000000000),(-1929233357/6250000000000)⟩
def e119 : ℝ := (612827723/100000000000000)
theorem h119 : Model (fun x => f119 ((117/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(348117496661/100000000000000),(855711/6250000000),(31747793/20000000000000),(185883/100000000000000)⟩
def e120 : ℝ := (1803/25000000000000)
theorem h120 : Model (fun x => f120 ((117/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(21139627163/25000000000000),(4157081829/100000000000000),(34317341/50000000000000),(20587/6250000000000)⟩
def e121 : ℝ := (2317/100000000000000)
theorem h121 : Model (fun x => f121 ((117/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(20539448473/100000000000000),(1211717227/100000000000000),(12981443/50000000000000),(214621/100000000000000)⟩
def e122 : ℝ := (969/100000000000000)
theorem h122 : Model (fun x => f122 ((117/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(4989077389/100000000000000),(85845897/25000000000000),(1809133/20000000000000),(52749/50000000000000)⟩
def e123 : ℝ := (297/50000000000000)
theorem h123 : Model (fun x => f123 ((117/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(14967232167/100000000000000),(257537691/25000000000000),(5427399/20000000000000),(158247/50000000000000)⟩
def e124 : ℝ := (891/50000000000000)
theorem h124 : Model (fun x => f124 ((117/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-14967232167/100000000000000),(-257537691/25000000000000),(-5427399/20000000000000),(-158247/50000000000000)⟩
def e125 : ℝ := (891/50000000000000)
theorem h125 : Model (fun x => f125 ((117/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(178522211208663299/100000000000000),(1512024143681553/50000000000000),(3261481871569/50000000000000),(-15434025103/50000000000000)⟩
def e126 : ℝ := (122565901/20000000000000)
theorem h126 : Model (fun x => f126 ((117/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(648818477644281/2000000000000),(155843603013/125000000000),(-27351052827/10000000000000),(1515423/312500000000)⟩
def e127 : ℝ := (255549/1250000000000)
theorem h127 : Model (fun x => f127 ((117/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1265352007349311/50000000000000),(2694782589597/25000000000000),(-16786570583/100000000000000),(1086427/10000000000000)⟩
def e128 : ℝ := (232773/12500000000000)
theorem h128 : Model (fun x => f128 ((117/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(410491881546257513/50000000000000),(831500216151257/12500000000000),(535703797183/50000000000000),(-4326743167/12500000000000)⟩
def e129 : ℝ := (123785973/10000000000000)
theorem h129 : Model (fun x => f129 ((117/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(12180508859/100000000000000),(-98692289/100000000000000),(195939/25000000000000),(-5709/100000000000000)⟩
def e130 : ℝ := (63/100000000000000)
theorem h130 : Model (fun x => f130 ((117/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (407165327051952769/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(21744913751553/100000000000000),(192156812927/100000000000000),(-790793757/100000000000000),(3311779/100000000000000)⟩
def e131 : ℝ := (140653/50000000000000)
theorem h131 : Model (fun x => f131 ((117/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(24785600145051/50000000000000),(507614358861/100000000000000),(-644177843/50000000000000),(4356909/100000000000000)⟩
def e132 : ℝ := (611439/100000000000000)
theorem h132 : Model (fun x => f132 ((117/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-514139705803981/100000000000000),(-2607223373437/50000000000000),(6776611811/50000000000000),(-2385989/5000000000000)⟩
def e133 : ℝ := (1887601/12500000000000)
theorem h133 : Model (fun x => f133 ((117/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(17094017094017/50000000000000),(-292205420411/100000000000000),(99899289/4000000000000),(-10673001/50000000000000)⟩
def e134 : ℝ := (184019/100000000000000)
theorem h134 : Model (fun x => f134 ((117/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (29/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-175774258394523/100000000000000),(-140186373847/50000000000000),(7029929/100000000000),(-38199659/50000000000000)⟩
def e135 : ℝ := (7758013/100000000000000)
theorem h135 : Model (fun x => f135 ((117/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(187388721/256000),(1601613/64000),(41067/128000),(117/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((117/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((117/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(14414517/32000),(369603/32000),(3159/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((117/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(302704857/256000),(2340819/64000),(53703/128000),(27/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((117/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-13689/1600),(-117/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((117/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(300514617/256000),(2331459/64000),(53623/128000),(27/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((117/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((117/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(351/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((117/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-351/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((117/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(296021817/256000),(2321859/64000),(53623/128000),(27/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((117/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(296789817/256000),(2321859/64000),(53623/128000),(27/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((117/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((117/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(296789817/4000),(2321859/1000),(53623/2000),(27/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((117/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((117/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(35416468269/512000),(302704857/128000),(7761663/256000),(22113/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((117/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1445655157/100000000000000),(-12356027/25000000000000),(105607/10000000000000),(-18053/100000000000000)⟩
def e151 : ℝ := (303/100000000000000)
theorem h151 : Model (fun x => f151 ((117/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (17095018437/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(6703995773299/6250000000000),(-310535555001/100000000000000),(1181039387/50000000000000),(-17412033/100000000000000)⟩
def e152 : ℝ := (690397/1562500000000)
theorem h152 : Model (fun x => f152 ((117/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(237/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((117/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(46689/1600),(217/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((117/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(471/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((117/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(4246284501061/100000000000000),(-1690399881/6250000000000),(172270051/100000000000000),(-548631/50000000000000)⟩
def e156 : ℝ := (1759/25000000000000)
theorem h156 : Model (fun x => f156 ((117/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (117/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(123909235668773/100000000000000),(45321733809/12500000000000),(172270043/50000000000000),(-2194539/100000000000000)⟩
def e157 : ℝ := (9947/2500000000000)
theorem h157 : Model (fun x => f157 ((117/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(223909235668773/100000000000000),(45321733809/12500000000000),(172270043/50000000000000),(-2194539/100000000000000)⟩
def e158 : ℝ := (9947/2500000000000)
theorem h158 : Model (fun x => f158 ((117/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(55977308917193/50000000000000),(45321733809/25000000000000),(172270043/100000000000000),(-109727/10000000000000)⟩
def e159 : ℝ := (198941/100000000000000)
theorem h159 : Model (fun x => f159 ((117/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(5977308917193/50000000000000),(45321733809/25000000000000),(172270043/100000000000000),(-109727/10000000000000)⟩
def e160 : ℝ := (198941/100000000000000)
theorem h160 : Model (fun x => f160 ((117/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((117/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((117/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(206582925765831/50000000000000),(167258779533/25000000000000),(158939623/25000000000000),(-4049449/100000000000000)⟩
def e163 : ℝ := (734189/100000000000000)
theorem h163 : Model (fun x => f163 ((117/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2768880137245947/100000000000000),(167258779533/25000000000000),(158939623/25000000000000),(-4049449/100000000000000)⟩
def e164 : ℝ := (73419/10000000000000)
theorem h164 : Model (fun x => f164 ((117/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((117/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1549944587972961/50000000000000),(2884316825427/50000000000000),(3347292627/50000000000000),(-32610543/100000000000000)⟩
def e166 : ℝ := (1269333/20000000000000)
theorem h166 : Model (fun x => f166 ((117/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4191135064163437/50000000000000),(2884316825427/50000000000000),(3347292627/50000000000000),(-32610543/100000000000000)⟩
def e167 : ℝ := (3173333/50000000000000)
theorem h167 : Model (fun x => f167 ((117/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((117/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1173042311001781/12500000000000),(866168495077/4000000000000),(32392816841/100000000000000),(-106411109/100000000000000)⟩
def e169 : ℝ := (23915181/100000000000000)
theorem h169 : Model (fun x => f169 ((117/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14653386107061867/100000000000000),(866168495077/4000000000000),(32392816841/100000000000000),(-106411109/100000000000000)⟩
def e170 : ℝ := (11957591/50000000000000)
theorem h170 : Model (fun x => f170 ((117/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((117/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(26248227865533/160000000000),(25403782646711/50000000000000),(20152981363/20000000000000),(-36778339/20000000000000)⟩
def e172 : ℝ := (28193769/50000000000000)
theorem h172 : Model (fun x => f172 ((117/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(1874085670167241/10000000000000),(25403782646711/50000000000000),(20152981363/20000000000000),(-36778339/20000000000000)⟩
def e173 : ℝ := (56387539/100000000000000)
theorem h173 : Model (fun x => f173 ((117/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((117/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(20981254499247263/100000000000000),(90856140306639/100000000000000),(118601663111/50000000000000),(-141313217/100000000000000)⟩
def e175 : ℝ := (12666751/12500000000000)
theorem h175 : Model (fun x => f175 ((117/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(4276727090325643/20000000000000),(90856140306639/100000000000000),(118601663111/50000000000000),(-141313217/100000000000000)⟩
def e176 : ℝ := (101334009/100000000000000)
theorem h176 : Model (fun x => f176 ((117/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((117/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2992495918621081/12500000000000),(70241691005833/50000000000000),(93421597517/20000000000000),(193693663/100000000000000)⟩
def e178 : ℝ := (39300341/25000000000000)
theorem h178 : Model (fun x => f178 ((117/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(29902935376687/125000000000),(70241691005833/50000000000000),(93421597517/20000000000000),(193693663/100000000000000)⟩
def e179 : ℝ := (31440273/20000000000000)
theorem h179 : Model (fun x => f179 ((117/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((117/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(1071286944711467/4000000000000),(200645725523979/100000000000000),(204709504961/25000000000000),(521586393/50000000000000)⟩
def e181 : ℝ := (7016927/3125000000000)
theorem h181 : Model (fun x => f181 ((117/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(3348188368890001/12500000000000),(200645725523979/100000000000000),(204709504961/25000000000000),(521586393/50000000000000)⟩
def e182 : ℝ := (44908333/20000000000000)
theorem h182 : Model (fun x => f182 ((117/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(1601052495504647/50000000000000),(72545054326533/100000000000000),(507776846781/100000000000000),(103806051/6250000000000)⟩
def e183 : ℝ := (82046031/100000000000000)
theorem h183 : Model (fun x => f183 ((117/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(62669182272217/50000000000000),(202959095527/50000000000000),(142875613/20000000000000),(-1832283/100000000000000)⟩
def e184 : ℝ := (7029/1562500000000)
theorem h184 : Model (fun x => f184 ((117/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(105977308917193/50000000000000),(45321733809/25000000000000),(172270043/100000000000000),(-109727/10000000000000)⟩
def e185 : ℝ := (198941/100000000000000)
theorem h185 : Model (fun x => f185 ((117/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(224623800106603/50000000000000),(384246030763/50000000000000),(1058918151/100000000000000),(-4026823/100000000000000)⟩
def e186 : ℝ := (423869/50000000000000)
theorem h186 : Model (fun x => f186 ((117/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(952201034162051/100000000000000),(1221640809071/50000000000000),(220576033/5000000000000),(-2044187/20000000000000)⟩
def e187 : ℝ := (676889/25000000000000)
theorem h187 : Model (fun x => f187 ((117/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1009117031486623/50000000000000),(1726216072117/25000000000000),(15420129251/100000000000000),(-155511/781250000000)⟩
def e188 : ℝ := (7680699/100000000000000)
theorem h188 : Model (fun x => f188 ((117/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(632405391802337/25000000000000),(3369364634567/20000000000000),(30886629737/50000000000000),(49991073/100000000000000)⟩
def e189 : ℝ := (18865959/100000000000000)
theorem h189 : Model (fun x => f189 ((117/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((117/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(55977308917193/6250000000000),(45321733809/3125000000000),(172270043/12500000000000),(-109727/1250000000000)⟩
def e191 : ℝ := (198941/12500000000000)
theorem h191 : Model (fun x => f191 ((117/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(510487653609761/50000000000000),(928106836471/50000000000000),(2092538409/100000000000000),(-10610443/100000000000000)⟩
def e192 : ℝ := (255173/12500000000000)
theorem h192 : Model (fun x => f192 ((117/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(560487653609761/50000000000000),(928106836471/50000000000000),(2092538409/100000000000000),(-10610443/100000000000000)⟩
def e193 : ℝ := (255173/12500000000000)
theorem h193 : Model (fun x => f193 ((117/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(1134257325380651/4000000000000),(117901954611323/50000000000000),(529054661627/50000000000000),(1791153463/100000000000000)⟩
def e194 : ℝ := (264256357/100000000000000)
theorem h194 : Model (fun x => f194 ((117/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(44081707811/12500000000000),(-2932566019/100000000000000),(11227237/100000000000000),(-6211/100000000000000)⟩
def e195 : ℝ := (441/12500000000000)
theorem h195 : Model (fun x => f195 ((117/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (5623913812112111/20000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(2258468105501/20000000000000),(161928948177/100000000000000),(711561/3125000000000),(-271939/25000000000000)⟩
def e196 : ℝ := (82251/20000000000000)
theorem h196 : Model (fun x => f196 ((117/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(123909235668773/50000000000000),(45321733809/6250000000000),(172270043/25000000000000),(-2194539/50000000000000)⟩
def e197 : ℝ := (9947/1250000000000)
theorem h197 : Model (fun x => f197 ((117/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(44660953667819/100000000000000),(-72319012577/100000000000000),(48383423/100000000000000),(3677/781250000000)⟩
def e198 : ℝ := (81171/100000000000000)
theorem h198 : Model (fun x => f198 ((117/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (55886578666449/25000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(55339046332179/50000000000000),(144638025151/100000000000000),(-96766851/100000000000000),(-941317/100000000000000)⟩
def e199 : ℝ := (564641/100000000000000)
theorem h199 : Model (fun x => f199 ((117/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(5339046332179/50000000000000),(144638025151/100000000000000),(-96766851/100000000000000),(-941317/100000000000000)⟩
def e200 : ℝ := (564641/100000000000000)
theorem h200 : Model (fun x => f200 ((117/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(40845486578513/10000000000000),(533783188057/100000000000000),(-4463947/1250000000000),(-868477/25000000000000)⟩
def e201 : ℝ := (520949/25000000000000)
theorem h201 : Model (fun x => f201 ((117/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(552833830299883/20000000000000),(533783188057/100000000000000),(-4463947/1250000000000),(-868477/25000000000000)⟩
def e202 : ℝ := (2083797/100000000000000)
theorem h202 : Model (fun x => f202 ((117/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(76483242372403/2500000000000),(2294410362033/50000000000000),(-459598979/20000000000000),(-12359/40000000000)⟩
def e203 : ℝ := (4482421/25000000000000)
theorem h203 : Model (fun x => f203 ((117/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(521356915454817/6250000000000),(2294410362033/50000000000000),(-459598979/20000000000000),(-12359/40000000000)⟩
def e204 : ℝ := (3585937/20000000000000)
theorem h204 : Model (fun x => f204 ((117/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(1846489247997187/20000000000000),(3428820959443/20000000000000),(-99455199/2500000000000),(-15060367/12500000000000)⟩
def e205 : ℝ := (67082541/100000000000000)
theorem h205 : Model (fun x => f205 ((117/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(7250746929516777/50000000000000),(3428820959443/20000000000000),(-99455199/2500000000000),(-15060367/12500000000000)⟩
def e206 : ℝ := (33541271/50000000000000)
theorem h206 : Model (fun x => f206 ((117/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(16049976811017341/100000000000000),(7989888505807/20000000000000),(79515637/1250000000000),(-58439411/20000000000000)⟩
def e207 : ℝ := (15665293/10000000000000)
theorem h207 : Model (fun x => f207 ((117/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(9192845548365813/50000000000000),(7989888505807/20000000000000),(79515637/1250000000000),(-58439411/20000000000000)⟩
def e208 : ℝ := (156652931/100000000000000)
theorem h208 : Model (fun x => f208 ((117/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(20348932229023247/100000000000000),(14161596306771/20000000000000),(5878917707/12500000000000),(-525922793/100000000000000)⟩
def e209 : ℝ := (27845103/10000000000000)
theorem h209 : Model (fun x => f209 ((117/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(20751313181404199/100000000000000),(14161596306771/20000000000000),(5878917707/12500000000000),(-525922793/100000000000000)⟩
def e210 : ℝ := (278451031/100000000000000)
theorem h210 : Model (fun x => f210 ((117/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(918686305279427/4000000000000),(108383212994283/100000000000000),(33597066433/25000000000000),(-388955203/50000000000000)⟩
def e211 : ℝ := (26726913/6250000000000)
theorem h211 : Model (fun x => f211 ((117/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(22949538584366627/100000000000000),(108383212994283/100000000000000),(33597066433/25000000000000),(-388955203/50000000000000)⟩
def e212 : ℝ := (427630609/100000000000000)
theorem h212 : Model (fun x => f212 ((117/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(1587506973777993/6250000000000),(30630046460023/20000000000000),(283294162339/100000000000000),(-987506797/100000000000000)⟩
def e213 : ℝ := (606383531/100000000000000)
theorem h213 : Model (fun x => f213 ((117/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(25403444913781221/100000000000000),(30630046460023/20000000000000),(283294162339/100000000000000),(-987506797/100000000000000)⟩
def e214 : ℝ := (151595883/25000000000000)
theorem h214 : Model (fun x => f214 ((117/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(1356301693916349/50000000000000),(53096564764301/100000000000000),(227181770991/100000000000000),(-20755353/25000000000000)⟩
def e215 : ℝ := (213078269/100000000000000)
theorem h215 : Model (fun x => f215 ((117/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(61248200979101/50000000000000),(320165215009/100000000000000),(-4997827/100000000000000),(-2363587/100000000000000)⟩
def e216 : ℝ := (250827/20000000000000)
theorem h216 : Model (fun x => f216 ((117/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(105339046332179/50000000000000),(144638025151/100000000000000),(-96766851/100000000000000),(-941317/100000000000000)⟩
def e217 : ℝ := (564641/100000000000000)
theorem h217 : Model (fun x => f217 ((117/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(221926293643459/50000000000000),(609441265311/100000000000000),(-198531529/100000000000000),(-4246221/100000000000000)⟩
def e218 : ℝ := (2383417/100000000000000)
theorem h218 : Model (fun x => f218 ((117/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(935100165137483/100000000000000),(3851877701/200000000000),(42149/125000000000),(-14000807/100000000000000)⟩
def e219 : ℝ := (7546097/100000000000000)
theorem h219 : Model (fun x => f219 ((117/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1970051192412911/100000000000000),(5410041648153/100000000000000),(975905951/50000000000000),(-4011379/10000000000000)⟩
def e220 : ℝ := (21238157/100000000000000)
theorem h220 : Model (fun x => f220 ((117/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(241324182744047/10000000000000),(12934524999403/100000000000000),(19613511077/100000000000000),(-44861593/50000000000000)⟩
def e221 : ℝ := (51115401/100000000000000)
theorem h221 : Model (fun x => f221 ((117/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(55339046332179/6250000000000),(144638025151/12500000000000),(-96766851/12500000000000),(-941317/12500000000000)⟩
def e222 : ℝ := (564641/12500000000000)
theorem h222 : Model (fun x => f222 ((117/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(503960571636533/50000000000000),(1477269416217/100000000000000),(-155826527/20000000000000),(-9894123/100000000000000)⟩
def e223 : ℝ := (5771263/100000000000000)
theorem h223 : Model (fun x => f223 ((117/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(553960571636533/50000000000000),(1477269416217/100000000000000),(-155826527/20000000000000),(-9894123/100000000000000)⟩
def e224 : ℝ := (5771263/100000000000000)
theorem h224 : Model (fun x => f224 ((117/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(5347363288904457/20000000000000),(8947721035323/5000000000000),(38957766347/10000000000000),(-32620749/3125000000000)⟩
def e225 : ℝ := (88731911/12500000000000)
theorem h225 : Model (fun x => f225 ((117/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(187008053497/50000000000000),(-500671693/20000000000000),(11305711/100000000000000),(-24593/100000000000000)⟩
def e226 : ℝ := (5083/50000000000000)
theorem h226 : Model (fun x => f226 ((117/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (26557470692433099/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(10145573589359/100000000000000),(130683517947/100000000000000),(-86410917/50000000000000),(-330927/50000000000000)⟩
def e227 : ℝ := (549131/50000000000000)
theorem h227 : Model (fun x => f227 ((117/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(83741852019/390625000000),(73153116531/25000000000000),(-75025941/50000000000000),(-174961/10000000000000)⟩
def e228 : ℝ := (1509517/100000000000000)
theorem h228 : Model (fun x => f228 ((117/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(718598428139/3125000000000),(123647646097/50000000000000),(-140809219/25000000000000),(55257/3125000000000)⟩
def e229 : ℝ := (5637379/50000000000000)
theorem h229 : Model (fun x => f229 ((117/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3930794820589/50000000000000),(271130081/1562500000000),(-42608761/12500000000000),(175897/5000000000000)⟩
def e230 : ℝ := (500351/12500000000000)
theorem h230 : Model (fun x => f230 ((117/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-33582533750669/20000000000000),(-26302042251/10000000000000),(209033091/3125000000000),(-36440689/50000000000000)⟩
def e231 : ℝ := (11760821/100000000000000)
theorem h231 : Model (fun x => f231 ((117/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((117/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-13689/320),(-117/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((117/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2457/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((117/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5967/320),(-33/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((117/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((117/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14287/320),(-33/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((117/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((117/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(357175/32),(-825/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((117/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14391/1600),(3/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((117/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23991/1600),(3/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((117/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((117/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4534299/1600),(567/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((117/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(17643300541/50000000000000),(-13789/156250000000),(1473033/100000000000000),(-737/100000000000000)⟩
def e244 : ℝ := (1/1562500000000)
theorem h244 : Model (fun x => f244 ((117/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (283311/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(393859116920729/100000000000000),(-1917967089791/100000000000000),(-266776001/2500000000000),(-77284951/100000000000000)⟩
def e245 : ℝ := (1831083/100000000000000)
theorem h245 : Model (fun x => f245 ((117/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(1053/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((117/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(97929/1600),(477/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((117/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(131529/1600),(477/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((117/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(38809/1600),(197/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((117/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(5104508961/2560000),(22211553/640000),(273107/1280000),(337/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((117/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((117/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(221841/160),(1413/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((117/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(14424745651/20000000000000),(-918773609/100000000000000),(8778091/100000000000000),(-74549/100000000000000)⟩
def e253 : ℝ := (19/3125000000000)
theorem h253 : Model (fun x => f253 ((117/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (109503/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(143811022335303/100000000000000),(167776555713/25000000000000),(1005187277/100000000000000),(-1027369/50000000000000)⟩
def e254 : ℝ := (2471533/100000000000000)
theorem h254 : Model (fun x => f254 ((117/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(243811022335303/100000000000000),(167776555713/25000000000000),(1005187277/100000000000000),(-1027369/50000000000000)⟩
def e255 : ℝ := (2471533/100000000000000)
theorem h255 : Model (fun x => f255 ((117/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(121905511167651/100000000000000),(167776555713/50000000000000),(251296819/50000000000000),(-1027369/100000000000000)⟩
def e256 : ℝ := (154471/12500000000000)
theorem h256 : Model (fun x => f256 ((117/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(21905511167651/100000000000000),(167776555713/50000000000000),(251296819/50000000000000),(-1027369/100000000000000)⟩
def e257 : ℝ := (154471/12500000000000)
theorem h257 : Model (fun x => f257 ((117/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(89977877290409/20000000000000),(1238350768357/100000000000000),(927404927/50000000000000),(-3791481/100000000000000)⟩
def e258 : ℝ := (182423/4000000000000)
theorem h258 : Model (fun x => f258 ((117/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(280560367216633/10000000000000),(1238350768357/100000000000000),(927404927/50000000000000),(-3791481/100000000000000)⟩
def e259 : ℝ := (71259/1562500000000)
theorem h259 : Model (fun x => f259 ((117/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3420185497892751/100000000000000),(218478165009/2000000000000),(20517225531/100000000000000),(-20998183/100000000000000)⟩
def e260 : ℝ := (20138581/50000000000000)
theorem h260 : Model (fun x => f260 ((117/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8702566450273703/100000000000000),(218478165009/2000000000000),(20517225531/100000000000000),(-20998183/100000000000000)⟩
def e261 : ℝ := (40277163/100000000000000)
theorem h261 : Model (fun x => f261 ((117/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(5304454057955329/50000000000000),(10629644672501/25000000000000),(52702844003/50000000000000),(2185911/25000000000000)⟩
def e262 : ℝ := (31398821/20000000000000)
theorem h262 : Model (fun x => f262 ((117/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(15877955734958277/100000000000000),(10629644672501/25000000000000),(52702844003/50000000000000),(2185911/25000000000000)⟩
def e263 : ℝ := (78497053/50000000000000)
theorem h263 : Model (fun x => f263 ((117/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(4839025775418561/25000000000000),(26277866298191/25000000000000),(17548467593/5000000000000),(207460763/50000000000000)⟩
def e264 : ℝ := (388776809/100000000000000)
theorem h264 : Model (fun x => f264 ((117/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(21691817387388529/100000000000000),(26277866298191/25000000000000),(17548467593/5000000000000),(207460763/50000000000000)⟩
def e265 : ℝ := (38877681/10000000000000)
theorem h265 : Model (fun x => f265 ((117/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(3305440108456173/12500000000000),(100462118553637/50000000000000),(444788734251/50000000000000),(1988929317/100000000000000)⟩
def e266 : ℝ := (746688563/100000000000000)
theorem h266 : Model (fun x => f266 ((117/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(209733607968987/781250000000),(100462118553637/50000000000000),(444788734251/50000000000000),(1988929317/100000000000000)⟩
def e267 : ℝ := (186672141/25000000000000)
theorem h267 : Model (fun x => f267 ((117/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(4090829230159213/12500000000000),(167509988576403/50000000000000),(1893577284043/100000000000000),(1535911321/25000000000000)⟩
def e268 : ℝ := (157011547/12500000000000)
theorem h268 : Model (fun x => f268 ((117/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(255539178075427/781250000000),(167509988576403/50000000000000),(1893577284043/100000000000000),(1535911321/25000000000000)⟩
def e269 : ℝ := (1256092377/100000000000000)
theorem h269 : Model (fun x => f269 ((117/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(19937045841053647/50000000000000),(259081966259387/50000000000000),(3596938452107/100000000000000),(7595573247/50000000000000)⟩
def e270 : ℝ := (394107981/20000000000000)
theorem h270 : Model (fun x => f270 ((117/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(39877425015440627/100000000000000),(259081966259387/50000000000000),(3596938452107/100000000000000),(7595573247/50000000000000)⟩
def e271 : ℝ := (985269953/50000000000000)
theorem h271 : Model (fun x => f271 ((117/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(8735353790129/100000000000),(6182909962513/2500000000000),(2727064353299/100000000000000),(6871839/39062500000)⟩
def e272 : ℝ := (500643921/50000000000000)
theorem h272 : Model (fun x => f272 ((117/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(74304768265231/50000000000000),(163623094289/20000000000000),(293917199/12500000000000),(434049/50000000000000)⟩
def e273 : ℝ := (3025627/100000000000000)
theorem h273 : Model (fun x => f273 ((117/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(221905511167651/100000000000000),(167776555713/50000000000000),(251296819/50000000000000),(-1027369/100000000000000)⟩
def e274 : ℝ := (154471/12500000000000)
theorem h274 : Model (fun x => f274 ((117/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(123105139716441/25000000000000),(1489221694297/100000000000000),(839131217/25000000000000),(-14833/1250000000000)⟩
def e275 : ℝ := (5497163/100000000000000)
theorem h275 : Model (fun x => f275 ((117/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(1092708358245677/100000000000000),(1239249379931/25000000000000),(7460158899/50000000000000),(11055461/100000000000000)⟩
def e276 : ℝ := (1145191/6250000000000)
theorem h276 : Model (fun x => f276 ((117/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(606195016984179/25000000000000),(458327111863/3125000000000),(27617124789/50000000000000),(3531427/4000000000000)⟩
def e277 : ℝ := (1698359/3125000000000)
theorem h277 : Model (fun x => f277 ((117/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(144138176833751/4000000000000),(20816635189881/50000000000000),(259086767947/100000000000000),(474494253/50000000000000)⟩
def e278 : ℝ := (157172583/100000000000000)
theorem h278 : Model (fun x => f278 ((117/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(121905511167651/12500000000000),(167776555713/6250000000000),(251296819/6250000000000),(-1027369/12500000000000)⟩
def e279 : ℝ := (154471/1562500000000)
theorem h279 : Model (fun x => f279 ((117/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(112385362587167/10000000000000),(3502540362853/100000000000000),(796510837/12500000000000),(-3675427/50000000000000)⟩
def e280 : ℝ := (12911771/100000000000000)
theorem h280 : Model (fun x => f280 ((117/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(122385362587167/10000000000000),(3502540362853/100000000000000),(796510837/12500000000000),(-3675427/50000000000000)⟩
def e281 : ℝ := (12911771/100000000000000)
theorem h281 : Model (fun x => f281 ((117/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(44101007586129527/100000000000000),(635742734658737/100000000000000),(2429340071423/50000000000000),(23076872271/100000000000000)⟩
def e282 : ℝ := (1223242711/50000000000000)
theorem h282 : Model (fun x => f282 ((117/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(45350437767/20000000000000),(-1634385069/50000000000000),(22139641/100000000000000),(-19421/25000000000000)⟩
def e283 : ℝ := (1669/12500000000000)
theorem h283 : Model (fun x => f283 ((117/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (43460380647970251/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(9903802960799/50000000000000),(275256710807/100000000000000),(66899/200000000000),(-1282439/100000000000000)⟩
def e284 : ℝ := (1834161/50000000000000)
theorem h284 : Model (fun x => f284 ((117/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(143811022335303/50000000000000),(167776555713/12500000000000),(1005187277/50000000000000),(-1027369/25000000000000)⟩
def e285 : ℝ := (2471533/50000000000000)
theorem h285 : Model (fun x => f285 ((117/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(4101537290733/10000000000000),(-112897570123/100000000000000),(141659431/100000000000000),(105297/25000000000000)⟩
def e286 : ℝ := (420781/100000000000000)
theorem h286 : Model (fun x => f286 ((117/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (243138906398903/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(14746156773167/12500000000000),(112897570121/50000000000000),(-141659433/50000000000000),(-842381/100000000000000)⟩
def e287 : ℝ := (1631033/50000000000000)
theorem h287 : Model (fun x => f287 ((117/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(2246156773167/12500000000000),(112897570121/50000000000000),(-141659433/50000000000000),(-842381/100000000000000)⟩
def e288 : ℝ := (1631033/50000000000000)
theorem h288 : Model (fun x => f288 ((117/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(27210170236201/6250000000000),(208322897247/25000000000000),(-104558153/10000000000000),(-777197/25000000000000)⟩
def e289 : ℝ := (601929/5000000000000)
theorem h289 : Model (fun x => f289 ((117/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2791077009493501/100000000000000),(208322897247/25000000000000),(-104558153/10000000000000),(-777197/25000000000000)⟩
def e290 : ℝ := (12038581/100000000000000)
theorem h290 : Model (fun x => f290 ((117/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1646306365918931/50000000000000),(3642572060283/50000000000000),(-3629790277/50000000000000),(-15950331/50000000000000)⟩
def e291 : ℝ := (10531413/10000000000000)
theorem h291 : Model (fun x => f291 ((117/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4287496842109407/50000000000000),(3642572060283/50000000000000),(-3629790277/50000000000000),(-15950331/50000000000000)⟩
def e292 : ℝ := (105314131/100000000000000)
theorem h292 : Model (fun x => f292 ((117/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(50579280478563/500000000000),(27956149200383/100000000000000),(-16409146519/100000000000000),(-146899059/100000000000000)⟩
def e293 : ℝ := (80909843/20000000000000)
theorem h293 : Model (fun x => f293 ((117/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(15384903714760219/100000000000000),(27956149200383/100000000000000),(-16409146519/100000000000000),(-146899059/100000000000000)⟩
def e294 : ℝ := (12642163/3125000000000)
theorem h294 : Model (fun x => f294 ((117/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(18149456169434683/100000000000000),(67718025629471/100000000000000),(88771893/50000000000000),(-419151331/100000000000000)⟩
def e295 : ℝ := (490728883/50000000000000)
theorem h295 : Model (fun x => f295 ((117/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(2560646306893621/12500000000000),(67718025629471/100000000000000),(88771893/50000000000000),(-419151331/100000000000000)⟩
def e296 : ℝ := (981457767/100000000000000)
theorem h296 : Model (fun x => f296 ((117/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(24166202804534037/100000000000000),(126140969142137/100000000000000),(95075105387/100000000000000),(-42924497/5000000000000)⟩
def e297 : ℝ := (916002341/50000000000000)
theorem h297 : Model (fun x => f297 ((117/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(24568583756914989/100000000000000),(126140969142137/100000000000000),(95075105387/100000000000000),(-42924497/5000000000000)⟩
def e298 : ℝ := (1832004683/100000000000000)
theorem h298 : Model (fun x => f298 ((117/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(3622921877741527/12500000000000),(204282228668533/100000000000000),(13094885521/4000000000000),(-1362421457/100000000000000)⟩
def e299 : ℝ := (118967099/4000000000000)
theorem h299 : Model (fun x => f299 ((117/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(1810359748394573/6250000000000),(204282228668533/100000000000000),(13094885521/4000000000000),(-1362421457/100000000000000)⟩
def e300 : ℝ := (743544369/25000000000000)
theorem h300 : Model (fun x => f300 ((117/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(34170686292041649/100000000000000),(153196745458903/50000000000000),(153078472599/20000000000000),(-1690820173/100000000000000)⟩
def e301 : ℝ := (894524289/20000000000000)
theorem h301 : Model (fun x => f301 ((117/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(17087009812687491/50000000000000),(153196745458903/50000000000000),(153078472599/20000000000000),(-1690820173/100000000000000)⟩
def e302 : ℝ := (2236310723/50000000000000)
theorem h302 : Model (fun x => f302 ((117/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(6140816451830239/100000000000000),(33054975182447/25000000000000),(366267733431/50000000000000),(67111243/25000000000000)⟩
def e303 : ℝ := (486794089/25000000000000)
theorem h303 : Model (fun x => f303 ((117/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(34791862332611/25000000000000),(26636884293/5000000000000),(-158623853/100000000000000),(-1633471/50000000000000)⟩
def e304 : ℝ := (1928557/25000000000000)
theorem h304 : Model (fun x => f304 ((117/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(27246156773167/12500000000000),(112897570121/50000000000000),(-141659433/50000000000000),(-842381/100000000000000)⟩
def e305 : ℝ := (1631033/50000000000000)
theorem h305 : Model (fun x => f305 ((117/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(118776489425279/25000000000000),(123040995793/12500000000000),(-145052317/20000000000000),(-618963/12500000000000)⟩
def e306 : ℝ := (355959/2500000000000)
theorem h306 : Model (fun x => f306 ((117/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(51779245629561/5000000000000),(3218298490467/100000000000000),(-88043421/12500000000000),(-19221787/100000000000000)⟩
def e307 : ℝ := (582691/1250000000000)
theorem h307 : Model (fun x => f307 ((117/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(451451342086189/20000000000000),(9353201622839/100000000000000),(1398746727/50000000000000),(-30664793/50000000000000)⟩
def e308 : ℝ := (135667417/100000000000000)
theorem h308 : Model (fun x => f308 ((117/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(392670823593379/12500000000000),(6260467323077/25000000000000),(25070341299/50000000000000),(-31805439/20000000000000)⟩
def e309 : ℝ := (365016279/100000000000000)
theorem h309 : Model (fun x => f309 ((117/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(14746156773167/1562500000000),(112897570121/6250000000000),(-141659433/6250000000000),(-842381/12500000000000)⟩
def e310 : ℝ := (1631033/6250000000000)
theorem h310 : Model (fun x => f310 ((117/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(270730370703283/25000000000000),(584774701949/25000000000000),(-2425174781/100000000000000),(-1000599/10000000000000)⟩
def e311 : ℝ := (8452689/25000000000000)
theorem h311 : Model (fun x => f311 ((117/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(295730370703283/25000000000000),(584774701949/25000000000000),(-2425174781/100000000000000),(-1000599/10000000000000)⟩
def e312 : ℝ := (8452689/25000000000000)
theorem h312 : Model (fun x => f312 ((117/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(37159900232202693/100000000000000),(369705319982579/100000000000000),(551347670929/50000000000000),(-162996067/10000000000000)⟩
def e313 : ℝ := (1351112349/25000000000000)
theorem h313 : Model (fun x => f313 ((117/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(2102400693/781250000000),(-66933977/2500000000000),(18651571/100000000000000),(-94313/100000000000000)⟩
def e314 : ℝ := (8041/20000000000000)
theorem h314 : Model (fun x => f314 ((117/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (3678908518246819/10000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(16525384657809/100000000000000),(191401683121/100000000000000),(-105834111/25000000000000),(-207/1000000000000)⟩
def e315 : ℝ := (7820247/100000000000000)
theorem h315 : Model (fun x => f315 ((117/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(36332990579407/100000000000000),(58332299241/12500000000000),(-12183967/3125000000000),(-1303139/100000000000000)⟩
def e316 : ℝ := (11488569/100000000000000)
theorem h316 : Model (fun x => f316 ((117/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(4471899870217/3125000000000),(1141121827311/100000000000000),(-2872613533/20000000000000),(-75531867/100000000000000)⟩
def e317 : ℝ := (46438699/100000000000000)
theorem h317 : Model (fun x => f317 ((117/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(48923349007501/100000000000000),(-7005290417/25000000000000),(-4670953377/100000000000000),(14099817/100000000000000)⟩
def e318 : ℝ := (16661593/100000000000000)
theorem h318 : Model (fun x => f318 ((117/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-29747329936461/25000000000000),(-145520792089/50000000000000),(403621107/20000000000000),(-58781561/100000000000000)⟩
def e319 : ℝ := (14211207/50000000000000)
theorem h319 : Model (fun x => f319 ((117/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((117/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-150579/1600),(-1287/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((117/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((117/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(11349/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((117/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(303381/1600),(653/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((117/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((117/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(476181/1600),(653/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((117/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2380905/32),(3265/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((117/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((117/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(219515806421566513/20000000000000),(34312211832807/12500000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (7087/5000000000000)
theorem h329 : Model (fun x => f329 ((117/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4555480611/50000000000000),(-455719/20000000000000),(76067/20000000000000),(-191/100000000000000)⟩
def e330 : ℝ := (19/100000000000000)
theorem h330 : Model (fun x => f330 ((117/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (274314696199312823/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(677885410258309/100000000000000),(422417644931/25000000000000),(12173731581/100000000000000),(67317419/100000000000000)⟩
def e331 : ℝ := (105529/5000000000000)
theorem h331 : Model (fun x => f331 ((117/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((117/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(477/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((117/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((117/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((117/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(835806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((117/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((117/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((117/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1854024647072407/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (11/1000000000000)
theorem h339 : Model (fun x => f339 ((117/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3934193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((117/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((117/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((117/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2216950705854927/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1099/100000000000000)
theorem h343 : Model (fun x => f343 ((117/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4510700203477/100000000000000),(-716585939/12500000000000),(7285721/100000000000000),(-463/5000000000000)⟩
def e344 : ℝ := (17/100000000000000)
theorem h344 : Model (fun x => f344 ((117/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2214133164219347/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(167258987056017/100000000000000),(157602663161/20000000000000),(-200298579/20000000000000),(636393/50000000000000)⟩
def e345 : ℝ := (2741/100000000000000)
theorem h345 : Model (fun x => f345 ((117/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(267258987056017/100000000000000),(157602663161/20000000000000),(-200298579/20000000000000),(636393/50000000000000)⟩
def e346 : ℝ := (2741/100000000000000)
theorem h346 : Model (fun x => f346 ((117/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(16703686691001/12500000000000),(197003328951/50000000000000),(-31296653/6250000000000),(636393/100000000000000)⟩
def e347 : ℝ := (343/25000000000000)
theorem h347 : Model (fun x => f347 ((117/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(4203686691001/12500000000000),(197003328951/50000000000000),(-31296653/6250000000000),(636393/100000000000000)⟩
def e348 : ℝ := (343/25000000000000)
theorem h348 : Model (fun x => f348 ((117/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(98631292842101/20000000000000),(363518047469/25000000000000),(-461998211/25000000000000),(2348593/100000000000000)⟩
def e349 : ℝ := (1013/20000000000000)
theorem h349 : Model (fun x => f349 ((117/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(284887074992479/10000000000000),(363518047469/25000000000000),(-461998211/25000000000000),(2348593/100000000000000)⟩
def e350 : ℝ := (2533/50000000000000)
theorem h350 : Model (fun x => f350 ((117/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(190346577719603/5000000000000),(13167809732589/100000000000000),(-687871333/6250000000000),(6705997/100000000000000)⟩
def e351 : ℝ := (36841/50000000000000)
theorem h351 : Model (fun x => f351 ((117/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(2272328126693253/25000000000000),(13167809732589/100000000000000),(-687871333/6250000000000),(6705997/100000000000000)⟩
def e352 : ℝ := (73683/100000000000000)
theorem h352 : Model (fun x => f352 ((117/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(12146002267978663/100000000000000),(10681714777719/20000000000000),(-4169773067/50000000000000),(-42496543/100000000000000)⟩
def e353 : ℝ := (194539/50000000000000)
theorem h353 : Model (fun x => f353 ((117/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(8707524943513141/50000000000000),(10681714777719/20000000000000),(-4169773067/50000000000000),(-42496543/100000000000000)⟩
def e354 : ℝ := (389079/100000000000000)
theorem h354 : Model (fun x => f354 ((117/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(465432859233663/2000000000000),(139986062819699/100000000000000),(112084000023/100000000000000),(-246259661/100000000000000)⟩
def e355 : ℝ := (487749/50000000000000)
theorem h355 : Model (fun x => f355 ((117/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(5121471449479487/20000000000000),(139986062819699/100000000000000),(112084000023/100000000000000),(-246259661/100000000000000)⟩
def e356 : ℝ := (975499/100000000000000)
theorem h356 : Model (fun x => f356 ((117/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(17109490897802421/50000000000000),(287957359223259/100000000000000),(286551878679/50000000000000),(-106367231/25000000000000)⟩
def e357 : ℝ := (2303283/100000000000000)
theorem h357 : Model (fun x => f357 ((117/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(17310681373992897/50000000000000),(287957359223259/100000000000000),(286551878679/50000000000000),(-106367231/25000000000000)⟩
def e358 : ℝ := (575821/25000000000000)
theorem h358 : Model (fun x => f358 ((117/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(46264351692627849/100000000000000),(260603217495067/50000000000000),(431760392849/25000000000000),(467906673/100000000000000)⟩
def e359 : ℝ := (6285331/100000000000000)
theorem h359 : Model (fun x => f359 ((117/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(46246732645008801/100000000000000),(260603217495067/50000000000000),(431760392849/25000000000000),(467906673/100000000000000)⟩
def e360 : ℝ := (1571333/25000000000000)
theorem h360 : Model (fun x => f360 ((117/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(30899637303388599/50000000000000),(439350362498087/50000000000000),(4129846089113/100000000000000),(19977767/390625000000)⟩
def e361 : ℝ := (6280891/50000000000000)
theorem h361 : Model (fun x => f361 ((117/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(61802607940110531/100000000000000),(439350362498087/50000000000000),(4129846089113/100000000000000),(19977767/390625000000)⟩
def e362 : ℝ := (12561783/100000000000000)
theorem h362 : Model (fun x => f362 ((117/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(20783904037359629/100000000000000),(539008993484253/100000000000000),(4541511318741/100000000000000),(279700587/2000000000000)⟩
def e363 : ℝ := (509871/5000000000000)
theorem h363 : Model (fun x => f363 ((117/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(178568415405519/100000000000000),(526509101421/50000000000000),(10706129/5000000000000),(-561283/25000000000000)⟩
def e364 : ℝ := (1401/12500000000000)
theorem h364 : Model (fun x => f364 ((117/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(29203686691001/12500000000000),(197003328951/50000000000000),(-31296653/6250000000000),(636393/100000000000000)⟩
def e365 : ℝ := (343/25000000000000)
theorem h365 : Model (fun x => f365 ((117/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(109165480492307/20000000000000),(920515759323/50000000000000),(-196842579/25000000000000),(-486173/50000000000000)⟩
def e366 : ℝ := (109/781250000000)
theorem h366 : Model (fun x => f366 ((117/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(637606897953983/50000000000000),(1290357783811/20000000000000),(1340523073/50000000000000),(-1389909/12500000000000)⟩
def e367 : ℝ := (10399/20000000000000)
theorem h367 : Model (fun x => f367 ((117/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1489637766389533/50000000000000),(10048854516723/50000000000000),(25298604639/100000000000000),(-9901533/25000000000000)⟩
def e368 : ℝ := (77759/50000000000000)
theorem h368 : Model (fun x => f368 ((117/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(5320045109447911/100000000000000),(67260474226817/100000000000000),(2056149637/781250000000),(85909967/50000000000000)⟩
def e369 : ℝ := (1430283/100000000000000)
theorem h369 : Model (fun x => f369 ((117/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(16703686691001/1562500000000),(197003328951/6250000000000),(-31296653/781250000000),(636393/12500000000000)⟩
def e370 : ℝ := (343/3125000000000)
theorem h370 : Model (fun x => f370 ((117/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(1247604363629583/100000000000000),(2102535733029/50000000000000),(-947962251/25000000000000),(711503/25000000000000)⟩
def e371 : ℝ := (2773/12500000000000)
theorem h371 : Model (fun x => f371 ((117/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1347604363629583/100000000000000),(2102535733029/50000000000000),(-947962251/25000000000000),(711503/25000000000000)⟩
def e372 : ℝ := (2773/12500000000000)
theorem h372 : Model (fun x => f372 ((117/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(71693160041982273/100000000000000),(226023356911469/20000000000000),(1234668899543/20000000000000),(2745913581/25000000000000)⟩
def e373 : ℝ := (10685591/50000000000000)
theorem h373 : Model (fun x => f373 ((117/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(139483320223/100000000000000),(-219870963/10000000000000),(11324093/50000000000000),(-189053/100000000000000)⟩
def e374 : ℝ := (181/12500000000000)
theorem h374 : Model (fun x => f374 ((117/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (70556858907901707/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(28990079423271/100000000000000),(294849940853/100000000000000),(-809414627/100000000000000),(2435301/100000000000000)⟩
def e375 : ℝ := (156663/25000000000000)
theorem h375 : Model (fun x => f375 ((117/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(167258987056017/50000000000000),(157602663161/10000000000000),(-200298579/10000000000000),(636393/25000000000000)⟩
def e376 : ℝ := (2741/50000000000000)
theorem h376 : Model (fun x => f376 ((117/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(37416889550299/100000000000000),(-55161862893/50000000000000),(116375239/25000000000000),(-1964137/100000000000000)⟩
def e377 : ℝ := (8483/100000000000000)
theorem h377 : Model (fun x => f377 ((117/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (26646997097179/10000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(125166220899397/100000000000000),(13790465723/6250000000000),(-931001913/100000000000000),(392827/10000000000000)⟩
def e378 : ℝ := (73709/100000000000000)
theorem h378 : Model (fun x => f378 ((117/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(25166220899397/100000000000000),(13790465723/6250000000000),(-931001913/100000000000000),(392827/10000000000000)⟩
def e379 : ℝ := (73709/100000000000000)
theorem h379 : Model (fun x => f379 ((117/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(461922958081107/100000000000000),(1628588333/200000000000),(-1717920197/50000000000000),(7248593/50000000000000)⟩
def e380 : ℝ := (10881/4000000000000)
theorem h380 : Model (fun x => f380 ((117/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(44025581934303/1562500000000),(1628588333/200000000000),(-1717920197/50000000000000),(7248593/50000000000000)⟩
def e381 : ℝ := (136013/50000000000000)
theorem h381 : Model (fun x => f381 ((117/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3526730056712621/100000000000000),(7236266008077/100000000000000),(-7184012223/25000000000000),(113667789/100000000000000)⟩
def e382 : ℝ := (2514779/100000000000000)
theorem h382 : Model (fun x => f382 ((117/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8809111009093573/100000000000000),(7236266008077/100000000000000),(-7184012223/25000000000000),(113667789/100000000000000)⟩
def e383 : ℝ := (125739/5000000000000)
theorem h383 : Model (fun x => f383 ((117/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(11026031344915161/100000000000000),(14247219821949/50000000000000),(-12751772739/12500000000000),(178772103/50000000000000)⟩
def e384 : ℝ := (10456483/100000000000000)
theorem h384 : Model (fun x => f384 ((117/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(814753948198139/5000000000000),(14247219821949/50000000000000),(-12751772739/12500000000000),(178772103/50000000000000)⟩
def e385 : ℝ := (2614121/25000000000000)
theorem h385 : Model (fun x => f385 ((117/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(815837381270593/4000000000000),(71620089733703/100000000000000),(-27065317281/12500000000000),(298631899/50000000000000)⟩
def e386 : ℝ := (28008531/100000000000000)
theorem h386 : Model (fun x => f386 ((117/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(2273164881747911/10000000000000),(71620089733703/100000000000000),(-27065317281/12500000000000),(298631899/50000000000000)⟩
def e387 : ℝ := (7002133/25000000000000)
theorem h387 : Model (fun x => f387 ((117/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(7113086443240267/25000000000000),(34950240884897/25000000000000),(-16230863053/5000000000000),(495997197/100000000000000)⟩
def e388 : ℝ := (58088703/100000000000000)
theorem h388 : Model (fun x => f388 ((117/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(1442736336267101/5000000000000),(34950240884897/25000000000000),(-16230863053/5000000000000),(495997197/100000000000000)⟩
def e389 : ℝ := (226909/390625000000)
theorem h389 : Model (fun x => f389 ((117/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(7223274198591787/20000000000000),(238650802019823/100000000000000),(-366481952543/100000000000000),(-263496839/100000000000000)⟩
def e390 : ℝ := (25958429/25000000000000)
theorem h390 : Model (fun x => f390 ((117/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(36098751945339887/100000000000000),(238650802019823/100000000000000),(-366481952543/100000000000000),(-263496839/100000000000000)⟩
def e391 : ℝ := (103833717/100000000000000)
theorem h391 : Model (fun x => f391 ((117/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(22591721800914747/50000000000000),(9459029156239/2500000000000),(-134107384327/50000000000000),(-971114607/50000000000000)⟩
def e392 : ℝ := (169196383/100000000000000)
theorem h392 : Model (fun x => f392 ((117/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(45186776935162827/100000000000000),(9459029156239/2500000000000),(-134107384327/50000000000000),(-971114607/50000000000000)⟩
def e393 : ℝ := (5287387/3125000000000)
theorem h393 : Model (fun x => f393 ((117/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(227436082016417/2000000000000),(48730669662263/25000000000000),(173327496099/50000000000000),(-35351073/1250000000000)⟩
def e394 : ℝ := (89623331/100000000000000)
theorem h394 : Model (fun x => f394 ((117/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(78332914271183/50000000000000),(138088038319/25000000000000),(-460936711/25000000000000),(572527/10000000000000)⟩
def e395 : ℝ := (210923/100000000000000)
theorem h395 : Model (fun x => f395 ((117/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(225166220899397/100000000000000),(13790465723/6250000000000),(-931001913/100000000000000),(392827/10000000000000)⟩
def e396 : ℝ := (73709/100000000000000)
theorem h396 : Model (fun x => f396 ((117/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(12674956758529/2500000000000),(248411764103/25000000000000),(-370575067/10000000000000),(1358181/10000000000000)⟩
def e397 : ℝ := (358341/100000000000000)
theorem h397 : Model (fun x => f397 ((117/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(570794422676249/50000000000000),(1678018144501/50000000000000),(-2717951357/25000000000000),(33070391/100000000000000)⟩
def e398 : ℝ := (80367/6250000000000)
theorem h398 : Model (fun x => f398 ((117/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2570472461289281/100000000000000),(10075546778613/100000000000000),(-2770283887/10000000000000),(32037459/50000000000000)⟩
def e399 : ℝ := (1012223/25000000000000)
theorem h399 : Model (fun x => f399 ((117/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(20135259894661/500000000000),(5996599766037/20000000000000),(-35141387341/100000000000000),(-91234813/100000000000000)⟩
def e400 : ℝ := (3313253/25000000000000)
theorem h400 : Model (fun x => f400 ((117/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(125166220899397/12500000000000),(13790465723/781250000000),(-931001913/12500000000000),(392827/1250000000000)⟩
def e401 : ℝ := (73709/12500000000000)
theorem h401 : Model (fun x => f401 ((117/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(578997797868771/50000000000000),(115876588291/5000000000000),(-2322940537/25000000000000),(3715143/10000000000000)⟩
def e402 : ℝ := (160119/20000000000000)
theorem h402 : Model (fun x => f402 ((117/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(628997797868771/50000000000000),(115876588291/5000000000000),(-2322940537/25000000000000),(3715143/10000000000000)⟩
def e403 : ℝ := (160119/20000000000000)
theorem h403 : Model (fun x => f403 ((117/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(50660136533028603/100000000000000),(235256506795801/50000000000000),(-24279134851/20000000000000),(-812996071/25000000000000)⟩
def e404 : ℝ := (105902987/50000000000000)
theorem h404 : Model (fun x => f404 ((117/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(39478772401/20000000000000),(-7161417/390625000000),(2187531/12500000000000),(-77129/50000000000000)⟩
def e405 : ℝ := (1107/50000000000000)
theorem h405 : Model (fun x => f405 ((117/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (6273687332496561/12500000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(22447243294253/100000000000000),(35256706283/20000000000000),(-44959611/5000000000000),(4632261/100000000000000)⟩
def e406 : ℝ := (2437/390625000000)
theorem h406 : Model (fun x => f406 ((117/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(12859330679381/25000000000000),(117783368067/25000000000000),(-1708606847/100000000000000),(3533781/50000000000000)⟩
def e407 : ℝ := (312631/25000000000000)
theorem h407 : Model (fun x => f407 ((117/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(348686106129577/100000000000000),(4062866380303/100000000000000),(2640048737/100000000000000),(55510473/50000000000000)⟩
def e408 : ℝ := (9822879/100000000000000)
theorem h408 : Model (fun x => f408 ((117/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(14901115646563/12500000000000),(370134444781/100000000000000),(-2260961501/100000000000000),(11456067/20000000000000)⟩
def e409 : ℝ := (5164299/100000000000000)
theorem h409 : Model (fun x => f409 ((117/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(10980271333/5000000000000),(79092860603/100000000000000),(-121427983/50000000000000),(-750613/50000000000000)⟩
def e410 : ℝ := (33586713/100000000000000)
theorem h410 : Model (fun x => f410 ((117/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1795656078918457/6250000000000),(291309005126953/25000000000000),(1930149/10240000),(15561/10240000)⟩
def e411 : ℝ := (305664063/50000000000000)
theorem h411 : Model (fun x => f411 ((117/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(56169/1600),(237/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((117/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(13312053/64000),(168507/64000),(711/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((117/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(1195193444616734113/20000000000000),(318015211949282487/100000000000000),(7307784041631041/100000000000000),(47315301284729/50000000000000)⟩
def e414 : ℝ := (379236659553/50000000000000)
theorem h414 : Model (fun x => f414 ((117/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(334673857/20000000000000),(-178099/200000000000),(269253/10000000000000),(-7611/12500000000000)⟩
def e415 : ℝ := (171/10000000000000)
theorem h415 : Model (fun x => f415 ((117/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (5650548838016868473/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2662278266171/50000000000000),(-1853604683/10000000000000),(-16478011/25000000000000),(1807/78125000000)⟩
def e416 : ℝ := (2060257/20000000000000)
theorem h416 : Model (fun x => f416 ((117/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2772080979501/50000000000000),(60556813773/100000000000000),(-30876801/10000000000000),(405867/50000000000000)⟩
def e417 : ℝ := (21943999/50000000000000)
theorem h417 : Model (fun x => f417 ((117/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((117/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((2772007574167/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (29/10) (59/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (29/10) (59/20) ≤ (554410292433/200000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(117/40)-(1/40)) (by norm_num : ((117/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel38


noncomputable section
namespace Hf4Quad.Panel39
open Hf4Quad.Dag

def p0 : Cubic := ⟨(119/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((119/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((119/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((119/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((119/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(521333333333333/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((119/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-521333333333333/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((119/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-214952380952381/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((119/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((119/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(14161/1600),(119/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((119/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(53572037037037/5000000000000),(18007407407407/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((119/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-53572037037037/5000000000000),(-18007407407407/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((119/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-750672751322751/50000000000000),(-22388359788359/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((119/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((119/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1685159/64000),(42483/64000),(357/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((119/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(25652839985532407/100000000000000),(646710251736111/100000000000000),(1086907986111/20000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((119/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-25652839985532407/100000000000000),(-646710251736111/100000000000000),(-1086907986111/20000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((119/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-27154185488177909/100000000000000),(-66909861152447/10000000000000),(-688775163277/12500000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((119/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((119/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(200533921/2560000),(1685159/640000),(42483/1280000),(119/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((119/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(2735457751736111/12500000000000),(735585277777777/100000000000000),(9272083333333/100000000000000),(12986111111/25000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((119/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-5270523474289021/100000000000000),(66486666253307/100000000000000),(3761882027117/100000000000000),(36721643519/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((119/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((119/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(23304234959960937/100000000000000),(244792384033203/25000000000000),(1685159/10240000),(14161/10240000)⟩
def e22 : ℝ := (582031251/100000000000000)
theorem h22 : Model (fun x => f22 ((119/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(30364555033015769/20000000000000),(6379108200213393/100000000000000),(53605951262297/50000000000000),(900940357349/100000000000000)⟩
def e23 : ℝ := (3791825819/100000000000000)
theorem h23 : Model (fun x => f23 ((119/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(2289878932668591/1562500000000),(64455948664667/1000000000000),(110973784551711/100000000000000),(234415500217/25000000000000)⟩
def e24 : ℝ := (975238203/25000000000000)
theorem h24 : Model (fun x => f24 ((119/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((119/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(69330099005883787/100000000000000),(3495635243994139/100000000000000),(1835942880249/2500000000000),(102853942871/12500000000000)⟩
def e26 : ℝ := (2601684573/50000000000000)
theorem h26 : Model (fun x => f26 ((119/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(19460115091334047/12500000000000),(1962364547025281/25000000000000),(32980916756727/20000000000000),(1847670406537/100000000000000)⟩
def e27 : ℝ := (5842089593/50000000000000)
theorem h27 : Model (fun x => f27 ((119/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(1511165862107311/500000000000),(893440815910489/6250000000000),(137939184167673/50000000000000),(557066481481/20000000000000)⟩
def e28 : ℝ := (7792565999/50000000000000)
theorem h28 : Model (fun x => f28 ((119/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((119/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(103128522271252133/50000000000000),(6066383663014829/50000000000000),(76467020962371/25000000000000),(2141933360289/50000000000000)⟩
def e30 : ℝ := (18090448007/50000000000000)
theorem h30 : Model (fun x => f30 ((119/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(6118140507758807/12500000000000),(359890618103459/12500000000000),(72582981802377/100000000000000),(1016568372581/100000000000000)⟩
def e31 : ℝ := (8585784057/100000000000000)
theorem h31 : Model (fun x => f31 ((119/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(21948643530220791/6250000000000),(2146772249924437/12500000000000),(348461350137723/100000000000000),(1900950389993/50000000000000)⟩
def e32 : ℝ := (4834183211/20000000000000)
theorem h32 : Model (fun x => f32 ((119/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((119/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(6075069/320),(51051/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((119/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((119/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(262871/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((119/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(2056201/64),(68723/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((119/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((119/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(2202121/64),(68723/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((119/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-2202121/64),(-68723/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((119/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((119/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(159/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((119/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(25281/1600),(159/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((119/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((119/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(530901/160),(3339/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((119/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(30137445587/100000000000000),(-189543683/50000000000000),(715259/20000000000000),(-2999/10000000000000)⟩
def e46 : ℝ := (121/50000000000000)
theorem h46 : Model (fun x => f46 ((119/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (262101/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-518486732917891/50000000000000),(99093441767/100000000000000),(-315771341/50000000000000),(4028379/100000000000000)⟩
def e47 : ℝ := (8279021/50000000000000)
theorem h47 : Model (fun x => f47 ((119/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((119/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(199/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((119/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((119/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((119/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(165833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((119/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(265833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((119/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((119/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(26583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((119/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((119/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(558249999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((119/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((119/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((119/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(36751458333331/4000000000000),(14510416666643/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (141/100000000000000)
theorem h60 : Model (fun x => f60 ((119/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(176668402777773/100000000000000),(1107638888887/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((119/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((119/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(26583333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((119/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1505835069444423/100000000000000),(5274305555547/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((119/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1605835069444423/100000000000000),(5274305555547/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((119/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(14754195161222101/100000000000000),(281472964770947/100000000000000),(1366735568567/100000000000000),(271855107/12500000000000)⟩
def e66 : ℝ := (158929/25000000000000)
theorem h66 : Model (fun x => f66 ((119/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(46583333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((119/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(542501736111103/100000000000000),(1940972222219/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((119/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(78973560022423/6250000000000),(6781271701377/100000000000000),(3032769097/25000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (71/100000000000000)
theorem h69 : Model (fun x => f69 ((119/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(186430610743570653/100000000000000),(2278574796859163/50000000000000),(19073522472961/50000000000000),(9710989317/6250000000000)⟩
def e70 : ℝ := (171046133/50000000000000)
theorem h70 : Model (fun x => f70 ((119/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((119/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3710036458333233/12500000000000),(23260416666627/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((119/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(610610167100647/6250000000000),(184920312499691/100000000000000),(871354166657/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1869/100000000000000)
theorem h73 : Model (fun x => f73 ((119/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(12344847022547119/10000000000000),(1499562307623381/50000000000000),(4947071337501/20000000000000),(12198051573/12500000000000)⟩
def e74 : ℝ := (100867023/50000000000000)
theorem h74 : Model (fun x => f74 ((119/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(309879080969041843/100000000000000),(236133569030159/3125000000000),(62882401633427/100000000000000),(31620030207/12500000000000)⟩
def e75 : ℝ := (67978289/12500000000000)
theorem h75 : Model (fun x => f75 ((119/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((119/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1236678819444411/12500000000000),(7753472222209/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((119/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(10835069444443/100000000000000),(54861111111/20000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((119/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(111454490379/3125000000000),(27087673611/20000000000000),(857204861/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((119/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(352853523414221/100000000000000),(3122349736959/20000000000000),(6427270457/2500000000000),(1910757027/100000000000000)⟩
def e80 : ℝ := (770151/12500000000000)
theorem h80 : Model (fun x => f80 ((119/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(821854664952283/100000000000000),(4729073457403/12500000000000),(663856317097/100000000000000),(2760841659/50000000000000)⟩
def e81 : ℝ := (22337657/100000000000000)
theorem h81 : Model (fun x => f81 ((119/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(155350467816997063/50000000000000),(949263349578039/12500000000000),(15886564487631/25000000000000),(129240962487/50000000000000)⟩
def e82 : ℝ := (566163969/100000000000000)
theorem h82 : Model (fun x => f82 ((119/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(586993649329/50000000000000),(14860598717/25000000000000),(1128653067/100000000000000),(4762249/50000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((119/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(24152342863/6250000000000),(24458068721/100000000000000),(619191613/100000000000000),(1959467/25000000000000)⟩
def e84 : ℝ := (6217/12500000000000)
theorem h84 : Model (fun x => f84 ((119/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(63601169539/50000000000000),(1207617143/12500000000000),(152862929/50000000000000),(5159929/100000000000000)⟩
def e85 : ℝ := (1231/2500000000000)
theorem h85 : Model (fun x => f85 ((119/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(20935384973/50000000000000),(1855034111/50000000000000),(70444333/50000000000000),(1486167/50000000000000)⟩
def e86 : ℝ := (9479/25000000000000)
theorem h86 : Model (fun x => f86 ((119/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(62806154919/50000000000000),(5565102333/50000000000000),(211332999/50000000000000),(4458501/50000000000000)⟩
def e87 : ℝ := (28437/25000000000000)
theorem h87 : Model (fun x => f87 ((119/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-62806154919/50000000000000),(-5565102333/50000000000000),(-211332999/50000000000000),(-4458501/50000000000000)⟩
def e88 : ℝ := (28437/25000000000000)
theorem h88 : Model (fun x => f88 ((119/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(4854700156588817/1562500000000),(3797047833209823/50000000000000),(31772917642263/50000000000000),(64618251993/25000000000000)⟩
def e89 : ℝ := (566277717/100000000000000)
theorem h89 : Model (fun x => f89 ((119/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3710036458333233/10000000000000),(23260416666627/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((119/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2943081336835609/100000000000000),(21059616005943/100000000000000),(56510597509/100000000000000),(16848717/25000000000000)⟩
def e91 : ℝ := (30359/100000000000000)
theorem h91 : Model (fun x => f91 ((119/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(272973476487505489/25000000000000),(293178482718233/2000000000000),(40340583028829/50000000000000),(233229596169/100000000000000)⟩
def e92 : ℝ := (46805741/12500000000000)
theorem h92 : Model (fun x => f92 ((119/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(2289599737/25000000000000),(-12295359/10000000000000),(243489/25000000000000),(-5947/100000000000000)⟩
def e93 : ℝ := (1/2500000000000)
theorem h93 : Model (fun x => f93 ((119/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (1077154067044010551/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(28455219716453/100000000000000),(156739888771/50000000000000),(-491342959/100000000000000),(256469/25000000000000)⟩
def e94 : ℝ := (331701/100000000000000)
theorem h94 : Model (fun x => f94 ((119/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(165833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((119/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(18808777429467/50000000000000),(-14740421183/12500000000000),(184832867/50000000000000),(-1158827/100000000000000)⟩
def e96 : ℝ := (57/1562500000000)
theorem h96 : Model (fun x => f96 ((119/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (33124999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(124764890282129/100000000000000),(117923369463/50000000000000),(-369665737/50000000000000),(579413/25000000000000)⟩
def e97 : ℝ := (31481/100000000000000)
theorem h97 : Model (fun x => f97 ((119/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2620062695924709/100000000000000),(2476390758723/50000000000000),(-7762980477/50000000000000),(12167673/25000000000000)⟩
def e98 : ℝ := (661101/100000000000000)
theorem h98 : Model (fun x => f98 ((119/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(24764890282129/100000000000000),(117923369463/50000000000000),(-369665737/50000000000000),(579413/25000000000000)⟩
def e99 : ℝ := (31481/100000000000000)
theorem h99 : Model (fun x => f99 ((119/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(129771130393749/20000000000000),(462867708429/6250000000000),(-230699233/2000000000000),(-457767/100000000000000)⟩
def e100 : ℝ := (668379/50000000000000)
theorem h100 : Model (fun x => f100 ((119/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(38915694617779/25000000000000),(58850785011/10000000000000),(-1288615363/100000000000000),(2295853/100000000000000)⟩
def e101 : ℝ := (95139/100000000000000)
theorem h101 : Model (fun x => f101 ((119/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(124764890282129/10000000000000),(117923369463/5000000000000),(-369665737/5000000000000),(579413/2500000000000)⟩
def e102 : ℝ := (31481/10000000000000)
theorem h102 : Model (fun x => f102 ((119/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(701655840646203/50000000000000),(294697523937/10000000000000),(-8681930103/100000000000000),(25472373/100000000000000)⟩
def e103 : ℝ := (409949/100000000000000)
theorem h103 : Model (fun x => f103 ((119/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(751655840646203/50000000000000),(294697523937/10000000000000),(-8681930103/100000000000000),(25472373/100000000000000)⟩
def e104 : ℝ := (409949/100000000000000)
theorem h104 : Model (fun x => f104 ((119/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(4877161405386071/50000000000000),(130455124678669/100000000000000),(-2872517989/25000000000000),(-206127203/25000000000000)⟩
def e105 : ℝ := (12851429/50000000000000)
theorem h105 : Model (fun x => f105 ((119/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(224764890282129/100000000000000),(117923369463/50000000000000),(-369665737/50000000000000),(579413/25000000000000)⟩
def e106 : ℝ := (31481/100000000000000)
theorem h106 : Model (fun x => f106 ((119/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(252596279517687/50000000000000),(530100663981/50000000000000),(-2767278311/100000000000000),(6931157/100000000000000)⟩
def e107 : ℝ := (158101/100000000000000)
theorem h107 : Model (fun x => f107 ((119/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(567747750514669/50000000000000),(714888105469/20000000000000),(-1490893479/20000000000000),(516899/4000000000000)⟩
def e108 : ℝ := (576599/100000000000000)
theorem h108 : Model (fun x => f108 ((119/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(55379948336098069/50000000000000),(1829974539304797/100000000000000),(761087756571/20000000000000),(-18237201063/100000000000000)⟩
def e109 : ℝ := (361588161/100000000000000)
theorem h109 : Model (fun x => f109 ((119/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(817229586973359/3125000000000),(1235866485231/1250000000000),(-27060922623/12500000000000),(48212913/12500000000000)⟩
def e110 : ℝ := (1997919/12500000000000)
theorem h110 : Model (fun x => f110 ((119/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(6476352338145547/100000000000000),(86161976901367/100000000000000),(-13777935787/100000000000000),(-539934209/100000000000000)⟩
def e111 : ℝ := (2133691/12500000000000)
theorem h111 : Model (fun x => f111 ((119/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(2941547577218041/4000000000000),(1209858733981289/100000000000000),(488116641419/20000000000000),(-3052356059/25000000000000)⟩
def e112 : ℝ := (29931431/12500000000000)
theorem h112 : Model (fun x => f112 ((119/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(184298586102647163/100000000000000),(1519916636643043/50000000000000),(124920439799/2000000000000),(-30446625299/100000000000000)⟩
def e113 : ℝ := (601039609/100000000000000)
theorem h113 : Model (fun x => f113 ((119/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(272409862324453/3125000000000),(411955495077/1250000000000),(-9020307541/12500000000000),(16070971/12500000000000)⟩
def e114 : ℝ := (665973/12500000000000)
theorem h114 : Model (fun x => f114 ((119/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(3066498953429/50000000000000),(58407186129/50000000000000),(38009517/20000000000000),(-2339451/100000000000000)⟩
def e115 : ℝ := (32177/100000000000000)
theorem h115 : Model (fun x => f115 ((119/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(759415101319/50000000000000),(8678685337/20000000000000),(277224779/100000000000000),(-426323/50000000000000)⟩
def e116 : ℝ := (3563/25000000000000)
theorem h116 : Model (fun x => f116 ((119/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(33099546111587/25000000000000),(4283207522947/100000000000000),(37370907657/100000000000000),(-12323759/100000000000000)⟩
def e117 : ℝ := (1756557/100000000000000)
theorem h117 : Model (fun x => f117 ((119/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(74396158501591/25000000000000),(9939403489921/100000000000000),(5819976463/6250000000000),(31840011/100000000000000)⟩
def e118 : ℝ := (420237/10000000000000)
theorem h118 : Model (fun x => f118 ((119/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(184596170736653527/100000000000000),(3049772676776007/100000000000000),(3169570806679/50000000000000),(-3801848161/12500000000000)⟩
def e119 : ℝ := (605241979/100000000000000)
theorem h119 : Model (fun x => f119 ((119/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(75227326651/20000000000000),(1432844601/10000000000000),(39941801/25000000000000),(19631/12500000000000)⟩
def e120 : ℝ := (57/800000000000)
theorem h120 : Model (fun x => f120 ((119/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(11643728067/12500000000000),(1108882479/25000000000000),(4411153/6250000000000),(318481/100000000000000)⟩
def e121 : ℝ := (2389/100000000000000)
theorem h121 : Model (fun x => f121 ((119/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(5767112961/25000000000000),(65907247/5000000000000),(27251041/100000000000000),(107347/50000000000000)⟩
def e122 : ℝ := (963/100000000000000)
theorem h122 : Model (fun x => f122 ((119/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(1428219197/25000000000000),(380843339/100000000000000),(9686939/100000000000000),(27057/25000000000000)⟩
def e123 : ℝ := (147/25000000000000)
theorem h123 : Model (fun x => f123 ((119/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(4284657591/25000000000000),(1142530017/100000000000000),(29060817/100000000000000),(81171/25000000000000)⟩
def e124 : ℝ := (441/25000000000000)
theorem h124 : Model (fun x => f124 ((119/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-4284657591/25000000000000),(-1142530017/100000000000000),(-29060817/100000000000000),(-81171/25000000000000)⟩
def e125 : ℝ := (441/25000000000000)
theorem h125 : Model (fun x => f125 ((119/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(184596153598023163/100000000000000),(304977153424599/10000000000000),(6339112552541/100000000000000),(-7603777493/25000000000000)⟩
def e126 : ℝ := (605243743/100000000000000)
theorem h126 : Model (fun x => f126 ((119/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(817229586973359/2500000000000),(1235866485231/1000000000000),(-27060922623/10000000000000),(48212913/10000000000000)⟩
def e127 : ℝ := (1997919/10000000000000)
theorem h127 : Model (fun x => f127 ((119/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1276097608523551/50000000000000),(2678029109829/25000000000000),(-4179974917/25000000000000),(5676969/50000000000000)⟩
def e128 : ℝ := (1824653/100000000000000)
theorem h128 : Model (fun x => f128 ((119/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(834291777241114197/100000000000000),(1663968982460117/25000000000000),(433335642273/50000000000000),(-1345406113/4000000000000)⟩
def e129 : ℝ := (61090539/5000000000000)
theorem h129 : Model (fun x => f129 ((119/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(11986214263/100000000000000),(-47812263/50000000000000),(750429/100000000000000),(-1081/20000000000000)⟩
def e130 : ℝ := (59/100000000000000)
theorem h130 : Model (fun x => f130 ((119/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (413817499891512789/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(4425218098303/20000000000000),(94516476867/50000000000000),(-192811723/25000000000000),(3201581/100000000000000)⟩
def e131 : ℝ := (68151/25000000000000)
theorem h131 : Model (fun x => f131 ((119/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(1580665943999/3125000000000),(125628182819/25000000000000),(-1262589851/100000000000000),(4227457/100000000000000)⟩
def e132 : ℝ := (120861/20000000000000)
theorem h132 : Model (fun x => f132 ((119/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-262257382764357/50000000000000),(-5160800924603/100000000000000),(6635618167/50000000000000),(-46224727/100000000000000)⟩
def e133 : ℝ := (7379131/50000000000000)
theorem h133 : Model (fun x => f133 ((119/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(33613445378151/100000000000000),(-70616481887/25000000000000),(296707907/12500000000000),(-19946751/100000000000000)⟩
def e134 : ℝ := (169043/100000000000000)
theorem h134 : Model (fun x => f134 ((119/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (59/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-44076871052833/25000000000000),(-25314750229/10000000000000),(1317641943/20000000000000),(-35450413/50000000000000)⟩
def e135 : ℝ := (1475391/20000000000000)
theorem h135 : Model (fun x => f135 ((119/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(200533921/256000),(1685159/64000),(42483/128000),(119/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((119/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((119/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(15166431/32000),(382347/32000),(3213/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((119/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(321865369/256000),(2449853/64000),(11067/25600),(137/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((119/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-14161/1600),(-119/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((119/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(319599609/256000),(2440333/64000),(11051/25600),(137/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((119/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((119/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(357/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((119/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-357/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((119/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(315030009/256000),(2430733/64000),(11051/25600),(137/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((119/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(315798009/256000),(2430733/64000),(11051/25600),(137/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((119/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((119/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(315798009/4000),(2430733/1000),(11051/400),(137/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((119/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((119/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(37900911069/512000),(318495051/128000),(8029287/256000),(22491/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((119/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(1350891009/100000000000000),(-22704051/50000000000000),(953951/100000000000000),(-16033/100000000000000)⟩
def e151 : ℝ := (53/20000000000000)
theorem h151 : Model (fun x => f151 ((119/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (18305391069/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(2133043455091/2000000000000),(-150645848019/50000000000000),(2260725973/100000000000000),(-2054683/12500000000000)⟩
def e152 : ℝ := (41074467/100000000000000)
theorem h152 : Model (fun x => f152 ((119/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(239/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((119/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(47561/1600),(219/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((119/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(477/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((119/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(20964360587/500000000000),(-2637026489/10000000000000),(82925361/50000000000000),(-1043087/100000000000000)⟩
def e156 : ℝ := (1321/20000000000000)
theorem h156 : Model (fun x => f156 ((119/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (237/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(31158936058697/25000000000000),(363926136867/100000000000000),(331701427/100000000000000),(-1043097/50000000000000)⟩
def e157 : ℝ := (380693/100000000000000)
theorem h157 : Model (fun x => f157 ((119/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(56158936058697/25000000000000),(363926136867/100000000000000),(331701427/100000000000000),(-1043097/50000000000000)⟩
def e158 : ℝ := (380693/100000000000000)
theorem h158 : Model (fun x => f158 ((119/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(56158936058697/50000000000000),(181963068433/100000000000000),(165850713/100000000000000),(-1043097/100000000000000)⟩
def e159 : ℝ := (47587/25000000000000)
theorem h159 : Model (fun x => f159 ((119/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(6158936058697/50000000000000),(181963068433/100000000000000),(165850713/100000000000000),(-1043097/100000000000000)⟩
def e160 : ℝ := (47587/25000000000000)
theorem h160 : Model (fun x => f160 ((119/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((119/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((119/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(25906652050887/6250000000000),(671530371597/100000000000000),(612068107/100000000000000),(-153981/4000000000000)⟩
def e163 : ℝ := (702477/100000000000000)
theorem h163 : Model (fun x => f163 ((119/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2770220718528477/100000000000000),(671530371597/100000000000000),(612068107/100000000000000),(-153981/4000000000000)⟩
def e164 : ℝ := (351239/50000000000000)
theorem h164 : Model (fun x => f164 ((119/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((119/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(3111452964006367/100000000000000),(28975136229/500000000000),(1625957489/25000000000000),(-15496159/50000000000000)⟩
def e166 : ℝ := (6077637/100000000000000)
theorem h166 : Model (fun x => f166 ((119/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8393833916387319/100000000000000),(28975136229/500000000000),(1625957489/25000000000000),(-15496159/50000000000000)⟩
def e167 : ℝ := (3038819/50000000000000)
theorem h167 : Model (fun x => f167 ((119/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((119/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(9427775643954353/100000000000000),(10891264522267/50000000000000),(7942751551/25000000000000),(-1261501/1250000000000)⟩
def e169 : ℝ := (11466029/50000000000000)
theorem h169 : Model (fun x => f169 ((119/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3674205815750493/25000000000000),(10891264522267/50000000000000),(7942751551/25000000000000),(-1261501/1250000000000)⟩
def e170 : ℝ := (22932059/100000000000000)
theorem h170 : Model (fun x => f170 ((119/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((119/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(8253579578928983/50000000000000),(51208463687707/100000000000000),(2492386563/2500000000000),(-21589429/12500000000000)⟩
def e172 : ℝ := (2708693/5000000000000)
theorem h172 : Model (fun x => f172 ((119/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(18842873443572251/100000000000000),(51208463687707/100000000000000),(2492386563/2500000000000),(-21589429/12500000000000)⟩
def e173 : ℝ := (54173861/100000000000000)
theorem h173 : Model (fun x => f173 ((119/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((119/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(169311315980751/800000000000),(91803327456911/100000000000000),(236407353879/100000000000000),(-124201221/100000000000000)⟩
def e175 : ℝ := (9759471/10000000000000)
theorem h175 : Model (fun x => f175 ((119/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(21566295449974827/100000000000000),(91803327456911/100000000000000),(236407353879/100000000000000),(-124201221/100000000000000)⟩
def e176 : ℝ := (97594711/100000000000000)
theorem h176 : Model (fun x => f176 ((119/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((119/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(24222804143962087/100000000000000),(71177118440333/50000000000000),(468343715741/100000000000000),(108986499/50000000000000)⟩
def e178 : ℝ := (151814451/100000000000000)
theorem h178 : Model (fun x => f178 ((119/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(24205185096343039/100000000000000),(71177118440333/50000000000000),(468343715741/100000000000000),(108986499/50000000000000)⟩
def e179 : ℝ := (37953613/25000000000000)
theorem h179 : Model (fun x => f179 ((119/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((119/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(13593374421144543/50000000000000),(203933747254511/100000000000000),(825210305253/100000000000000),(540323593/50000000000000)⟩
def e181 : ℝ := (217453247/100000000000000)
theorem h181 : Model (fun x => f181 ((119/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(27190082175622419/100000000000000),(203933747254511/100000000000000),(825210305253/100000000000000),(540323593/50000000000000)⟩
def e182 : ℝ := (3397707/1562500000000)
theorem h182 : Model (fun x => f182 ((119/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(3349239551007509/100000000000000),(18649051506809/25000000000000),(16182106229/3125000000000),(1689297373/100000000000000)⟩
def e183 : ℝ := (16108359/20000000000000)
theorem h183 : Model (fun x => f183 ((119/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(492785328007/390625000000),(204377046503/50000000000000),(351832783/50000000000000),(-347919/20000000000000)⟩
def e184 : ℝ := (43181/10000000000000)
theorem h184 : Model (fun x => f184 ((119/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(106158936058697/50000000000000),(181963068433/100000000000000),(165850713/100000000000000),(-1043097/100000000000000)⟩
def e185 : ℝ := (47587/25000000000000)
theorem h185 : Model (fun x => f185 ((119/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(22539439410229/5000000000000),(48292514367/6250000000000),(64710437/6250000000000),(-3825789/100000000000000)⟩
def e186 : ℝ := (406253/50000000000000)
theorem h186 : Model (fun x => f186 ((119/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(3828420651439/400000000000),(492161466701/20000000000000),(6799841/156250000000),(-9659517/100000000000000)⟩
def e187 : ℝ := (2599439/100000000000000)
theorem h187 : Model (fun x => f187 ((119/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(2032105315709539/100000000000000),(1741577922469/25000000000000),(1913123001/12500000000000),(-18492303/100000000000000)⟩
def e188 : ℝ := (923303/12500000000000)
theorem h188 : Model (fun x => f188 ((119/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(512712542487907/20000000000000),(17094527901357/100000000000000),(3104100637/5000000000000),(52900279/100000000000000)⟩
def e189 : ℝ := (18242901/100000000000000)
theorem h189 : Model (fun x => f189 ((119/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((119/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(56158936058697/6250000000000),(181963068433/12500000000000),(165850713/12500000000000),(-1043097/12500000000000)⟩
def e191 : ℝ := (47587/3125000000000)
theorem h191 : Model (fun x => f191 ((119/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(64043501306809/6250000000000),(186445864047/10000000000000),(203047127/10000000000000),(-10084371/100000000000000)⟩
def e192 : ℝ := (977297/50000000000000)
theorem h192 : Model (fun x => f192 ((119/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(70293501306809/6250000000000),(186445864047/10000000000000),(203047127/10000000000000),(-10084371/100000000000000)⟩
def e193 : ℝ := (977297/50000000000000)
theorem h193 : Model (fun x => f193 ((119/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(7208071955078211/25000000000000),(240058041595677/100000000000000),(213801346771/20000000000000),(920520543/50000000000000)⟩
def e194 : ℝ := (64122113/25000000000000)
theorem h194 : Model (fun x => f194 ((119/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(346833385623/100000000000000),(-144386987/5000000000000),(11183917/100000000000000),(-8197/100000000000000)⟩
def e195 : ℝ := (661/20000000000000)
theorem h195 : Model (fun x => f195 ((119/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (14295579337226887/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(11616280927383/100000000000000),(2531362897/1562500000000),(8215093/50000000000000),(-51311/5000000000000)⟩
def e196 : ℝ := (398021/100000000000000)
theorem h196 : Model (fun x => f196 ((119/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(31158936058697/12500000000000),(363926136867/50000000000000),(331701427/50000000000000),(-1043097/25000000000000)⟩
def e197 : ℝ := (380693/50000000000000)
theorem h197 : Model (fun x => f197 ((119/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(1112912821829/2500000000000),(-36059983713/50000000000000),(81769/160000000000),(109281/25000000000000)⟩
def e198 : ℝ := (77147/100000000000000)
theorem h198 : Model (fun x => f198 ((119/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (224271483929607/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(27741743563419/25000000000000),(144239934847/100000000000000),(-51105627/50000000000000),(-874249/100000000000000)⟩
def e199 : ℝ := (134723/25000000000000)
theorem h199 : Model (fun x => f199 ((119/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(2741743563419/25000000000000),(144239934847/100000000000000),(-51105627/50000000000000),(-874249/100000000000000)⟩
def e200 : ℝ := (134723/25000000000000)
theorem h200 : Model (fun x => f200 ((119/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(3276167811299/800000000000),(133078511317/25000000000000),(-1886041/500000000000),(-806599/25000000000000)⟩
def e201 : ℝ := (497193/25000000000000)
theorem h201 : Model (fun x => f201 ((119/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(138261763106333/5000000000000),(133078511317/25000000000000),(-1886041/500000000000),(-806599/25000000000000)⟩
def e202 : ℝ := (1988773/100000000000000)
theorem h202 : Model (fun x => f202 ((119/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(153424895068883/5000000000000),(4579266330019/100000000000000),(-619287183/25000000000000),(-14421723/50000000000000)⟩
def e203 : ℝ := (3424637/20000000000000)
theorem h203 : Model (fun x => f203 ((119/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(2087719713439653/25000000000000),(4579266330019/100000000000000),(-619287183/25000000000000),(-14421723/50000000000000)⟩
def e204 : ℝ := (8561593/50000000000000)
theorem h204 : Model (fun x => f204 ((119/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(1158339698450749/12500000000000),(4281693876813/25000000000000),(-2339612111/50000000000000),(-56633869/50000000000000)⟩
def e205 : ℝ := (64131867/100000000000000)
theorem h205 : Model (fun x => f205 ((119/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14535765206653611/100000000000000),(4281693876813/25000000000000),(-2339612111/50000000000000),(-56633869/50000000000000)⟩
def e206 : ℝ := (16032967/25000000000000)
theorem h206 : Model (fun x => f206 ((119/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(8064949417221053/50000000000000),(39971442831207/100000000000000),(4654068399/100000000000000),(-138511683/50000000000000)⟩
def e207 : ℝ := (29998129/20000000000000)
theorem h207 : Model (fun x => f207 ((119/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(18465613120156391/100000000000000),(39971442831207/100000000000000),(4654068399/100000000000000),(-138511683/50000000000000)⟩
def e208 : ℝ := (74995323/50000000000000)
theorem h208 : Model (fun x => f208 ((119/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(20490732156827359/100000000000000),(3549494450447/5000000000000),(175781309/400000000000),(-251491087/50000000000000)⟩
def e209 : ℝ := (133567879/50000000000000)
theorem h209 : Model (fun x => f209 ((119/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(20893113109208311/100000000000000),(3549494450447/5000000000000),(175781309/400000000000),(-251491087/50000000000000)⟩
def e210 : ℝ := (267135759/100000000000000)
theorem h210 : Model (fun x => f210 ((119/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(23184455444686591/100000000000000),(21782308919099/20000000000000),(129805456721/100000000000000),(-749974877/100000000000000)⟩
def e211 : ℝ := (411183359/100000000000000)
theorem h211 : Model (fun x => f211 ((119/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(23166836397067543/100000000000000),(21782308919099/20000000000000),(129805456721/100000000000000),(-749974877/100000000000000)⟩
def e212 : ℝ := (321237/78125000000)
theorem h212 : Model (fun x => f212 ((119/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(25707537380125181/100000000000000),(30854335075161/20000000000000),(277456014711/100000000000000),(-479424407/50000000000000)⟩
def e213 : ℝ := (584470071/100000000000000)
theorem h213 : Model (fun x => f213 ((119/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(12855435356729257/50000000000000),(30854335075161/20000000000000),(277456014711/100000000000000),(-479424407/50000000000000)⟩
def e214 : ℝ := (73058759/12500000000000)
theorem h214 : Model (fun x => f214 ((119/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(1409852285770459/50000000000000),(13501069521217/25000000000000),(226670490377/100000000000000),(-21853593/25000000000000)⟩
def e215 : ℝ := (207345819/100000000000000)
theorem h215 : Model (fun x => f215 ((119/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(123136693750159/100000000000000),(32011738273/10000000000000),(-4697471/25000000000000),(-447023/20000000000000)⟩
def e216 : ℝ := (599981/50000000000000)
theorem h216 : Model (fun x => f216 ((119/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(52741743563419/25000000000000),(144239934847/100000000000000),(-51105627/50000000000000),(-874249/100000000000000)⟩
def e217 : ℝ := (134723/25000000000000)
theorem h217 : Model (fun x => f217 ((119/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(445070642257511/100000000000000),(76074656553/12500000000000),(-27901549/12500000000000),(-3983613/100000000000000)⟩
def e218 : ℝ := (1138873/50000000000000)
theorem h218 : Model (fun x => f218 ((119/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(938952067262073/100000000000000),(385181762649/20000000000000),(-23988217/50000000000000),(-264783/2000000000000)⟩
def e219 : ℝ := (7221157/100000000000000)
theorem h219 : Model (fun x => f219 ((119/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(15475615359337/781250000000),(5417375400251/100000000000000),(1717000503/100000000000000),(-3817671/10000000000000)⟩
def e220 : ℝ := (1271931/6250000000000)
theorem h220 : Model (fun x => f220 ((119/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2439188619645359/100000000000000),(13011914216661/100000000000000),(4771003293/25000000000000),(-86805959/100000000000000)⟩
def e221 : ℝ := (12300761/25000000000000)
theorem h221 : Model (fun x => f221 ((119/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(27741743563419/3125000000000),(144239934847/12500000000000),(-51105627/6250000000000),(-874249/12500000000000)⟩
def e222 : ℝ := (134723/3125000000000)
theorem h222 : Model (fun x => f222 ((119/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(1010872487779567/100000000000000),(737018430753/50000000000000),(-209119979/25000000000000),(-9229107/100000000000000)⟩
def e223 : ℝ := (2755549/50000000000000)
theorem h223 : Model (fun x => f223 ((119/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1110872487779567/100000000000000),(737018430753/50000000000000),(-209119979/25000000000000),(-9229107/100000000000000)⟩
def e224 : ℝ := (2755549/50000000000000)
theorem h224 : Model (fun x => f224 ((119/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(27096275300690479/100000000000000),(180500314541597/100000000000000),(95849035229/25000000000000),(-203391101/20000000000000)⟩
def e225 : ℝ := (137018823/20000000000000)
theorem h225 : Model (fun x => f225 ((119/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(369054413901/100000000000000),(-245843523/10000000000000),(2788707/25000000000000),(-25671/100000000000000)⟩
def e226 : ℝ := (4769/50000000000000)
theorem h226 : Model (fun x => f226 ((119/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (13457694943979173/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(130078052253/1250000000000),(64992280699/50000000000000),(-88294777/50000000000000),(-148729/25000000000000)⟩
def e227 : ℝ := (66131/6250000000000)
theorem h227 : Model (fun x => f227 ((119/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(22022525107623/100000000000000),(145995893403/50000000000000),(-20019921/12500000000000),(-101321/6250000000000)⟩
def e228 : ℝ := (1456117/100000000000000)
theorem h228 : Model (fun x => f228 ((119/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(2935937690337/12500000000000),(122531772743/50000000000000),(-138172877/25000000000000),(1734759/100000000000000)⟩
def e229 : ℝ := (5384891/50000000000000)
theorem h229 : Model (fun x => f229 ((119/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7894958495023/100000000000000),(16030111969/100000000000000),(-160242741/50000000000000),(3276267/100000000000000)⟩
def e230 : ℝ := (3757949/100000000000000)
theorem h230 : Model (fun x => f230 ((119/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-168412525716309/100000000000000),(-237117390321/100000000000000),(6267724233/100000000000000),(-67624559/100000000000000)⟩
def e231 : ℝ := (1391863/12500000000000)
theorem h231 : Model (fun x => f231 ((119/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((119/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-14161/320),(-119/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((119/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2499/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((119/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5831/320),(-7/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((119/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((119/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14151/320),(-7/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((119/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((119/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(353775/32),(-875/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((119/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14399/1600),(1/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((119/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23999/1600),(1/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((119/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((119/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4535811/1600),(189/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((119/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(35274838391/100000000000000),(-2939693/100000000000000),(1470091/100000000000000),(-123/50000000000000)⟩
def e244 : ℝ := (1/1562500000000)
theorem h244 : Model (fun x => f244 ((119/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1133811/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(389979873493/100000000000),(-490398102151/25000000000000),(-5572578961/50000000000000),(-20204653/25000000000000)⟩
def e245 : ℝ := (1846349/100000000000000)
theorem h245 : Model (fun x => f245 ((119/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(1071/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((119/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(99841/1600),(479/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((119/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(133441/1600),(479/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((119/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(39601/1600),(199/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((119/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(5284397041/2560000),(22761819/640000),(277163/1280000),(339/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((119/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((119/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(227529/160),(1431/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((119/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(70320706371/100000000000000),(-221134297/25000000000000),(834469/10000000000000),(-69977/100000000000000)⟩
def e253 : ℝ := (563/100000000000000)
theorem h253 : Model (fun x => f253 ((119/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (112329/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(72578619661707/50000000000000),(67510275881/10000000000000),(248295853/25000000000000),(-1950017/100000000000000)⟩
def e254 : ℝ := (592817/25000000000000)
theorem h254 : Model (fun x => f254 ((119/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(122578619661707/50000000000000),(67510275881/10000000000000),(248295853/25000000000000),(-1950017/100000000000000)⟩
def e255 : ℝ := (592817/25000000000000)
theorem h255 : Model (fun x => f255 ((119/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(122578619661707/100000000000000),(67510275881/20000000000000),(248295853/50000000000000),(-975009/100000000000000)⟩
def e256 : ℝ := (237127/20000000000000)
theorem h256 : Model (fun x => f256 ((119/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(22578619661707/100000000000000),(67510275881/20000000000000),(248295853/50000000000000),(-975009/100000000000000)⟩
def e257 : ℝ := (237127/20000000000000)
theorem h257 : Model (fun x => f257 ((119/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(226186738661483/50000000000000),(311431332189/25000000000000),(1832659867/100000000000000),(-449781/12500000000000)⟩
def e258 : ℝ := (109389/2500000000000)
theorem h258 : Model (fun x => f258 ((119/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2808087763037251/100000000000000),(311431332189/25000000000000),(1832659867/100000000000000),(-449781/12500000000000)⟩
def e259 : ℝ := (4375561/100000000000000)
theorem h259 : Model (fun x => f259 ((119/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(215132201176273/6250000000000),(55028659459/500000000000),(20396143127/100000000000000),(-9708727/50000000000000)⟩
def e260 : ℝ := (7740397/20000000000000)
theorem h260 : Model (fun x => f260 ((119/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(218112404280033/2500000000000),(55028659459/500000000000),(20396143127/100000000000000),(-9708727/50000000000000)⟩
def e261 : ℝ := (19350993/50000000000000)
theorem h261 : Model (fun x => f261 ((119/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2138873395819411/20000000000000),(42940331408663/100000000000000),(1054764349/1000000000000),(1829343/12500000000000)⟩
def e262 : ℝ := (30242893/20000000000000)
theorem h262 : Model (fun x => f262 ((119/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7981707299072337/50000000000000),(42940331408663/100000000000000),(1054764349/1000000000000),(1829343/12500000000000)⟩
def e263 : ℝ := (75607233/50000000000000)
theorem h263 : Model (fun x => f263 ((119/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(4891933316320293/25000000000000),(53260195847539/50000000000000),(44188778981/12500000000000),(431569623/100000000000000)⟩
def e264 : ℝ := (23487591/6250000000000)
theorem h264 : Model (fun x => f264 ((119/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(21903447550995457/100000000000000),(53260195847539/50000000000000),(44188778981/12500000000000),(431569623/100000000000000)⟩
def e265 : ℝ := (375801457/100000000000000)
theorem h265 : Model (fun x => f265 ((119/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(26848943666336197/100000000000000),(102253307571853/50000000000000),(450829858971/50000000000000),(509425399/25000000000000)⟩
def e266 : ℝ := (362529857/50000000000000)
theorem h266 : Model (fun x => f266 ((119/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(27251324618717149/100000000000000),(102253307571853/50000000000000),(450829858971/50000000000000),(509425399/25000000000000)⟩
def e267 : ℝ := (145011943/20000000000000)
theorem h267 : Model (fun x => f267 ((119/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(33404297557154419/100000000000000),(42833576014581/12500000000000),(965442377261/50000000000000),(3145605663/50000000000000)⟩
def e268 : ℝ := (306529791/25000000000000)
theorem h268 : Model (fun x => f268 ((119/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(33386678509535371/100000000000000),(42833576014581/12500000000000),(965442377261/50000000000000),(3145605663/50000000000000)⟩
def e269 : ℝ := (245223833/20000000000000)
theorem h269 : Model (fun x => f269 ((119/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(40924929667880229/100000000000000),(26636782184491/5000000000000),(461166246153/12500000000000),(15605548893/100000000000000)⟩
def e270 : ℝ := (241816359/12500000000000)
theorem h270 : Model (fun x => f270 ((119/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(20464131500606781/50000000000000),(26636782184491/5000000000000),(461166246153/12500000000000),(15605548893/100000000000000)⟩
def e271 : ℝ := (1934530873/100000000000000)
theorem h271 : Model (fun x => f271 ((119/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(2310259209296789/25000000000000),(258438271118173/100000000000000),(2834502655147/100000000000000),(9111684253/50000000000000)⟩
def e272 : ℝ := (500397601/50000000000000)
theorem h272 : Model (fun x => f272 ((119/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(75127589990847/50000000000000),(827531643047/100000000000000),(1178419927/50000000000000),(962199/100000000000000)⟩
def e273 : ℝ := (1459407/50000000000000)
theorem h273 : Model (fun x => f273 ((119/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(222578619661707/100000000000000),(67510275881/20000000000000),(248295853/50000000000000),(-975009/100000000000000)⟩
def e274 : ℝ := (237127/20000000000000)
theorem h274 : Model (fun x => f274 ((119/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(123853104826277/25000000000000),(1502634401857/100000000000000),(1675011633/50000000000000),(-987819/100000000000000)⟩
def e275 : ℝ := (1322521/25000000000000)
theorem h275 : Model (fun x => f275 ((119/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(1102682124521977/100000000000000),(5016814365323/100000000000000),(14988775679/100000000000000),(11741017/100000000000000)⟩
def e276 : ℝ := (17685507/100000000000000)
theorem h276 : Model (fun x => f276 ((119/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(2454334652017401/100000000000000),(7444237443551/50000000000000),(13942991019/25000000000000),(45444823/50000000000000)⟩
def e277 : ℝ := (52622629/100000000000000)
theorem h277 : Model (fun x => f277 ((119/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(3687764948741829/100000000000000),(8536220121971/20000000000000),(16553240193/6250000000000),(194522029/20000000000000)⟩
def e278 : ℝ := (153791133/100000000000000)
theorem h278 : Model (fun x => f278 ((119/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(122578619661707/12500000000000),(67510275881/2500000000000),(248295853/6250000000000),(-975009/12500000000000)⟩
def e279 : ℝ := (237127/2500000000000)
theorem h279 : Model (fun x => f279 ((119/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(22617682745507/2000000000000),(3527942678287/100000000000000),(3164786751/50000000000000),(-6837873/100000000000000)⟩
def e280 : ℝ := (6201947/50000000000000)
theorem h280 : Model (fun x => f280 ((119/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(24617682745507/2000000000000),(3527942678287/100000000000000),(3164786751/50000000000000),(-6837873/100000000000000)⟩
def e281 : ℝ := (6201947/50000000000000)
theorem h281 : Model (fun x => f281 ((119/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(9078422754812723/20000000000000),(655457130522809/100000000000000),(124980097021/2500000000000),(23764892149/100000000000000)⟩
def e282 : ℝ := (602345449/25000000000000)
theorem h282 : Model (fun x => f282 ((119/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(220302584933/100000000000000),(-3181145097/100000000000000),(10836317/50000000000000),(-38969/50000000000000)⟩
def e283 : ℝ := (12453/100000000000000)
theorem h283 : Model (fun x => f283 ((119/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (44731631265386021/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(10179121513467/50000000000000),(275375401471/100000000000000),(324529/1250000000000),(-121499/10000000000000)⟩
def e284 : ℝ := (28037/781250000000)
theorem h284 : Model (fun x => f284 ((119/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(72578619661707/25000000000000),(67510275881/5000000000000),(248295853/12500000000000),(-1950017/50000000000000)⟩
def e285 : ℝ := (592817/12500000000000)
theorem h285 : Model (fun x => f285 ((119/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(20395073846479/50000000000000),(-28081509357/25000000000000),(72034421/50000000000000),(382777/100000000000000)⟩
def e286 : ℝ := (399263/100000000000000)
theorem h286 : Model (fun x => f286 ((119/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (244481139059907/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(59209852307041/50000000000000),(224652074851/100000000000000),(-288137687/100000000000000),(-153111/20000000000000)⟩
def e287 : ℝ := (1558377/50000000000000)
theorem h287 : Model (fun x => f287 ((119/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(9209852307041/50000000000000),(224652074851/100000000000000),(-288137687/100000000000000),(-153111/20000000000000)⟩
def e288 : ℝ := (1558377/50000000000000)
theorem h288 : Model (fun x => f288 ((119/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(437025100361493/100000000000000),(414536566689/50000000000000),(-531682637/50000000000000),(-2825263/100000000000000)⟩
def e289 : ℝ := (11502309/100000000000000)
theorem h289 : Model (fun x => f289 ((119/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1396369693037889/50000000000000),(414536566689/50000000000000),(-531682637/50000000000000),(-2825263/100000000000000)⟩
def e290 : ℝ := (1150231/10000000000000)
theorem h290 : Model (fun x => f290 ((119/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3307153731632063/100000000000000),(7255732931581/100000000000000),(-1860909673/25000000000000),(-29503369/100000000000000)⟩
def e291 : ℝ := (50362607/50000000000000)
theorem h291 : Model (fun x => f291 ((119/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1717906936802603/20000000000000),(7255732931581/100000000000000),(-1860909673/25000000000000),(-29503369/100000000000000)⟩
def e292 : ℝ := (20145043/20000000000000)
theorem h292 : Model (fun x => f292 ((119/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(5085850800266167/50000000000000),(13944392696423/50000000000000),(-8632133469/50000000000000),(-27664841/20000000000000)⟩
def e293 : ℝ := (193773321/50000000000000)
theorem h293 : Model (fun x => f293 ((119/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(15440749219579953/100000000000000),(13944392696423/50000000000000),(-8632133469/50000000000000),(-27664841/20000000000000)⟩
def e294 : ℝ := (387546643/100000000000000)
theorem h294 : Model (fun x => f294 ((119/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(2285611202003469/12500000000000),(67713780776989/100000000000000),(-2282176533/100000000000000),(-200576589/50000000000000)⟩
def e295 : ℝ := (94239833/10000000000000)
theorem h295 : Model (fun x => f295 ((119/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(20620603901742037/100000000000000),(67713780776989/100000000000000),(-2282176533/100000000000000),(-200576589/50000000000000)⟩
def e296 : ℝ := (942398331/100000000000000)
theorem h296 : Model (fun x => f296 ((119/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(24418858230082787/100000000000000),(126511073691207/100000000000000),(45001067819/50000000000000),(-52071397/6250000000000)⟩
def e297 : ℝ := (176432343/10000000000000)
theorem h297 : Model (fun x => f297 ((119/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(24821239182463739/100000000000000),(126511073691207/100000000000000),(45001067819/50000000000000),(-52071397/6250000000000)⟩
def e298 : ℝ := (1764323431/100000000000000)
theorem h298 : Model (fun x => f298 ((119/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(29393238121428341/100000000000000),(41115093719273/20000000000000),(319270670667/100000000000000),(-1338959367/100000000000000)⟩
def e299 : ℝ := (1436969703/50000000000000)
theorem h299 : Model (fun x => f299 ((119/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(29375619073809293/100000000000000),(41115093719273/20000000000000),(319270670667/100000000000000),(-1338959367/100000000000000)⟩
def e300 : ℝ := (2873939407/100000000000000)
theorem h300 : Model (fun x => f300 ((119/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(6957304267152579/20000000000000),(309434800420469/100000000000000),(94408338921/12500000000000),(-1685570463/100000000000000)⟩
def e301 : ℝ := (4337261529/100000000000000)
theorem h301 : Model (fun x => f301 ((119/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(8697463667274057/25000000000000),(309434800420469/100000000000000),(94408338921/12500000000000),(-1685570463/100000000000000)⟩
def e302 : ℝ := (433726153/10000000000000)
theorem h302 : Model (fun x => f302 ((119/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(320409423285797/5000000000000),(33788276640599/25000000000000),(734026914183/100000000000000),(3567367/1562500000000)⟩
def e303 : ℝ := (477745497/25000000000000)
theorem h303 : Model (fun x => f303 ((119/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(4382258262777/3125000000000),(106412929379/20000000000000),(-177738049/100000000000000),(-3107751/100000000000000)⟩
def e304 : ℝ := (369917/5000000000000)
theorem h304 : Model (fun x => f304 ((119/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(109209852307041/50000000000000),(224652074851/100000000000000),(-288137687/100000000000000),(-153111/20000000000000)⟩
def e305 : ℝ := (1558377/50000000000000)
theorem h305 : Model (fun x => f305 ((119/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(119267918409257/25000000000000),(981368796597/100000000000000),(-754013423/100000000000000),(-4638861/100000000000000)⟩
def e306 : ℝ := (1703981/12500000000000)
theorem h306 : Model (fun x => f306 ((119/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(1042018540355453/100000000000000),(3215254240053/100000000000000),(-408435907/50000000000000),(-18306033/100000000000000)⟩
def e307 : ℝ := (44720851/100000000000000)
theorem h307 : Model (fun x => f307 ((119/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(2275973817868349/100000000000000),(2340916271239/25000000000000),(1218239119/50000000000000),(-59060687/100000000000000)⟩
def e308 : ℝ := (65210293/50000000000000)
theorem h308 : Model (fun x => f308 ((119/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(3191649622149659/100000000000000),(25240531637759/100000000000000),(12298052179/25000000000000),(-31446579/20000000000000)⟩
def e309 : ℝ := (70654547/20000000000000)
theorem h309 : Model (fun x => f309 ((119/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(59209852307041/6250000000000),(224652074851/12500000000000),(-288137687/12500000000000),(-153111/2500000000000)⟩
def e310 : ℝ := (1558377/6250000000000)
theorem h310 : Model (fun x => f310 ((119/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(13594873766519/1250000000000),(2329281245703/100000000000000),(-496567909/20000000000000),(-9232191/100000000000000)⟩
def e311 : ℝ := (8083093/25000000000000)
theorem h311 : Model (fun x => f311 ((119/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(14844873766519/1250000000000),(2329281245703/100000000000000),(-496567909/20000000000000),(-9232191/100000000000000)⟩
def e312 : ℝ := (8083093/25000000000000)
theorem h312 : Model (fun x => f312 ((119/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(37903708598215801/100000000000000),(374096500847171/100000000000000),(218576226749/20000000000000),(-1642798181/100000000000000)⟩
def e313 : ℝ := (210039859/4000000000000)
theorem h313 : Model (fun x => f313 ((119/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(65956606687/25000000000000),(-260387563/10000000000000),(904621/5000000000000),(-46027/50000000000000)⟩
def e314 : ℝ := (7513/20000000000000)
theorem h314 : Model (fun x => f314 ((119/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (37528512322440229/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(135251957187/800000000000),(189708353899/100000000000000),(-84653091/20000000000000),(42671/100000000000000)⟩
def e315 : ℝ := (1888287/25000000000000)
theorem h315 : Model (fun x => f315 ((119/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(37264737675309/100000000000000),(46508375537/10000000000000),(-79460627/20000000000000),(-1172319/100000000000000)⟩
def e316 : ℝ := (2785471/25000000000000)
theorem h316 : Model (fun x => f316 ((119/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(36331244210917/25000000000000),(1082750775503/100000000000000),(-7412831883/50000000000000),(-78729503/100000000000000)⟩
def e317 : ℝ := (44676599/100000000000000)
theorem h317 : Model (fun x => f317 ((119/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(12212182928039/25000000000000),(-181811341/390625000000),(-1148073209/25000000000000),(3031749/25000000000000)⟩
def e318 : ℝ := (3147747/20000000000000)
theorem h318 : Model (fun x => f318 ((119/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-119563794004153/100000000000000),(-283661093617/100000000000000),(1675431397/100000000000000),(-55497563/100000000000000)⟩
def e319 : ℝ := (26873639/100000000000000)
theorem h319 : Model (fun x => f319 ((119/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((119/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-155771/1600),(-1309/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((119/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((119/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(11543/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((119/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(305949/1600),(631/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((119/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((119/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(478749/1600),(631/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((119/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2393745/32),(3155/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((119/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((119/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(1097945029034049173/100000000000000),(11437403944269/12500000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (35441/25000000000000)
theorem h329 : Model (fun x => f329 ((119/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(2276981027/25000000000000),(-379513/50000000000000),(15183/4000000000000),(-1/1562500000000)⟩
def e330 : ℝ := (19/100000000000000)
theorem h330 : Model (fun x => f330 ((119/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (54890389009328809/5000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(340656996779757/50000000000000),(1739190200909/100000000000000),(12590014949/100000000000000),(71364531/100000000000000)⟩
def e331 : ℝ := (130637/6250000000000)
theorem h331 : Model (fun x => f331 ((119/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((119/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(479/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((119/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((119/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((119/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(845806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((119/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((119/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((119/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(938103552718963/25000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (551/50000000000000)
theorem h339 : Model (fun x => f339 ((119/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3944193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((119/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((119/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((119/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2222585789123889/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (551/50000000000000)
theorem h343 : Model (fun x => f343 ((119/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2249631948727/50000000000000),(-5703655363/100000000000000),(1446089/20000000000000),(-4583/50000000000000)⟩
def e344 : ℝ := (1/6250000000000)
theorem h344 : Model (fun x => f344 ((119/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1109884123744153/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(16883101787287/10000000000000),(392011283213/50000000000000),(-993894731/100000000000000),(157493/12500000000000)⟩
def e345 : ℝ := (269/10000000000000)
theorem h345 : Model (fun x => f345 ((119/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(26883101787287/10000000000000),(392011283213/50000000000000),(-993894731/100000000000000),(157493/12500000000000)⟩
def e346 : ℝ := (269/10000000000000)
theorem h346 : Model (fun x => f346 ((119/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(26883101787287/20000000000000),(392011283213/100000000000000),(-248473683/50000000000000),(157493/25000000000000)⟩
def e347 : ℝ := (673/50000000000000)
theorem h347 : Model (fun x => f347 ((119/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(6883101787287/20000000000000),(392011283213/100000000000000),(-248473683/50000000000000),(157493/25000000000000)⟩
def e348 : ℝ := (673/50000000000000)
theorem h348 : Model (fun x => f348 ((119/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(124014308840163/25000000000000),(289341661419/20000000000000),(-1833972423/100000000000000),(72653/3125000000000)⟩
def e349 : ℝ := (4971/100000000000000)
theorem h349 : Model (fun x => f349 ((119/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2851771521074937/100000000000000),(289341661419/20000000000000),(-1833972423/100000000000000),(72653/3125000000000)⟩
def e350 : ℝ := (1243/25000000000000)
theorem h350 : Model (fun x => f350 ((119/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(383322320375719/10000000000000),(3280966616969/25000000000000),(-5482843513/50000000000000),(53693/800000000000)⟩
def e351 : ℝ := (72473/100000000000000)
theorem h351 : Model (fun x => f351 ((119/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4557802078069071/50000000000000),(3280966616969/25000000000000),(-5482843513/50000000000000),(53693/800000000000)⟩
def e352 : ℝ := (36237/50000000000000)
theorem h352 : Model (fun x => f352 ((119/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(382899553721997/3125000000000),(13343677182507/25000000000000),(-4296150713/50000000000000),(-41758221/100000000000000)⟩
def e353 : ℝ := (384159/100000000000000)
theorem h353 : Model (fun x => f353 ((119/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(17521833338151523/100000000000000),(13343677182507/25000000000000),(-4296150713/50000000000000),(-41758221/100000000000000)⟩
def e354 : ℝ := (2401/625000000000)
theorem h354 : Model (fun x => f354 ((119/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(23552061456470307/100000000000000),(140431450094137/100000000000000),(110611205663/100000000000000),(-122336941/50000000000000)⟩
def e355 : ℝ := (484923/50000000000000)
theorem h355 : Model (fun x => f355 ((119/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(1617985983886537/6250000000000),(140431450094137/100000000000000),(110611205663/100000000000000),(-122336941/50000000000000)⟩
def e356 : ℝ := (969847/100000000000000)
theorem h356 : Model (fun x => f356 ((119/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(17398592758090191/50000000000000),(290244650233091/100000000000000),(285268562457/50000000000000),(-430055891/100000000000000)⟩
def e357 : ℝ := (2283839/100000000000000)
theorem h357 : Model (fun x => f357 ((119/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(17599783234280667/50000000000000),(290244650233091/100000000000000),(285268562457/50000000000000),(-430055891/100000000000000)⟩
def e358 : ℝ := (7137/312500000000)
theorem h358 : Model (fun x => f358 ((119/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(47313676412135437/100000000000000),(105624019194081/20000000000000),(1729758839551/100000000000000),(218946179/50000000000000)⟩
def e359 : ℝ := (6254913/100000000000000)
theorem h359 : Model (fun x => f359 ((119/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(47296057364516389/100000000000000),(105624019194081/20000000000000),(1729758839551/100000000000000),(218946179/50000000000000)⟩
def e360 : ℝ := (3127457/50000000000000)
theorem h360 : Model (fun x => f360 ((119/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(1271464724267659/2000000000000),(447640598089003/50000000000000),(4160318001379/100000000000000),(5042918077/100000000000000)⟩
def e361 : ℝ := (12636983/100000000000000)
theorem h361 : Model (fun x => f361 ((119/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(63576569546716283/100000000000000),(447640598089003/50000000000000),(4160318001379/100000000000000),(5042918077/100000000000000)⟩
def e362 : ℝ := (1579623/12500000000000)
theorem h362 : Model (fun x => f362 ((119/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(4376039994765791/20000000000000),(557342906179751/100000000000000),(925091166259/20000000000000),(1749487521/12500000000000)⟩
def e363 : ℝ := (10001951/100000000000000)
theorem h363 : Model (fun x => f363 ((119/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(22584411303301/12500000000000),(526923961419/50000000000000),(200779799/100000000000000),(-110131/5000000000000)⟩
def e364 : ℝ := (5523/50000000000000)
theorem h364 : Model (fun x => f364 ((119/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(46883101787287/20000000000000),(392011283213/100000000000000),(-248473683/50000000000000),(157493/25000000000000)⟩
def e365 : ℝ := (673/50000000000000)
theorem h365 : Model (fun x => f365 ((119/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(274753154149639/50000000000000),(114866905579/6250000000000),(-793114933/100000000000000),(-235669/25000000000000)⟩
def e366 : ℝ := (6869/50000000000000)
theorem h366 : Model (fun x => f366 ((119/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(20127000144337/1562500000000),(6462380191501/100000000000000),(2614718157/100000000000000),(-1373799/12500000000000)⟩
def e367 : ℝ := (3219/6250000000000)
theorem h367 : Model (fun x => f367 ((119/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(3019571828607013/100000000000000),(2524803569219/12500000000000),(25061246177/100000000000000),(-2469561/6250000000000)⟩
def e368 : ℝ := (769/500000000000)
theorem h368 : Model (fun x => f368 ((119/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(5455620170969719/100000000000000),(34157632222719/50000000000000),(132101444661/50000000000000),(166761909/100000000000000)⟩
def e369 : ℝ := (1426893/100000000000000)
theorem h369 : Model (fun x => f369 ((119/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(26883101787287/2500000000000),(392011283213/12500000000000),(-248473683/6250000000000),(157493/3125000000000)⟩
def e370 : ℝ := (673/6250000000000)
theorem h370 : Model (fun x => f370 ((119/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(19624990029967/1562500000000),(2094969094271/50000000000000),(-3774799129/100000000000000),(709289/25000000000000)⟩
def e371 : ℝ := (10907/50000000000000)
theorem h371 : Model (fun x => f371 ((119/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(21187490029967/1562500000000),(2094969094271/50000000000000),(-3774799129/100000000000000),(709289/25000000000000)⟩
def e372 : ℝ := (10907/50000000000000)
theorem h372 : Model (fun x => f372 ((119/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(3698908735350649/5000000000000),(1154941662937917/100000000000000),(3119509072141/50000000000000),(681703039/6250000000000)⟩
def e373 : ℝ := (10831227/50000000000000)
theorem h373 : Model (fun x => f373 ((119/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(67587501581/50000000000000),(-527585479/25000000000000),(5386597/25000000000000),(-178333/100000000000000)⟩
def e374 : ℝ := (677/50000000000000)
theorem h374 : Model (fun x => f374 ((119/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (72816983097019703/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(1183062440259/4000000000000),(291641259699/100000000000000),(-397494059/50000000000000),(2373673/100000000000000)⟩
def e375 : ℝ := (61553/10000000000000)
theorem h375 : Model (fun x => f375 ((119/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(16883101787287/5000000000000),(392011283213/25000000000000),(-993894731/50000000000000),(157493/6250000000000)⟩
def e376 : ℝ := (269/5000000000000)
theorem h376 : Model (fun x => f376 ((119/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(4649761065113/12500000000000),(-108485029217/100000000000000),(453912261/100000000000000),(-379843/20000000000000)⟩
def e377 : ℝ := (1627/20000000000000)
theorem h377 : Model (fun x => f377 ((119/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (268046000149079/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(62801911479093/50000000000000),(3390157163/1562500000000),(-226956131/25000000000000),(151937/4000000000000)⟩
def e378 : ℝ := (71193/100000000000000)
theorem h378 : Model (fun x => f378 ((119/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(12801911479093/50000000000000),(3390157163/1562500000000),(-226956131/25000000000000),(151937/4000000000000)⟩
def e379 : ℝ := (71193/100000000000000)
theorem h379 : Model (fun x => f379 ((119/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(115884479514993/25000000000000),(800722834689/100000000000000),(-3350304791/100000000000000),(14017997/100000000000000)⟩
def e380 : ℝ := (262737/100000000000000)
theorem h380 : Model (fun x => f380 ((119/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2819252203774257/100000000000000),(800722834689/100000000000000),(-3350304791/100000000000000),(14017997/100000000000000)⟩
def e381 : ℝ := (131369/50000000000000)
theorem h381 : Model (fun x => f381 ((119/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1770544273386687/50000000000000),(3561335822771/50000000000000),(-7016161249/25000000000000),(27539001/25000000000000)⟩
def e382 : ℝ := (2429767/100000000000000)
theorem h382 : Model (fun x => f382 ((119/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4411734749577163/50000000000000),(3561335822771/50000000000000),(-7016161249/25000000000000),(27539001/25000000000000)⟩
def e383 : ℝ := (303721/12500000000000)
theorem h383 : Model (fun x => f383 ((119/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(554130750424367/5000000000000),(7022658702901/25000000000000),(-19979564433/20000000000000),(173979893/50000000000000)⟩
def e384 : ℝ := (2022073/20000000000000)
theorem h384 : Model (fun x => f384 ((119/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(16351662627534959/100000000000000),(7022658702901/25000000000000),(-19979564433/20000000000000),(173979893/50000000000000)⟩
def e385 : ℝ := (5055183/50000000000000)
theorem h385 : Model (fun x => f385 ((119/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(10269156688704437/50000000000000),(70761123174163/100000000000000),(-106485810171/50000000000000),(586394399/100000000000000)⟩
def e386 : ℝ := (13559091/50000000000000)
theorem h386 : Model (fun x => f386 ((119/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(22874027663123159/100000000000000),(70761123174163/100000000000000),(-106485810171/50000000000000),(586394399/100000000000000)⟩
def e387 : ℝ := (27118183/100000000000000)
theorem h387 : Model (fun x => f387 ((119/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(14365326604697851/50000000000000),(138508467061329/100000000000000),(-16081303971/5000000000000),(500915089/100000000000000)⟩
def e388 : ℝ := (56362751/100000000000000)
theorem h388 : Model (fun x => f388 ((119/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(14566517080888327/50000000000000),(138508467061329/100000000000000),(-16081303971/5000000000000),(500915089/100000000000000)⟩
def e389 : ℝ := (220167/390625000000)
theorem h389 : Model (fun x => f389 ((119/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(7318440930181159/20000000000000),(23718189099363/10000000000000),(-91982394543/25000000000000),(-21948117/10000000000000)⟩
def e390 : ℝ := (20208131/20000000000000)
theorem h390 : Model (fun x => f390 ((119/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(36574585603286747/100000000000000),(23718189099363/10000000000000),(-91982394543/25000000000000),(-21948117/10000000000000)⟩
def e391 : ℝ := (6315041/6250000000000)
theorem h391 : Model (fun x => f391 ((119/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(4593907774884247/10000000000000),(377265422207229/100000000000000),(-279552986157/100000000000000),(-1837910931/100000000000000)⟩
def e392 : ℝ := (10326491/6250000000000)
theorem h392 : Model (fun x => f392 ((119/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(45942411082175803/100000000000000),(377265422207229/100000000000000),(-279552986157/100000000000000),(-1837910931/100000000000000)⟩
def e393 : ℝ := (165223857/100000000000000)
theorem h393 : Model (fun x => f393 ((119/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(11763013596202317/100000000000000),(98137823477229/50000000000000),(65980056127/20000000000000),(-1378470867/50000000000000)⟩
def e394 : ℝ := (88526601/100000000000000)
theorem h394 : Model (fun x => f394 ((119/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(157763203417113/100000000000000),(54504537613/10000000000000),(-904882277/50000000000000),(5602519/100000000000000)⟩
def e395 : ℝ := (50987/25000000000000)
theorem h395 : Model (fun x => f395 ((119/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(112801911479093/50000000000000),(3390157163/1562500000000),(-226956131/25000000000000),(151937/4000000000000)⟩
def e396 : ℝ := (71193/100000000000000)
theorem h396 : Model (fun x => f396 ((119/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(101794169866697/20000000000000),(489492746497/50000000000000),(-1812706801/50000000000000),(13199369/100000000000000)⟩
def e397 : ℝ := (173167/50000000000000)
theorem h397 : Model (fun x => f397 ((119/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1148257693839091/100000000000000),(3312943047601/100000000000000),(-10675528479/100000000000000),(4044703/12500000000000)⟩
def e398 : ℝ := (622073/50000000000000)
theorem h398 : Model (fun x => f398 ((119/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(647628313678123/25000000000000),(9965501557087/100000000000000),(-27320470847/100000000000000),(31688667/50000000000000)⟩
def e399 : ℝ := (3923061/100000000000000)
theorem h399 : Model (fun x => f399 ((119/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(4086876695579343/100000000000000),(29841367205887/100000000000000),(-35667335203/100000000000000),(-84140969/100000000000000)⟩
def e400 : ℝ := (3228789/25000000000000)
theorem h400 : Model (fun x => f400 ((119/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(62801911479093/6250000000000),(3390157163/195312500000),(-226956131/3125000000000),(151937/500000000000)⟩
def e401 : ℝ := (71193/12500000000000)
theorem h401 : Model (fun x => f401 ((119/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(1162593787082601/100000000000000),(1140402921793/50000000000000),(-4536180373/50000000000000),(35989919/100000000000000)⟩
def e402 : ℝ := (193373/25000000000000)
theorem h402 : Model (fun x => f402 ((119/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1262593787082601/100000000000000),(1140402921793/50000000000000),(-4536180373/50000000000000),(35989919/100000000000000)⟩
def e403 : ℝ := (193373/25000000000000)
theorem h403 : Model (fun x => f403 ((119/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(51600651244111489/100000000000000),(234994485407481/50000000000000),(-140486108321/100000000000000),(-622462837/20000000000000)⟩
def e404 : ℝ := (207266361/100000000000000)
theorem h404 : Model (fun x => f404 ((119/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(193796003711/100000000000000),(-882566229/50000000000000),(8302399/50000000000000),(-144357/100000000000000)⟩
def e405 : ℝ := (2061/100000000000000)
theorem h405 : Model (fun x => f405 ((119/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (2556525923380383/5000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(22796250265421/100000000000000),(17274158903/10000000000000),(-435983473/50000000000000),(4444421/100000000000000)⟩
def e406 : ℝ := (300231/50000000000000)
theorem h406 : Model (fun x => f406 ((119/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(6546601408987/12500000000000),(464382848729/100000000000000),(-208369383/12500000000000),(3409047/50000000000000)⟩
def e407 : ℝ := (151999/12500000000000)
theorem h407 : Model (fun x => f407 ((119/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(356823292015941/100000000000000),(2037384066831/50000000000000),(66260953/2000000000000),(11330259/10000000000000)⟩
def e408 : ℝ := (9650913/100000000000000)
theorem h408 : Model (fun x => f408 ((119/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(59970301179149/50000000000000),(180882869697/50000000000000),(-1926418771/100000000000000),(54273293/100000000000000)⟩
def e409 : ℝ := (4937813/100000000000000)
theorem h409 : Model (fun x => f409 ((119/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(75361670829/20000000000000),(78104645777/100000000000000),(-125493687/50000000000000),(-122427/10000000000000)⟩
def e410 : ℝ := (7952863/25000000000000)
theorem h410 : Model (fun x => f410 ((119/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(31137591249023437/100000000000000),(310618907470703/25000000000000),(2025023/10240000),(3213/2048000)⟩
def e411 : ℝ := (621093751/100000000000000)
theorem h411 : Model (fun x => f411 ((119/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(57121/1600),(239/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((119/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(13651919/64000),(171363/64000),(717/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((119/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(6641998024793387359/100000000000000),(174203185217504157/50000000000000),(7893985963187681/100000000000000),(100821554436401/100000000000000)⟩
def e414 : ℝ := (159450796049/20000000000000)
theorem h414 : Model (fun x => f414 ((119/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(752785529/50000000000000),(-78974813/100000000000000),(2353263/100000000000000),(-26217/50000000000000)⟩
def e415 : ℝ := (363/25000000000000)
theorem h415 : Model (fun x => f415 ((119/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (3142798024793387359/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5287238793833/100000000000000),(-18772949537/100000000000000),(-52792809/100000000000000),(1030183/50000000000000)⟩
def e416 : ℝ := (1927971/20000000000000)
theorem h416 : Model (fun x => f416 ((119/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2832023573989/50000000000000),(741646203/1250000000000),(-303780183/100000000000000),(1633/195312500000)⟩
def e417 : ℝ := (41451307/100000000000000)
theorem h417 : Model (fun x => f417 ((119/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((119/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((566390443661/200000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (59/20) 3 ∧
    SigmaActualBlockSeparable.endpointCellMass (59/20) 3 ≤ (707998417403/250000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(119/40)-(1/40)) (by norm_num : ((119/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel39

