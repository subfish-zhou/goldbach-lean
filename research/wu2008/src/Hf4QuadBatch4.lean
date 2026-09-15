import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel13
open Hf4Quad.Dag

def p0 : Cubic := ⟨(67/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((67/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((67/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((67/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((67/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(293523809523809/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((67/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-293523809523809/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((67/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-101047619047619/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((67/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((67/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(4489/1600),(67/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((67/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(67928783068783/20000000000000),(158416005291/1562500000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((67/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-67928783068783/20000000000000),(-158416005291/1562500000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((67/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-541739153439153/100000000000000),(-1814947089947/12500000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((67/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((67/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(300763/64000),(13467/64000),(201/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((67/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(4578455274884259/100000000000000),(51251365017361/25000000000000),(3059782986111/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((67/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-4578455274884259/100000000000000),(-51251365017361/25000000000000),(-3059782986111/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((67/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1280048607080853/25000000000000),(-10976251839451/5000000000000),(-783861090443/25000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((67/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((67/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(20151121/2560000),(300763/640000),(13467/1280000),(67/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((67/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(68719720672123/3125000000000),(4102669890873/3125000000000),(734806547619/25000000000000),(14623015873/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((67/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-730290841703869/25000000000000),(-22059900070271/25000000000000),(-6131817853/3125000000000),(14023230821/100000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((67/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((67/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1318481549804687/100000000000000),(24598536376953/25000000000000),(300763/10240000),(4489/10240000)⟩
def e22 : ℝ := (328125001/100000000000000)
theorem h22 : Model (fun x => f22 ((67/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(8589663133727571/100000000000000),(320509818422669/50000000000000),(2391864316587/12500000000000),(285595739293/100000000000000)⟩
def e23 : ℝ := (2137673621/100000000000000)
theorem h23 : Model (fun x => f23 ((67/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(1133699953382419/20000000000000),(276390018282127/50000000000000),(94693481807/500000000000),(149809485057/50000000000000)⟩
def e24 : ℝ := (2246800613/100000000000000)
theorem h24 : Model (fun x => f24 ((67/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((67/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(44169131918457/2000000000000),(98886116235351/50000000000000),(1475912182617/20000000000000),(146856933593/100000000000000)⟩
def e26 : ℝ := (165375977/10000000000000)
theorem h26 : Model (fun x => f26 ((67/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(2479547564311263/50000000000000),(17763922848797/4000000000000),(828541177649/5000000000000),(329767632893/100000000000000)⟩
def e27 : ℝ := (3713521941/100000000000000)
theorem h27 : Model (fun x => f27 ((67/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(10627594895534621/100000000000000),(996878107784179/100000000000000),(1775475995719/5000000000000),(629386603007/100000000000000)⟩
def e28 : ℝ := (2980161277/50000000000000)
theorem h28 : Model (fun x => f28 ((67/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((67/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(3699164798170773/100000000000000),(386479904286497/100000000000000),(270391724081/1562500000000),(86094877319/20000000000000)⟩
def e30 : ℝ := (6482814951/100000000000000)
theorem h30 : Model (fun x => f30 ((67/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(10972720978701/1250000000000),(91712294747351/100000000000000),(513315082541/12500000000000),(102152255231/100000000000000)⟩
def e31 : ℝ := (38459557/2500000000000)
theorem h31 : Model (fun x => f31 ((67/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(11505412573830701/100000000000000),(108859040253153/10000000000000),(9904010143677/25000000000000),(365769429119/50000000000000)⟩
def e32 : ℝ := (3749352417/50000000000000)
theorem h32 : Model (fun x => f32 ((67/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((67/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1925781/320),(28743/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((67/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((67/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(148003/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((67/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(4293829/320),(9283/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((67/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((67/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(5023429/320),(9283/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((67/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-5023429/320),(-9283/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((67/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((67/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(107/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((67/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(11449/1600),(107/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((67/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((67/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(240429/160),(2247/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((67/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(6654771263/10000000000000),(-15548531/1250000000000),(4359401/25000000000000),(-54323/25000000000000)⟩
def e46 : ℝ := (261/10000000000000)
theorem h46 : Model (fun x => f46 ((67/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (117957/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-261170085554069/25000000000000),(5541496811/2500000000000),(-1056130819/50000000000000),(20136683/100000000000000)⟩
def e47 : ℝ := (4084103/5000000000000)
theorem h47 : Model (fun x => f47 ((67/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((67/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(147/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((67/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((67/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((67/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(61249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((67/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(111249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((67/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((67/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(111249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((67/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((67/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2336249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((67/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((67/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(11249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((67/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(131414062499987/50000000000000),(5359374999991/50000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (79/100000000000000)
theorem h60 : Model (fun x => f60 ((67/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(123765624999997/100000000000000),(927083333331/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (9/100000000000000)
theorem h61 : Model (fun x => f61 ((67/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((67/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(111249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((67/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1236265624999987/100000000000000),(5093749999991/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (39/100000000000000)
theorem h64 : Model (fun x => f64 ((67/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1336265624999987/100000000000000),(5093749999991/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (39/100000000000000)
theorem h65 : Model (fun x => f65 ((67/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(3512081887206649/100000000000000),(4894336853019/3125000000000),(51886474609/5000000000000),(2043185763/100000000000000)⟩
def e66 : ℝ := (634127/100000000000000)
theorem h66 : Model (fun x => f66 ((67/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(211249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((67/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(89253124999999/20000000000000),(1760416666663/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (3/20000000000000)
theorem h68 : Model (fun x => f68 ((67/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(235684033203121/25000000000000),(5578320312489/100000000000000),(5501302083/50000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (3/6250000000000)
theorem h69 : Model (fun x => f69 ((67/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(33109664964659669/100000000000000),(1672417000504257/100000000000000),(9453084265171/50000000000000),(94635926673/100000000000000)⟩
def e70 : ℝ := (3840587/1562500000000)
theorem h70 : Model (fun x => f70 ((67/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((67/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2599078124999937/12500000000000),(19468749999951/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (189/12500000000000)
theorem h72 : Model (fun x => f72 ((67/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(467834062499947/20000000000000),(104157812499813/100000000000000),(42610677083/6250000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (101/12500000000000)
theorem h73 : Model (fun x => f73 ((67/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(11026101871978849/50000000000000),(11124197462687/1000000000000),(6247463025367/50000000000000),(61117506223/100000000000000)⟩
def e74 : ℝ := (150531153/100000000000000)
theorem h74 : Model (fun x => f74 ((67/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(55161868708617367/100000000000000),(2784836746772957/100000000000000),(7850273645269/25000000000000),(2433647389/1562500000000)⟩
def e75 : ℝ := (396328721/100000000000000)
theorem h75 : Model (fun x => f75 ((67/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((67/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(866359374999979/12500000000000),(6489583333317/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (63/12500000000000)
theorem h77 : Model (fun x => f77 ((67/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(1265624999999/100000000000000),(93749999999/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((67/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(142382812499/100000000000000),(15820312499/100000000000000),(585937499/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((67/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(9868374755789/100000000000000),(117040649407/10000000000000),(48962402273/100000000000000),(205236359/25000000000000)⟩
def e80 : ℝ := (4332523/100000000000000)
theorem h80 : Model (fun x => f80 ((67/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(5211735417901/25000000000000),(2513601946871/100000000000000),(54154884263/50000000000000),(1938257243/100000000000000)⟩
def e81 : ℝ := (3147779/25000000000000)
theorem h81 : Model (fun x => f81 ((67/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(55182715650288971/100000000000000),(696837587179957/25000000000000),(15754702174801/50000000000000),(157691690139/100000000000000)⟩
def e82 : ℝ := (408919837/100000000000000)
theorem h82 : Model (fun x => f82 ((67/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(8009033203/50000000000000),(1186523437/50000000000000),(131835937/100000000000000),(406901/12500000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((67/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(180203247/10000000000000),(83427429/25000000000000),(12359619/50000000000000),(915527/100000000000000)⟩
def e84 : ℝ := (8541/50000000000000)
theorem h84 : Model (fun x => f84 ((67/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(50682163/25000000000000),(45050811/100000000000000),(4171371/100000000000000),(205993/100000000000000)⟩
def e85 : ℝ := (5811/100000000000000)
theorem h85 : Model (fun x => f85 ((67/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(22806973/100000000000000),(2956459/50000000000000),(65699/10000000000000),(20277/50000000000000)⟩
def e86 : ℝ := (77/5000000000000)
theorem h86 : Model (fun x => f86 ((67/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(68420919/100000000000000),(8869377/50000000000000),(197097/10000000000000),(60831/50000000000000)⟩
def e87 : ℝ := (231/5000000000000)
theorem h87 : Model (fun x => f87 ((67/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-68420919/100000000000000),(-8869377/50000000000000),(-197097/10000000000000),(-60831/50000000000000)⟩
def e88 : ℝ := (231/5000000000000)
theorem h88 : Model (fun x => f88 ((67/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(13795678895467013/25000000000000),(1393675165490537/50000000000000),(3938675297329/12500000000000),(157691568477/100000000000000)⟩
def e89 : ℝ := (408924457/100000000000000)
theorem h89 : Model (fun x => f89 ((67/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2599078124999937/10000000000000),(19468749999951/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (189/10000000000000)
theorem h90 : Model (fun x => f90 ((67/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1991530080566363/100000000000000),(7856134440089/50000000000000),(23243001301/50000000000000),(30562789/50000000000000)⟩
def e91 : ℝ := (30273/100000000000000)
theorem h91 : Model (fun x => f91 ((67/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(517614226767939621/100000000000000),(7961001559651669/100000000000000),(24966342737887/50000000000000),(163673765203/100000000000000)⟩
def e92 : ℝ := (74168027/25000000000000)
theorem h92 : Model (fun x => f92 ((67/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(9659703581/50000000000000),(-297136019/100000000000000),(2706321/100000000000000),(-19069/100000000000000)⟩
def e93 : ℝ := (71/50000000000000)
theorem h93 : Model (fun x => f93 ((67/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (509603128552374867/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(10660973506309/100000000000000),(374531835217/100000000000000),(-14027413/2000000000000),(1751147/100000000000000)⟩
def e94 : ℝ := (311697/100000000000000)
theorem h94 : Model (fun x => f94 ((67/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(61249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((67/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(44943820224719/100000000000000),(-1683289147/1000000000000),(630445373/100000000000000),(-2361219/100000000000000)⟩
def e96 : ℝ := (111/1250000000000)
theorem h96 : Model (fun x => f96 ((67/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (11083333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(110112359550559/100000000000000),(84164457349/25000000000000),(-315222687/25000000000000),(1180609/25000000000000)⟩
def e97 : ℝ := (12253/20000000000000)
theorem h97 : Model (fun x => f97 ((67/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2312359550561739/100000000000000),(1767453604329/25000000000000),(-6619676427/25000000000000),(24792789/25000000000000)⟩
def e98 : ℝ := (257313/20000000000000)
theorem h98 : Model (fun x => f98 ((67/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(10112359550559/100000000000000),(84164457349/25000000000000),(-315222687/25000000000000),(1180609/25000000000000)⟩
def e99 : ℝ := (12253/20000000000000)
theorem h99 : Model (fun x => f99 ((67/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(233834111854493/100000000000000),(2124916131047/25000000000000),(-40164329/500000000000),(-59057029/100000000000000)⟩
def e100 : ℝ := (102383/4000000000000)
theorem h100 : Model (fun x => f100 ((67/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(24249463451583/20000000000000),(741403759119/100000000000000),(-205426021/12500000000000),(477549/25000000000000)⟩
def e101 : ℝ := (183153/100000000000000)
theorem h101 : Model (fun x => f101 ((67/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(110112359550559/10000000000000),(84164457349/2500000000000),(-315222687/2500000000000),(1180609/2500000000000)⟩
def e102 : ℝ := (12253/2000000000000)
theorem h102 : Model (fun x => f102 ((67/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(244474182552701/20000000000000),(4107982053079/100000000000000),(-13918277/97656250000),(12283639/25000000000000)⟩
def e103 : ℝ := (795803/100000000000000)
theorem h103 : Model (fun x => f103 ((67/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(264474182552701/20000000000000),(4107982053079/100000000000000),(-13918277/97656250000),(12283639/25000000000000)⟩
def e104 : ℝ := (795803/100000000000000)
theorem h104 : Model (fun x => f104 ((67/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1546077139641347/50000000000000),(122002954699299/100000000000000),(20961363671/10000000000000),(-551861831/25000000000000)⟩
def e105 : ℝ := (4847593/12500000000000)
theorem h105 : Model (fun x => f105 ((67/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(210112359550559/100000000000000),(84164457349/25000000000000),(-315222687/25000000000000),(1180609/25000000000000)⟩
def e106 : ℝ := (12253/20000000000000)
theorem h106 : Model (fun x => f106 ((67/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(441472036359033/100000000000000),(1414719417911/100000000000000),(-130162177/3125000000000),(2838767/25000000000000)⟩
def e107 : ℝ := (305683/100000000000000)
theorem h107 : Model (fun x => f107 ((67/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(185517462469973/20000000000000),(4458750524989/100000000000000),(-477764733/5000000000000),(3211533/25000000000000)⟩
def e108 : ℝ := (536273/50000000000000)
theorem h108 : Model (fun x => f108 ((67/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(28682430772909679/100000000000000),(1269555373643637/100000000000000),(3544346214753/50000000000000),(-22390371773/100000000000000)⟩
def e109 : ℝ := (498952947/100000000000000)
theorem h109 : Model (fun x => f109 ((67/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(509238732483243/2500000000000),(15569478941499/12500000000000),(-4313946441/1562500000000),(10028529/3125000000000)⟩
def e110 : ℝ := (3846213/12500000000000)
theorem h110 : Model (fun x => f110 ((67/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(128740128998537/6250000000000),(3246848642183/4000000000000),(134569722701/100000000000000),(-1505609419/100000000000000)⟩
def e111 : ℝ := (1311609/5000000000000)
theorem h111 : Model (fun x => f111 ((67/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(2388354204986557/12500000000000),(422388560121917/50000000000000),(1167662429317/25000000000000),(-1545725257/10000000000000)⟩
def e112 : ℝ := (84296803/25000000000000)
theorem h112 : Model (fun x => f112 ((67/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(9557852882560427/20000000000000),(2114332493887471/100000000000000),(5879671073387/50000000000000),(-37847624343/100000000000000)⟩
def e113 : ℝ := (836140159/100000000000000)
theorem h113 : Model (fun x => f113 ((67/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(169746244161081/2500000000000),(5189826313833/12500000000000),(-1437982147/1562500000000),(3342843/3125000000000)⟩
def e114 : ℝ := (1282071/12500000000000)
theorem h114 : Model (fun x => f114 ((67/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(1022598156797/100000000000000),(68088100327/100000000000000),(54898333/6250000000000),(-1883669/25000000000000)⟩
def e115 : ℝ := (60623/100000000000000)
theorem h115 : Model (fun x => f115 ((67/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(25852200593/25000000000000),(5163985137/50000000000000),(38144293/12500000000000),(692477/50000000000000)⟩
def e116 : ℝ := (40369/100000000000000)
theorem h116 : Model (fun x => f116 ((67/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(109707848849/1562500000000),(372093781709/50000000000000),(24912383257/100000000000000),(211337837/100000000000000)⟩
def e117 : ℝ := (3075667/100000000000000)
theorem h117 : Model (fun x => f117 ((67/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(7376311994521/50000000000000),(793633906493/50000000000000),(54760831027/100000000000000),(518864589/100000000000000)⟩
def e118 : ℝ := (1382307/20000000000000)
theorem h118 : Model (fun x => f118 ((67/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(47804017036791177/100000000000000),(2115919761700457/100000000000000),(11814102977801/100000000000000),(-18664379877/50000000000000)⟩
def e119 : ℝ := (421525847/50000000000000)
theorem h119 : Model (fun x => f119 ((67/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(5228534951/50000000000000),(1392535317/100000000000000),(251267/390625000000),(260509/25000000000000)⟩
def e120 : ℝ := (2799/50000000000000)
theorem h120 : Model (fun x => f120 ((67/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(528728253/50000000000000),(88011361/50000000000000),(1382617/12500000000000),(152431/50000000000000)⟩
def e121 : ℝ := (3369/100000000000000)
theorem h121 : Model (fun x => f121 ((67/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(106933803/100000000000000),(1068003/5000000000000),(848891/50000000000000),(8237/12500000000000)⟩
def e122 : ℝ := (251/20000000000000)
theorem h122 : Model (fun x => f122 ((67/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(1081353/10000000000000),(2520007/100000000000000),(242247/100000000000000),(2423/20000000000000)⟩
def e123 : ℝ := (21/6250000000000)
theorem h123 : Model (fun x => f123 ((67/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(3244059/10000000000000),(7560021/100000000000000),(726741/100000000000000),(7269/20000000000000)⟩
def e124 : ℝ := (63/6250000000000)
theorem h124 : Model (fun x => f124 ((67/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-3244059/10000000000000),(-7560021/100000000000000),(-726741/100000000000000),(-7269/20000000000000)⟩
def e125 : ℝ := (63/6250000000000)
theorem h125 : Model (fun x => f125 ((67/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(47804017004350587/100000000000000),(528979938535109/25000000000000),(590705112553/5000000000000),(-37328796099/100000000000000)⟩
def e126 : ℝ := (421526351/50000000000000)
theorem h126 : Model (fun x => f126 ((67/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(509238732483243/2000000000000),(15569478941499/10000000000000),(-4313946441/1250000000000),(10028529/2500000000000)⟩
def e127 : ℝ := (3846213/10000000000000)
theorem h127 : Model (fun x => f127 ((67/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(389795117773983/20000000000000),(12491181246037/100000000000000),(-8380992469/50000000000000),(-17592593/100000000000000)⟩
def e128 : ℝ := (3203107/100000000000000)
theorem h128 : Model (fun x => f128 ((67/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(496246929258448819/100000000000000),(194217190353617/3125000000000),(1690794262087/20000000000000),(-65867838251/100000000000000)⟩
def e129 : ℝ := (1655570927/100000000000000)
theorem h129 : Model (fun x => f129 ((67/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(4030251639/20000000000000),(-31546559/12500000000000),(704349/25000000000000),(-28311/100000000000000)⟩
def e130 : ℝ := (87/25000000000000)
theorem h130 : Model (fun x => f130 ((67/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (245011728836206731/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(602069430883/6250000000000),(152870136713/50000000000000),(-1612480279/100000000000000),(8742279/100000000000000)⟩
def e131 : ℝ := (52219/10000000000000)
theorem h131 : Model (fun x => f131 ((67/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(20294084400437/100000000000000),(680272108643/100000000000000),(-2313850929/100000000000000),(5246713/50000000000000)⟩
def e132 : ℝ := (833887/100000000000000)
theorem h132 : Model (fun x => f132 ((67/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-106004155182073/50000000000000),(-7061685150979/100000000000000),(6312892983/25000000000000),(-12503421/10000000000000)⟩
def e133 : ℝ := (6514329/25000000000000)
theorem h133 : Model (fun x => f133 ((67/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(59701492537313/100000000000000),(-222766763199/25000000000000),(53198033/400000000000),(-49625031/25000000000000)⟩
def e134 : ℝ := (150379/5000000000000)
theorem h134 : Model (fun x => f134 ((67/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (33/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-25314425118107/20000000000000),(-145424701911/6250000000000),(49803852357/100000000000000),(-51124273/6250000000000)⟩
def e135 : ℝ := (40938713/100000000000000)
theorem h135 : Model (fun x => f135 ((67/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(20151121/256000),(300763/64000),(13467/128000),(67/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((67/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((67/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(2706867/32000),(121203/32000),(1809/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((67/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(41806057/256000),(543169/64000),(20703/128000),(17/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((67/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-4489/1600),(-67/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((67/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(41087817/256000),(537809/64000),(20623/128000),(17/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((67/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((67/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(201/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((67/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-201/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((67/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(38515017/256000),(528209/64000),(20623/128000),(17/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((67/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(39283017/256000),(528209/64000),(20623/128000),(17/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((67/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((67/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(39283017/4000),(528209/1000),(20623/2000),(17/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((67/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((67/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(3808561869/512000),(56844207/128000),(2545263/256000),(12663/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((67/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(13443394583/100000000000000),(-401295361/50000000000000),(14973707/50000000000000),(-893953/100000000000000)⟩
def e151 : ℝ := (27197/100000000000000)
theorem h151 : Model (fun x => f151 ((67/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (1788021837/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(8251517155339/6250000000000),(-781124234801/100000000000000),(4396056941/50000000000000),(-94024813/100000000000000)⟩
def e152 : ℝ := (523672647/100000000000000)
theorem h152 : Model (fun x => f152 ((67/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(187/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((67/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(27489/1600),(167/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((67/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(321/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((67/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1246105919003/20000000000000),(-7278656069/12500000000000),(68024823/12500000000000),(-5085969/100000000000000)⟩
def e156 : ℝ := (2999/6250000000000)
theorem h156 : Model (fun x => f156 ((67/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (159/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(53522196261677/50000000000000),(60041633911/20000000000000),(544198579/50000000000000),(-10171953/100000000000000)⟩
def e157 : ℝ := (389799/25000000000000)
theorem h157 : Model (fun x => f157 ((67/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(103522196261677/50000000000000),(60041633911/20000000000000),(544198579/50000000000000),(-10171953/100000000000000)⟩
def e158 : ℝ := (389799/25000000000000)
theorem h158 : Model (fun x => f158 ((67/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(103522196261677/100000000000000),(150104084777/100000000000000),(544198579/100000000000000),(-5085977/100000000000000)⟩
def e159 : ℝ := (779599/100000000000000)
theorem h159 : Model (fun x => f159 ((67/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(3522196261677/100000000000000),(150104084777/100000000000000),(544198579/100000000000000),(-5085977/100000000000000)⟩
def e160 : ℝ := (779599/100000000000000)
theorem h160 : Model (fun x => f160 ((67/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((67/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((67/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(191023100244761/50000000000000),(276977775481/50000000000000),(1004175949/50000000000000),(-9384839/50000000000000)⟩
def e163 : ℝ := (575419/20000000000000)
theorem h163 : Model (fun x => f163 ((67/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2737760486203807/100000000000000),(276977775481/50000000000000),(1004175949/50000000000000),(-9384839/50000000000000)⟩
def e164 : ℝ := (359637/12500000000000)
theorem h164 : Model (fun x => f164 ((67/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((67/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2834189783702547/100000000000000),(4682957273871/100000000000000),(3561890713/20000000000000),(-19080427/12500000000000)⟩
def e166 : ℝ := (24376283/100000000000000)
theorem h166 : Model (fun x => f166 ((67/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8116570736083499/100000000000000),(4682957273871/100000000000000),(3561890713/20000000000000),(-19080427/12500000000000)⟩
def e167 : ℝ := (6094071/25000000000000)
theorem h167 : Model (fun x => f167 ((67/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((67/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8402452287126201/100000000000000),(17031204438583/100000000000000),(34818155119/50000000000000),(-259304717/50000000000000)⟩
def e169 : ℝ := (88957067/100000000000000)
theorem h169 : Model (fun x => f169 ((67/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(683574995308691/5000000000000),(17031204438583/100000000000000),(34818155119/50000000000000),(-259304717/50000000000000)⟩
def e170 : ℝ := (22239267/25000000000000)
theorem h170 : Model (fun x => f170 ((67/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((67/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(1769129620598031/12500000000000),(38152556694087/100000000000000),(1075335497/625000000000),(-1034994699/100000000000000)⟩
def e172 : ℝ := (100106309/50000000000000)
theorem h172 : Model (fun x => f172 ((67/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(16488751250498533/100000000000000),(38152556694087/100000000000000),(1075335497/625000000000),(-1034994699/100000000000000)⟩
def e173 : ℝ := (200212619/100000000000000)
theorem h173 : Model (fun x => f173 ((67/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((67/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(17069517430640811/100000000000000),(64246653775417/100000000000000),(40639230479/12500000000000),(-361044517/25000000000000)⟩
def e175 : ℝ := (16949159/5000000000000)
theorem h175 : Model (fun x => f175 ((67/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(17471898383021763/100000000000000),(64246653775417/100000000000000),(40639230479/12500000000000),(-361044517/25000000000000)⟩
def e176 : ℝ := (338983181/100000000000000)
theorem h176 : Model (fun x => f176 ((67/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((67/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(18087292934712559/100000000000000),(92735580173949/100000000000000),(528083665859/100000000000000),(-1546023051/100000000000000)⟩
def e178 : ℝ := (49183823/10000000000000)
theorem h178 : Model (fun x => f178 ((67/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(18069673887093511/100000000000000),(92735580173949/100000000000000),(528083665859/100000000000000),(-1546023051/100000000000000)⟩
def e179 : ℝ := (491838231/100000000000000)
theorem h179 : Model (fun x => f179 ((67/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((67/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(18706123265241943/100000000000000),(12312522792249/10000000000000),(392109305701/50000000000000),(-305538903/25000000000000)⟩
def e181 : ℝ := (20490609/3125000000000)
theorem h181 : Model (fun x => f181 ((67/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(4677364149643819/25000000000000),(12312522792249/10000000000000),(392109305701/50000000000000),(-305538903/25000000000000)⟩
def e182 : ℝ := (655699489/100000000000000)
theorem h182 : Model (fun x => f182 ((67/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(658983780895099/100000000000000),(8105092692277/25000000000000),(2455111813/781250000000),(852584531/100000000000000)⟩
def e183 : ℝ := (279653/160000000000)
theorem h183 : Model (fun x => f183 ((67/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(107168451188411/100000000000000),(310782090479/100000000000000),(338011251/25000000000000),(-4448251/50000000000000)⟩
def e184 : ℝ := (162883/10000000000000)
theorem h184 : Model (fun x => f184 ((67/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(203522196261677/100000000000000),(150104084777/100000000000000),(544198579/100000000000000),(-5085977/100000000000000)⟩
def e185 : ℝ := (779599/100000000000000)
theorem h185 : Model (fun x => f185 ((67/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(82842568742353/20000000000000),(610990260033/100000000000000),(1220221081/50000000000000),(-2383557/12500000000000)⟩
def e186 : ℝ := (797007/25000000000000)
theorem h186 : Model (fun x => f186 ((67/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(843015076720131/100000000000000),(932625597123/50000000000000),(4069051617/50000000000000),(-52887107/100000000000000)⟩
def e187 : ℝ := (610861/6250000000000)
theorem h187 : Model (fun x => f187 ((67/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1715722798957871/100000000000000),(5061600261769/100000000000000),(11975170369/50000000000000),(-128146259/100000000000000)⟩
def e188 : ℝ := (13311971/50000000000000)
theorem h188 : Model (fun x => f188 ((67/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(459678387582401/25000000000000),(672287361707/6250000000000),(32297550357/50000000000000),(-18387899/12500000000000)⟩
def e189 : ℝ := (14293309/25000000000000)
theorem h189 : Model (fun x => f189 ((67/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((67/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(103522196261677/12500000000000),(150104084777/12500000000000),(544198579/12500000000000),(-5085977/12500000000000)⟩
def e191 : ℝ := (779599/12500000000000)
theorem h191 : Model (fun x => f191 ((67/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(935346021281827/100000000000000),(302322953739/20000000000000),(1426408409/25000000000000),(-24792159/50000000000000)⟩
def e192 : ℝ := (3932811/50000000000000)
theorem h192 : Model (fun x => f192 ((67/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1035346021281827/100000000000000),(302322953739/20000000000000),(1426408409/25000000000000),(-24792159/50000000000000)⟩
def e193 : ℝ := (3932811/50000000000000)
theorem h193 : Model (fun x => f193 ((67/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(9518523793053689/50000000000000),(69581136398501/50000000000000),(117036423093/12500000000000),(-211144869/25000000000000)⟩
def e194 : ℝ := (371098969/50000000000000)
theorem h194 : Model (fun x => f194 ((67/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(525291537711/100000000000000),(-479990161/12500000000000),(2234917/100000000000000),(12239/6250000000000)⟩
def e195 : ℝ := (563/2500000000000)
theorem h195 : Model (fun x => f195 ((67/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (9448473717574109/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(3461586035929/100000000000000),(144997005657/100000000000000),(420562329/100000000000000),(-1393387/25000000000000)⟩
def e196 : ℝ := (69939/6250000000000)
theorem h196 : Model (fun x => f196 ((67/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(53522196261677/25000000000000),(60041633911/10000000000000),(544198579/25000000000000),(-10171953/50000000000000)⟩
def e197 : ℝ := (389799/12500000000000)
theorem h197 : Model (fun x => f197 ((67/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(48298820741411/100000000000000),(-70031843847/100000000000000),(-15235461/10000000000000),(2961943/100000000000000)⟩
def e198 : ℝ := (92939/25000000000000)
theorem h198 : Model (fun x => f198 ((67/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (51685771056373/25000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(51701179258587/50000000000000),(140063687691/100000000000000),(152354609/50000000000000),(-5923891/100000000000000)⟩
def e199 : ℝ := (583819/25000000000000)
theorem h199 : Model (fun x => f199 ((67/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1701179258587/50000000000000),(140063687691/100000000000000),(152354609/50000000000000),(-5923891/100000000000000)⟩
def e200 : ℝ := (583819/25000000000000)
theorem h200 : Model (fun x => f200 ((67/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(381603942146713/100000000000000),(516901704573/100000000000000),(562261057/50000000000000),(-21861979/100000000000000)⟩
def e201 : ℝ := (8618283/100000000000000)
theorem h201 : Model (fun x => f201 ((67/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1368659113930499/50000000000000),(516901704573/100000000000000),(562261057/50000000000000),(-21861979/100000000000000)⟩
def e202 : ℝ := (2154571/25000000000000)
theorem h202 : Model (fun x => f202 ((67/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2830451607728783/100000000000000),(1092119351881/25000000000000),(10227634943/100000000000000),(-2837679/1562500000000)⟩
def e203 : ℝ := (72917591/100000000000000)
theorem h203 : Model (fun x => f203 ((67/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1622566512021947/20000000000000),(1092119351881/25000000000000),(10227634943/100000000000000),(-2837679/1562500000000)⟩
def e204 : ℝ := (9114699/12500000000000)
theorem h204 : Model (fun x => f204 ((67/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4194430104851347/50000000000000),(3176048226111/20000000000000),(10353703739/25000000000000),(-640749531/100000000000000)⟩
def e205 : ℝ := (132771661/50000000000000)
theorem h205 : Model (fun x => f205 ((67/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13657907828750313/100000000000000),(3176048226111/20000000000000),(10353703739/25000000000000),(-640749531/100000000000000)⟩
def e206 : ℝ := (265543323/100000000000000)
theorem h206 : Model (fun x => f206 ((67/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(14122598819029573/100000000000000),(35550313233593/100000000000000),(106683250921/100000000000000),(-54609361/4000000000000)⟩
def e207 : ℝ := (595988931/100000000000000)
theorem h207 : Model (fun x => f207 ((67/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8229156552371929/50000000000000),(35550313233593/100000000000000),(106683250921/100000000000000),(-54609361/4000000000000)⟩
def e208 : ℝ := (148997233/25000000000000)
theorem h208 : Model (fun x => f208 ((67/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(680731356897851/4000000000000),(59811982610013/100000000000000),(210256074453/100000000000000),(-1064453567/50000000000000)⟩
def e209 : ℝ := (1005986647/100000000000000)
theorem h209 : Model (fun x => f209 ((67/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(17420664874827227/100000000000000),(59811982610013/100000000000000),(210256074453/100000000000000),(-1064453567/50000000000000)⟩
def e210 : ℝ := (125748331/12500000000000)
theorem h210 : Model (fun x => f210 ((67/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(72053513399777/400000000000),(86247026338609/100000000000000),(70853396029/20000000000000),(-55131527/2000000000000)⟩
def e211 : ℝ := (727875927/50000000000000)
theorem h211 : Model (fun x => f211 ((67/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(8997879651162601/50000000000000),(86247026338609/100000000000000),(70853396029/20000000000000),(-55131527/2000000000000)⟩
def e212 : ℝ := (291150371/20000000000000)
theorem h212 : Model (fun x => f212 ((67/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(3721607910335599/20000000000000),(57193491745941/50000000000000),(270977957987/50000000000000),(-315741209/10000000000000)⟩
def e213 : ℝ := (193751859/10000000000000)
theorem h213 : Model (fun x => f213 ((67/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(145401350664151/781250000000),(57193491745941/50000000000000),(270977957987/50000000000000),(-315741209/10000000000000)⟩
def e214 : ℝ := (1937518591/100000000000000)
theorem h214 : Model (fun x => f214 ((67/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(126645126103239/20000000000000),(7489907617011/25000000000000),(367756999/156250000000),(-102312799/100000000000000)⟩
def e215 : ℝ := (128885283/25000000000000)
theorem h215 : Model (fun x => f215 ((67/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(106920477469141/100000000000000),(289658312997/100000000000000),(413165701/50000000000000),(-11397313/100000000000000)⟩
def e216 : ℝ := (2425861/50000000000000)
theorem h216 : Model (fun x => f216 ((67/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(101701179258587/50000000000000),(140063687691/100000000000000),(152354609/50000000000000),(-5923891/100000000000000)⟩
def e217 : ℝ := (583819/25000000000000)
theorem h217 : Model (fun x => f217 ((67/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(413725194503489/100000000000000),(569785688379/100000000000000),(717874919/50000000000000),(-4649019/20000000000000)⟩
def e218 : ℝ := (4761137/50000000000000)
theorem h218 : Model (fun x => f218 ((67/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(420763401699931/50000000000000),(217304536623/12500000000000),(1244767671/25000000000000),(-17010637/25000000000000)⟩
def e219 : ℝ := (29118959/100000000000000)
theorem h219 : Model (fun x => f219 ((67/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1711685365669501/100000000000000),(2357346947499/50000000000000),(605066997/4000000000000),(-175980233/100000000000000)⟩
def e220 : ℝ := (79145837/100000000000000)
theorem h220 : Model (fun x => f220 ((67/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(915071082871621/50000000000000),(1999802435551/20000000000000),(21987104767/50000000000000),(-300470377/100000000000000)⟩
def e221 : ℝ := (169054021/100000000000000)
theorem h221 : Model (fun x => f221 ((67/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(51701179258587/6250000000000),(140063687691/12500000000000),(152354609/6250000000000),(-5923891/12500000000000)⟩
def e222 : ℝ := (583819/3125000000000)
theorem h222 : Model (fun x => f222 ((67/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(934139345606533/100000000000000),(56406712581/4000000000000),(1632002573/50000000000000),(-58788441/100000000000000)⟩
def e223 : ℝ := (2353393/10000000000000)
theorem h223 : Model (fun x => f223 ((67/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1034139345606533/100000000000000),(56406712581/4000000000000),(1632002573/50000000000000),(-58788441/100000000000000)⟩
def e224 : ℝ := (2353393/10000000000000)
theorem h224 : Model (fun x => f224 ((67/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(18926220216486393/100000000000000),(25842358976703/20000000000000),(16387334717/2500000000000),(-3236716017/100000000000000)⟩
def e225 : ℝ := (2192427623/100000000000000)
theorem h225 : Model (fun x => f225 ((67/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(2063935617/390625000000),(-721446909/20000000000000),(6327509/100000000000000),(86047/50000000000000)⟩
def e226 : ℝ := (16021/25000000000000)
theorem h226 : Model (fun x => f226 ((67/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (9398173749535279/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1672879273497/50000000000000),(135455022199/100000000000000),(101471363/50000000000000),(-1209059/20000000000000)⟩
def e227 : ℝ := (25299/781250000000)
theorem h227 : Model (fun x => f227 ((67/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(6807344582923/100000000000000),(17528251741/6250000000000),(124701011/20000000000000),(-11618843/100000000000000)⟩
def e228 : ℝ := (272331/6250000000000)
theorem h228 : Model (fun x => f228 ((67/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(4493673648663/50000000000000),(79272734193/25000000000000),(-192247811/25000000000000),(-976487/50000000000000)⟩
def e229 : ℝ := (10756763/25000000000000)
theorem h229 : Model (fun x => f229 ((67/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(1073116095203/20000000000000),(54612365633/50000000000000),(-26116489/1250000000000),(3752239/12500000000000)⟩
def e230 : ℝ := (1692027/6250000000000)
theorem h230 : Model (fun x => f230 ((67/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-3030163627863/2500000000000),(-221757049931/10000000000000),(47714533237/100000000000000),(-98496307/12500000000000)⟩
def e231 : ℝ := (13602229/20000000000000)
theorem h231 : Model (fun x => f231 ((67/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((67/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-4489/320),(-67/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((67/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1407/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((67/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6767/320),(17/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((67/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((67/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15087/320),(17/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((67/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((67/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(377175/32),(425/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((67/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(11591/1600),(53/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((67/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(21191/1600),(53/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((67/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((67/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4005099/1600),(10017/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((67/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(9987268729/25000000000000),(-199830209/100000000000000),(1442383/50000000000000),(-1193/5000000000000)⟩
def e244 : ℝ := (13/5000000000000)
theorem h244 : Model (fun x => f244 ((67/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (996219/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(470868510357571/100000000000000),(-1294195168781/100000000000000),(-629069801/25000000000000),(-24243581/50000000000000)⟩
def e245 : ℝ := (1195561/20000000000000)
theorem h245 : Model (fun x => f245 ((67/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(603/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((67/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(52729/1600),(427/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((67/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(86329/1600),(427/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((67/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(21609/1600),(147/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((67/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1865483361/2560000),(10958703/640000),(179507/1280000),(287/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((67/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((67/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(103041/160),(963/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((67/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(155277996137/100000000000000),(-725598113/25000000000000),(317873/781250000000),(-507013/100000000000000)⟩
def e253 : ℝ := (1217/20000000000000)
theorem h253 : Model (fun x => f253 ((67/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (50553/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(22630352978359/20000000000000),(543834743009/100000000000000),(69116507/4000000000000),(-2541513/25000000000000)⟩
def e254 : ℝ := (4465589/50000000000000)
theorem h254 : Model (fun x => f254 ((67/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(42630352978359/20000000000000),(543834743009/100000000000000),(69116507/4000000000000),(-2541513/25000000000000)⟩
def e255 : ℝ := (4465589/50000000000000)
theorem h255 : Model (fun x => f255 ((67/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(106575882445897/100000000000000),(16994835719/6250000000000),(863956337/100000000000000),(-2541513/50000000000000)⟩
def e256 : ℝ := (4465591/100000000000000)
theorem h256 : Model (fun x => f256 ((67/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(6575882445897/100000000000000),(16994835719/6250000000000),(863956337/100000000000000),(-2541513/50000000000000)⟩
def e257 : ℝ := (4465591/100000000000000)
theorem h257 : Model (fun x => f257 ((67/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(98328939161393/25000000000000),(31359518291/3125000000000),(3188410291/100000000000000),(-18758787/100000000000000)⟩
def e258 : ℝ := (16480159/100000000000000)
theorem h258 : Model (fun x => f258 ((67/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2749030042359857/100000000000000),(31359518291/3125000000000),(3188410291/100000000000000),(-18758787/100000000000000)⟩
def e259 : ℝ := (103001/625000000000)
theorem h259 : Model (fun x => f259 ((67/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2929803026347833/100000000000000),(8544584100221/100000000000000),(29877198951/100000000000000),(-35596643/25000000000000)⟩
def e260 : ℝ := (5619561/4000000000000)
theorem h260 : Model (fun x => f260 ((67/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(1642436795745757/20000000000000),(8544584100221/100000000000000),(29877198951/100000000000000),(-35596643/25000000000000)⟩
def e261 : ℝ := (70244513/50000000000000)
theorem h261 : Model (fun x => f261 ((67/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(1094025942926347/12500000000000),(15718410362087/50000000000000),(126025780813/100000000000000),(-414114423/100000000000000)⟩
def e262 : ℝ := (258891123/50000000000000)
theorem h262 : Model (fun x => f262 ((67/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(2804251032491679/20000000000000),(15718410362087/50000000000000),(126025780813/100000000000000),(-414114423/100000000000000)⟩
def e263 : ℝ := (517782247/100000000000000)
theorem h263 : Model (fun x => f263 ((67/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(14943276419380923/100000000000000),(17907574397337/25000000000000),(340932787111/100000000000000),(-539763751/100000000000000)⟩
def e264 : ℝ := (1182430047/100000000000000)
theorem h264 : Model (fun x => f264 ((67/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(2159873838136901/12500000000000),(17907574397337/25000000000000),(340932787111/100000000000000),(-539763751/100000000000000)⟩
def e265 : ℝ := (36950939/3125000000000)
theorem h265 : Model (fun x => f265 ((67/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(9207618410849869/50000000000000),(24665039820437/20000000000000),(353705141991/50000000000000),(92356397/100000000000000)⟩
def e266 : ℝ := (255052381/12500000000000)
theorem h266 : Model (fun x => f266 ((67/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(1881761777408069/10000000000000),(24665039820437/20000000000000),(353705141991/50000000000000),(92356397/100000000000000)⟩
def e267 : ℝ := (2040419049/100000000000000)
theorem h267 : Model (fun x => f267 ((67/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(4011008439604491/20000000000000),(91301645426131/50000000000000),(1251847393699/100000000000000),(2130972563/100000000000000)⟩
def e268 : ℝ := (23641771/781250000000)
theorem h268 : Model (fun x => f268 ((67/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(20037423150403407/100000000000000),(91301645426131/50000000000000),(1251847393699/100000000000000),(2130972563/100000000000000)⟩
def e269 : ℝ := (3026146689/100000000000000)
theorem h269 : Model (fun x => f269 ((67/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(10677530270980443/50000000000000),(249096302948757/100000000000000),(400762412511/20000000000000),(779274827/12500000000000)⟩
def e270 : ℝ := (2071885363/50000000000000)
theorem h270 : Model (fun x => f270 ((67/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(21358393875294219/100000000000000),(249096302948757/100000000000000),(400762412511/20000000000000),(779274827/12500000000000)⟩
def e271 : ℝ := (4143770727/100000000000000)
theorem h271 : Model (fun x => f271 ((67/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(351125718392753/25000000000000),(74457463280157/100000000000000),(993631642529/100000000000000),(6925097243/100000000000000)⟩
def e272 : ℝ := (127043583/10000000000000)
theorem h272 : Model (fun x => f272 ((67/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(7099011699451/6250000000000),(72449584551/12500000000000),(2580928749/100000000000000),(-1227213/20000000000000)⟩
def e273 : ℝ := (4781559/50000000000000)
theorem h273 : Model (fun x => f273 ((67/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(206575882445897/100000000000000),(16994835719/6250000000000),(863956337/100000000000000),(-2541513/50000000000000)⟩
def e274 : ℝ := (4465591/100000000000000)
theorem h274 : Model (fun x => f274 ((67/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(42673595208301/10000000000000),(140428927427/12500000000000),(4308841423/100000000000000),(-16302117/100000000000000)⟩
def e275 : ℝ := (184943/1000000000000)
theorem h275 : Model (fun x => f275 ((67/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(440766779364689/50000000000000),(3481107552499/100000000000000),(15642644679/100000000000000),(-33944897/100000000000000)⟩
def e276 : ℝ := (57426427/100000000000000)
theorem h276 : Model (fun x => f276 ((67/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(455258932000483/25000000000000),(1198521440911/12500000000000),(24697866241/50000000000000),(-42320233/100000000000000)⟩
def e277 : ℝ := (9902677/6250000000000)
theorem h277 : Model (fun x => f277 ((67/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(2068408630112637/100000000000000),(21445309251471/100000000000000),(7933904969/5000000000000),(37395087/10000000000000)⟩
def e278 : ℝ := (44550409/12500000000000)
theorem h278 : Model (fun x => f278 ((67/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(106575882445897/12500000000000),(16994835719/781250000000),(863956337/12500000000000),(-2541513/6250000000000)⟩
def e279 : ℝ := (4465591/12500000000000)
theorem h279 : Model (fun x => f279 ((67/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(120773905844799/12500000000000),(68873391211/2500000000000),(1898515889/20000000000000),(-46800273/100000000000000)⟩
def e280 : ℝ := (22643923/50000000000000)
theorem h280 : Model (fun x => f280 ((67/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(133273905844799/12500000000000),(68873391211/2500000000000),(1898515889/20000000000000),(-46800273/100000000000000)⟩
def e281 : ℝ := (22643923/50000000000000)
theorem h281 : Model (fun x => f281 ((67/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(22053191761456101/100000000000000),(285631336785833/100000000000000),(2478961808059/100000000000000),(9426203101/100000000000000)⟩
def e282 : ℝ := (596460303/12500000000000)
theorem h282 : Model (fun x => f282 ((67/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(226724550989/50000000000000),(-5873039811/100000000000000),(25095741/100000000000000),(70661/50000000000000)⟩
def e283 : ℝ := (20581/20000000000000)
theorem h283 : Model (fun x => f283 ((67/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (5441266816244171/25000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(3184352833731/50000000000000),(31892460711/12500000000000),(242583851/50000000000000),(-6284067/100000000000000)⟩
def e284 : ℝ := (7413953/100000000000000)
theorem h284 : Model (fun x => f284 ((67/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(22630352978359/10000000000000),(543834743009/50000000000000),(69116507/2000000000000),(-2541513/12500000000000)⟩
def e285 : ℝ := (4465589/25000000000000)
theorem h285 : Model (fun x => f285 ((67/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(46914929393507/100000000000000),(-119698603401/100000000000000),(-74916771/100000000000000),(849759/25000000000000)⟩
def e286 : ℝ := (24871/1250000000000)
theorem h286 : Model (fun x => f286 ((67/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (212606183138881/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(21234028242597/20000000000000),(239397206801/100000000000000),(149833541/100000000000000),(-1699519/25000000000000)⟩
def e287 : ℝ := (3246197/25000000000000)
theorem h287 : Model (fun x => f287 ((67/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(1234028242597/20000000000000),(239397206801/100000000000000),(149833541/100000000000000),(-1699519/25000000000000)⟩
def e288 : ℝ := (3246197/25000000000000)
theorem h288 : Model (fun x => f288 ((67/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(6122162160719/1562500000000),(176697938353/20000000000000),(110591423/20000000000000),(-12544069/50000000000000)⟩
def e289 : ℝ := (47920053/100000000000000)
theorem h289 : Model (fun x => f289 ((67/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2747532664000301/100000000000000),(176697938353/20000000000000),(110591423/20000000000000),(-12544069/50000000000000)⟩
def e290 : ℝ := (23960027/50000000000000)
theorem h290 : Model (fun x => f290 ((67/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(364632413655251/12500000000000),(751551870691/10000000000000),(3409425237/50000000000000),(-210767943/100000000000000)⟩
def e291 : ℝ := (50998381/12500000000000)
theorem h291 : Model (fun x => f291 ((67/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(102493003270287/1250000000000),(751551870691/10000000000000),(3409425237/50000000000000),(-210767943/100000000000000)⟩
def e292 : ℝ := (407987049/100000000000000)
theorem h292 : Model (fun x => f292 ((67/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(8705357304439443/100000000000000),(3451058472957/12500000000000),(9379259181/25000000000000),(-376795949/50000000000000)⟩
def e293 : ℝ := (375200153/25000000000000)
theorem h293 : Model (fun x => f293 ((67/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(6987202461743531/50000000000000),(3451058472957/12500000000000),(9379259181/25000000000000),(-376795949/50000000000000)⟩
def e294 : ℝ := (1500800613/100000000000000)
theorem h294 : Model (fun x => f294 ((67/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(7418322720470271/50000000000000),(31383142143269/50000000000000),(126864137313/100000000000000),(-1618898767/100000000000000)⟩
def e295 : ℝ := (3418762717/100000000000000)
theorem h295 : Model (fun x => f295 ((67/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(17172359726654827/100000000000000),(31383142143269/50000000000000),(126864137313/100000000000000),(-1618898767/100000000000000)⟩
def e296 : ℝ := (1709381359/50000000000000)
theorem h296 : Model (fun x => f296 ((67/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(9115959285695597/50000000000000),(6734325136787/6250000000000),(15534125989/5000000000000),(-99536921/4000000000000)⟩
def e297 : ℝ := (5883820259/100000000000000)
theorem h297 : Model (fun x => f297 ((67/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(9317149761886073/50000000000000),(6734325136787/6250000000000),(15534125989/5000000000000),(-99536921/4000000000000)⟩
def e298 : ℝ := (294191013/5000000000000)
theorem h298 : Model (fun x => f298 ((67/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(9892031059219739/50000000000000),(31801494537267/20000000000000),(615721081181/100000000000000),(-750881591/25000000000000)⟩
def e299 : ℝ := (108843169/1250000000000)
theorem h299 : Model (fun x => f299 ((67/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(1976644307082043/10000000000000),(31801494537267/20000000000000),(615721081181/100000000000000),(-750881591/25000000000000)⟩
def e300 : ℝ := (8707453521/100000000000000)
theorem h300 : Model (fun x => f300 ((67/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(20986060521074339/100000000000000),(108069385442867/50000000000000),(531994075583/50000000000000),(-352540051/12500000000000)⟩
def e301 : ℝ := (5935028767/50000000000000)
theorem h301 : Model (fun x => f301 ((67/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(2623674231800959/12500000000000),(108069385442867/50000000000000),(531994075583/50000000000000),(-352540051/12500000000000)⟩
def e302 : ℝ := (2374011507/20000000000000)
theorem h302 : Model (fun x => f302 ((67/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(323768810141637/25000000000000),(15896022497893/25000000000000),(614528903777/100000000000000),(127011359/10000000000000)⟩
def e303 : ℝ := (883598899/25000000000000)
theorem h303 : Model (fun x => f303 ((67/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(112720988851851/100000000000000),(508336705041/100000000000000),(89126719/10000000000000),(-685883/5000000000000)⟩
def e304 : ℝ := (432289/1562500000000)
theorem h304 : Model (fun x => f304 ((67/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(41234028242597/20000000000000),(239397206801/100000000000000),(149833541/100000000000000),(-1699519/25000000000000)⟩
def e305 : ℝ := (3246197/25000000000000)
theorem h305 : Model (fun x => f305 ((67/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(425061271277821/100000000000000),(987131118643/100000000000000),(4652087/390625000000),(-6828453/25000000000000)⟩
def e306 : ℝ := (6704509/12500000000000)
theorem h306 : Model (fun x => f306 ((67/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(109543677904399/12500000000000),(610550886379/20000000000000),(109107991/2000000000000),(-80878797/100000000000000)⟩
def e307 : ℝ := (20770317/12500000000000)
theorem h307 : Model (fun x => f307 ((67/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(903385421701587/50000000000000),(1678364832833/20000000000000),(19403007/97656250000),(-104344353/50000000000000)⟩
def e308 : ℝ := (457558309/100000000000000)
theorem h308 : Model (fun x => f308 ((67/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1018304980485493/50000000000000),(1165239159597/6250000000000),(20289512451/25000000000000),(-30728929/10000000000000)⟩
def e309 : ℝ := (255582863/25000000000000)
theorem h309 : Model (fun x => f309 ((67/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(21234028242597/2500000000000),(239397206801/12500000000000),(149833541/12500000000000),(-1699519/3125000000000)⟩
def e310 : ℝ := (3246197/3125000000000)
theorem h310 : Model (fun x => f310 ((67/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(962082118555731/100000000000000),(2423514359449/100000000000000),(1044967759/50000000000000),(-17025567/25000000000000)⟩
def e311 : ℝ := (164431/125000000000)
theorem h311 : Model (fun x => f311 ((67/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1062082118555731/100000000000000),(2423514359449/100000000000000),(1044967759/50000000000000),(-17025567/25000000000000)⟩
def e312 : ℝ := (164431/125000000000)
theorem h312 : Model (fun x => f312 ((67/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(10815235110098847/50000000000000),(247370282889921/100000000000000),(27127295667/2000000000000),(-143382577/6250000000000)⟩
def e313 : ℝ := (13604995771/100000000000000)
theorem h313 : Model (fun x => f313 ((67/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(3698486403/800000000000),(-42296613/800000000000),(31474283/100000000000000),(20619/100000000000000)⟩
def e314 : ℝ := (60071/20000000000000)
theorem h314 : Model (fun x => f314 ((67/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (1069086383670371/5000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(5987272710121/100000000000000),(225484495031/100000000000000),(-5654521/5000000000000),(-3169537/50000000000000)⟩
def e315 : ℝ := (20750439/100000000000000)
theorem h315 : Model (fun x => f315 ((67/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(12355978377583/100000000000000),(480624180719/100000000000000),(186038641/50000000000000),(-12623141/100000000000000)⟩
def e316 : ℝ := (3520549/12500000000000)
theorem h316 : Model (fun x => f316 ((67/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(14545102831657/25000000000000),(2103197444951/100000000000000),(-4779131087/100000000000000),(-10292339/12500000000000)⟩
def e317 : ℝ := (133829031/100000000000000)
theorem h317 : Model (fun x => f317 ((67/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(4341821740793/12500000000000),(737213789129/100000000000000),(-13856403473/100000000000000),(157654551/100000000000000)⟩
def e318 : ℝ := (21750029/25000000000000)
theorem h318 : Model (fun x => f318 ((67/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-5404498199261/6250000000000),(-1480356710181/100000000000000),(8464532441/25000000000000),(-126063181/20000000000000)⟩
def e319 : ℝ := (155011261/100000000000000)
theorem h319 : Model (fun x => f319 ((67/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((67/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-49379/1600),(-737/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((67/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((67/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(6499/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((67/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(210581/1600),(1203/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((67/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((67/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(383381/1600),(1203/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((67/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1916905/32),(6015/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((67/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((67/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(484740053966009751/50000000000000),(969891854474013/20000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (62897/50000000000000)
theorem h329 : Model (fun x => f329 ((67/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10314806789/100000000000000),(-25797969/50000000000000),(744843/100000000000000),(-6161/100000000000000)⟩
def e330 : ℝ := (69/100000000000000)
theorem h330 : Model (fun x => f330 ((67/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (482292449521873283/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(154472693030219/25000000000000),(196739172967/25000000000000),(1498623521/20000000000000),(-369183/100000000000000)⟩
def e331 : ℝ := (3883163/50000000000000)
theorem h331 : Model (fun x => f331 ((67/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((67/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(427/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((67/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((67/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((67/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(585806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((67/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((67/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((67/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2598926375868877/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1037/100000000000000)
theorem h339 : Model (fun x => f339 ((67/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3684193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((67/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((67/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((67/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(129754601508179/6250000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1037/100000000000000)
theorem h343 : Model (fun x => f343 ((67/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2408392429769/50000000000000),(-408568479/6250000000000),(4435907/50000000000000),(-12041/100000000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((67/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1036628041247673/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(125184692183391/100000000000000),(224646748149/25000000000000),(-121951661/10000000000000),(1655049/100000000000000)⟩
def e345 : ℝ := (3247/100000000000000)
theorem h345 : Model (fun x => f345 ((67/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(225184692183391/100000000000000),(224646748149/25000000000000),(-121951661/10000000000000),(1655049/100000000000000)⟩
def e346 : ℝ := (3247/100000000000000)
theorem h346 : Model (fun x => f346 ((67/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(22518469218339/20000000000000),(224646748149/50000000000000),(-121951661/20000000000000),(206881/25000000000000)⟩
def e347 : ℝ := (13/800000000000)
theorem h347 : Model (fun x => f347 ((67/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(2518469218339/20000000000000),(224646748149/50000000000000),(-121951661/20000000000000),(206881/25000000000000)⟩
def e348 : ℝ := (13/800000000000)
theorem h348 : Model (fun x => f348 ((67/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(83103874496251/20000000000000),(1658106950623/100000000000000),(-2250298507/100000000000000),(3053957/100000000000000)⟩
def e349 : ℝ := (3/50000000000)
theorem h349 : Model (fun x => f349 ((67/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(138561682909777/5000000000000),(1658106950623/100000000000000),(-2250298507/100000000000000),(3053957/100000000000000)⟩
def e350 : ℝ := (6001/100000000000000)
theorem h350 : Model (fun x => f350 ((67/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1560098495722531/50000000000000),(14317874109909/100000000000000),(-479268983/4000000000000),(1230051/20000000000000)⟩
def e351 : ℝ := (11631/12500000000000)
theorem h351 : Model (fun x => f351 ((67/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4201288971913007/50000000000000),(14317874109909/100000000000000),(-479268983/4000000000000),(1230051/20000000000000)⟩
def e352 : ℝ := (93049/100000000000000)
theorem h352 : Model (fun x => f352 ((67/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1892131927827403/20000000000000),(26936533296891/50000000000000),(-24790279/6250000000000),(-64679471/100000000000000)⟩
def e353 : ℝ := (230637/50000000000000)
theorem h353 : Model (fun x => f353 ((67/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(7364853629092317/50000000000000),(26936533296891/50000000000000),(-24790279/6250000000000),(-64679471/100000000000000)⟩
def e354 : ℝ := (18451/4000000000000)
theorem h354 : Model (fun x => f354 ((67/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(16584522974428761/100000000000000),(63418283162119/50000000000000),(30357195969/20000000000000),(-281209867/100000000000000)⟩
def e355 : ℝ := (919693/100000000000000)
theorem h355 : Model (fun x => f355 ((67/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(9460118630071523/50000000000000),(63418283162119/50000000000000),(30357195969/20000000000000),(-281209867/100000000000000)⟩
def e356 : ℝ := (459847/50000000000000)
theorem h356 : Model (fun x => f356 ((67/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(2130273901731009/10000000000000),(227815661220581/100000000000000),(156350030287/25000000000000),(-62870811/25000000000000)⟩
def e357 : ℝ := (1245759/50000000000000)
theorem h357 : Model (fun x => f357 ((67/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(10852559984845521/50000000000000),(227815661220581/100000000000000),(156350030287/25000000000000),(-62870811/25000000000000)⟩
def e358 : ℝ := (2491519/100000000000000)
theorem h358 : Model (fun x => f358 ((67/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(12219151897946071/50000000000000),(17701134506003/5000000000000),(1595364846647/100000000000000),(329305337/25000000000000)⟩
def e359 : ℝ := (6237701/100000000000000)
theorem h359 : Model (fun x => f359 ((67/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(12210342374136547/50000000000000),(17701134506003/5000000000000),(1595364846647/100000000000000),(329305337/25000000000000)⟩
def e360 : ℝ := (3118851/50000000000000)
theorem h360 : Model (fun x => f360 ((67/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(27495821889737417/100000000000000),(101664600165707/20000000000000),(32379524783/1000000000000),(6694365189/100000000000000)⟩
def e361 : ℝ := (1667819/20000000000000)
theorem h361 : Model (fun x => f361 ((67/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(109996620892283/400000000000),(101664600165707/20000000000000),(32379524783/1000000000000),(6694365189/100000000000000)⟩
def e362 : ℝ := (1042387/12500000000000)
theorem h362 : Model (fun x => f362 ((67/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(3462788797981491/100000000000000),(187561707482167/100000000000000),(630979495621/25000000000000),(6259453963/50000000000000)⟩
def e363 : ℝ := (804851/5000000000000)
theorem h363 : Model (fun x => f363 ((67/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(396157387451/312500000000),(505870088319/50000000000000),(129112819/20000000000000),(-451969/12500000000000)⟩
def e364 : ℝ := (14841/100000000000000)
theorem h364 : Model (fun x => f364 ((67/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(42518469218339/20000000000000),(224646748149/50000000000000),(-121951661/20000000000000),(206881/25000000000000)⟩
def e365 : ℝ := (13/800000000000)
theorem h365 : Model (fun x => f365 ((67/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(45195505616771/10000000000000),(955163584617/50000000000000),(-114790503/20000000000000),(-7659/390625000000)⟩
def e366 : ℝ := (18091/100000000000000)
theorem h366 : Model (fun x => f366 ((67/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(240205464296743/25000000000000),(6091814020653/100000000000000),(2303481561/50000000000000),(-732769/5000000000000)⟩
def e367 : ℝ := (2257/4000000000000)
theorem h367 : Model (fun x => f367 ((67/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1021316863977789/50000000000000),(17267640461399/100000000000000),(6261096823/20000000000000),(-39651741/100000000000000)⟩
def e368 : ℝ := (89789/50000000000000)
theorem h368 : Model (fun x => f368 ((67/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2589454211795771/100000000000000),(5319549593963/12500000000000),(45515248441/20000000000000),(15204031/5000000000000)⟩
def e369 : ℝ := (680003/50000000000000)
theorem h369 : Model (fun x => f369 ((67/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(22518469218339/2500000000000),(224646748149/6250000000000),(-121951661/2500000000000),(206881/3125000000000)⟩
def e370 : ℝ := (13/100000000000)
theorem h370 : Model (fun x => f370 ((67/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(25687728317947/2500000000000),(2303044073511/50000000000000),(-846500469/20000000000000),(75111/2500000000000)⟩
def e371 : ℝ := (27841/100000000000000)
theorem h371 : Model (fun x => f371 ((67/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(28187728317947/2500000000000),(2303044073511/50000000000000),(-846500469/20000000000000),(75111/2500000000000)⟩
def e372 : ℝ := (27841/100000000000000)
theorem h372 : Model (fun x => f372 ((67/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(29196332725545113/100000000000000),(149774950863301/25000000000000),(44165293511/1000000000000),(6093748593/50000000000000)⟩
def e373 : ℝ := (5447103/25000000000000)
theorem h373 : Model (fun x => f373 ((67/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(68501753929/20000000000000),(-7028175029/100000000000000),(18480939/20000000000000),(-975939/100000000000000)⟩
def e374 : ℝ := (9553/100000000000000)
theorem h374 : Model (fun x => f374 ((67/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (28592804183455211/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(11860355307371/100000000000000),(79808887803/20000000000000),(-668872617/50000000000000),(5014101/100000000000000)⟩
def e375 : ℝ := (796549/100000000000000)
theorem h375 : Model (fun x => f375 ((67/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(125184692183391/50000000000000),(224646748149/12500000000000),(-121951661/5000000000000),(1655049/50000000000000)⟩
def e376 : ℝ := (3247/50000000000000)
theorem h376 : Model (fun x => f376 ((67/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(44407991960021/100000000000000),(-88603811289/50000000000000),(189526869/20000000000000),(-126689/2500000000000)⟩
def e377 : ℝ := (13723/50000000000000)
theorem h377 : Model (fun x => f377 ((67/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (224284884015889/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(55592008039977/50000000000000),(11075476411/3125000000000),(-947634347/50000000000000),(10135119/100000000000000)⟩
def e378 : ℝ := (38463/20000000000000)
theorem h378 : Model (fun x => f378 ((67/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(5592008039977/50000000000000),(11075476411/3125000000000),(-947634347/50000000000000),(10135119/100000000000000)⟩
def e379 : ℝ := (38463/20000000000000)
theorem h379 : Model (fun x => f379 ((67/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(25645122756537/6250000000000),(52318440951/4000000000000),(-699444399/10000000000000),(7480683/20000000000000)⟩
def e380 : ℝ := (141947/20000000000000)
theorem h380 : Model (fun x => f380 ((67/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2766036249818877/100000000000000),(52318440951/4000000000000),(-699444399/10000000000000),(7480683/20000000000000)⟩
def e381 : ℝ := (88717/12500000000000)
theorem h381 : Model (fun x => f381 ((67/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(384423773596997/12500000000000),(5628748875391/50000000000000),(-5556490957/10000000000000),(68087233/25000000000000)⟩
def e382 : ℝ := (6512789/100000000000000)
theorem h382 : Model (fun x => f382 ((67/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(130590174080577/1562500000000),(5628748875391/50000000000000),(-5556490957/10000000000000),(68087233/25000000000000)⟩
def e383 : ℝ := (651279/10000000000000)
theorem h383 : Model (fun x => f383 ((67/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(9292505609509673/100000000000000),(10534438297151/25000000000000),(-36056645939/20000000000000),(73958819/10000000000000)⟩
def e384 : ℝ := (26529527/100000000000000)
theorem h384 : Model (fun x => f384 ((67/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3640388307139323/25000000000000),(10534438297151/25000000000000),(-36056645939/20000000000000),(73958819/10000000000000)⟩
def e385 : ℝ := (3316191/12500000000000)
theorem h385 : Model (fun x => f385 ((67/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(80950598415651/500000000000),(98458810853879/100000000000000),(-32708407353/10000000000000),(172111941/20000000000000)⟩
def e386 : ℝ := (68017703/100000000000000)
theorem h386 : Model (fun x => f386 ((67/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3705166793768897/20000000000000),(98458810853879/100000000000000),(-32708407353/10000000000000),(172111941/20000000000000)⟩
def e387 : ℝ := (8502213/12500000000000)
theorem h387 : Model (fun x => f387 ((67/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(643680194339551/3125000000000),(2189110499613/1250000000000),(-365826504561/100000000000000),(-190874681/100000000000000)⟩
def e388 : ℝ := (6548133/5000000000000)
theorem h388 : Model (fun x => f388 ((67/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(2625018396405823/12500000000000),(2189110499613/1250000000000),(-365826504561/100000000000000),(-190874681/100000000000000)⟩
def e389 : ℝ := (130962661/100000000000000)
theorem h389 : Model (fun x => f389 ((67/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(23348807007692807/100000000000000),(67285750167767/25000000000000),(-184066507179/100000000000000),(-674884803/25000000000000)⟩
def e390 : ℝ := (210840033/100000000000000)
theorem h390 : Model (fun x => f390 ((67/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(23331187960073759/100000000000000),(67285750167767/25000000000000),(-184066507179/100000000000000),(-674884803/25000000000000)⟩
def e391 : ℝ := (105420017/50000000000000)
theorem h391 : Model (fun x => f391 ((67/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(25940551773172699/100000000000000),(149192689121/39062500000),(38380323669/12500000000000),(-1278031049/20000000000000)⟩
def e392 : ℝ := (37723843/12500000000000)
theorem h392 : Model (fun x => f392 ((67/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(1621492819156627/6250000000000),(149192689121/39062500000),(38380323669/12500000000000),(-1278031049/20000000000000)⟩
def e393 : ℝ := (60358149/20000000000000)
theorem h393 : Model (fun x => f393 ((67/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(116062731283057/4000000000000),(67332281958091/50000000000000),(89626314547/10000000000000),(-4235688583/100000000000000)⟩
def e394 : ℝ := (23963019/25000000000000)
theorem h394 : Model (fun x => f394 ((67/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(61809427158337/50000000000000),(788106206319/100000000000000),(-73959251/2500000000000),(4551511/50000000000000)⟩
def e395 : ℝ := (537167/100000000000000)
theorem h395 : Model (fun x => f395 ((67/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(105592008039977/50000000000000),(11075476411/3125000000000),(-947634347/50000000000000),(10135119/100000000000000)⟩
def e396 : ℝ := (38463/20000000000000)
theorem h396 : Model (fun x => f396 ((67/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(222993443238291/50000000000000),(1496936696623/100000000000000),(-1687226857/25000000000000),(1468663/5000000000000)⟩
def e397 : ℝ := (921797/100000000000000)
theorem h397 : Model (fun x => f397 ((67/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(941853018051191/100000000000000),(2370968275577/50000000000000),(-4349972931/25000000000000),(27471401/50000000000000)⟩
def e398 : ℝ := (159777/5000000000000)
theorem h398 : Model (fun x => f398 ((67/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1989043029090759/100000000000000),(13352282731587/100000000000000),(-37790289479/100000000000000),(58543/97656250000)⟩
def e399 : ℝ := (1198531/12500000000000)
theorem h399 : Model (fun x => f399 ((67/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(491766440885533/20000000000000),(3218171049653/10000000000000),(-16450353/5000000000000),(-218833727/50000000000000)⟩
def e400 : ℝ := (398379/1562500000000)
theorem h400 : Model (fun x => f400 ((67/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(55592008039977/6250000000000),(11075476411/390625000000),(-947634347/6250000000000),(10135119/12500000000000)⟩
def e401 : ℝ := (38463/2500000000000)
theorem h401 : Model (fun x => f401 ((67/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(506545491478153/50000000000000),(724685633507/20000000000000),(-2265064949/12500000000000),(45091987/50000000000000)⟩
def e402 : ℝ := (2075687/100000000000000)
theorem h402 : Model (fun x => f402 ((67/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(556545491478153/50000000000000),(724685633507/20000000000000),(-2265064949/12500000000000),(45091987/50000000000000)⟩
def e403 : ℝ := (2075687/100000000000000)
theorem h403 : Model (fun x => f403 ((67/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(27369039553510103/100000000000000),(13978304262051/3125000000000),(716865843669/100000000000000),(-424878943/5000000000000)⟩
def e404 : ℝ := (174866941/50000000000000)
theorem h404 : Model (fun x => f404 ((67/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(182688179109/50000000000000),(-2985763177/50000000000000),(17605091/20000000000000),(-146099/12500000000000)⟩
def e405 : ℝ := (10039/50000000000000)
theorem h405 : Model (fun x => f405 ((67/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (1346050405198403/5000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(10601644520259/100000000000000),(318764564803/100000000000000),(-2212677601/100000000000000),(7814501/50000000000000)⟩
def e406 : ℝ := (378039/25000000000000)
theorem h406 : Model (fun x => f406 ((67/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2246199982763/10000000000000),(358904501909/50000000000000),(-710084567/20000000000000),(20643103/100000000000000)⟩
def e407 : ℝ := (461741/20000000000000)
theorem h407 : Model (fun x => f407 ((67/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(34697656042183/25000000000000),(922408361363/20000000000000),(-2921157003/20000000000000),(30662977/20000000000000)⟩
def e408 : ℝ := (16191911/100000000000000)
theorem h408 : Model (fun x => f408 ((67/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(16572014826117/20000000000000),(60669610831/4000000000000),(-31357786141/100000000000000),(139889483/25000000000000)⟩
def e409 : ℝ := (26639907/100000000000000)
theorem h409 : Model (fun x => f409 ((67/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3611897057591/100000000000000),(18191780297/50000000000000),(2500343623/100000000000000),(-70757973/100000000000000)⟩
def e410 : ℝ := (5676599/3125000000000)
theorem h410 : Model (fun x => f410 ((67/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(2105634713867187/100000000000000),(36347091064453/25000000000000),(408499/10240000),(5561/10240000)⟩
def e411 : ℝ := (367187501/100000000000000)
theorem h411 : Model (fun x => f411 ((67/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(34969/1600),(187/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((67/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(6539203/64000),(104907/64000),(561/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((67/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(53785831397751761/25000000000000),(18306560135116281/100000000000000),(332187664058929/50000000000000),(1339516717517/10000000000000)⟩
def e414 : ℝ := (164919583647/100000000000000)
theorem h414 : Model (fun x => f414 ((67/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(9296128497/20000000000000),(-791008203/20000000000000),(192999731/100000000000000),(-7102919/100000000000000)⟩
def e415 : ℝ := (166611/50000000000000)
theorem h415 : Model (fun x => f415 ((67/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (24519853755126761/12500000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2673894842433/50000000000000),(25470013443/50000000000000),(-1217495701/50000000000000),(1423743/2500000000000)⟩
def e416 : ℝ := (15429397/20000000000000)
theorem h416 : Model (fun x => f416 ((67/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(69435705091/4000000000000),(2183089687/2500000000000),(65352221/100000000000000),(-13808253/100000000000000)⟩
def e417 : ℝ := (258798153/100000000000000)
theorem h417 : Model (fun x => f417 ((67/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((67/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((5206966839587/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (33/20) (17/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (33/20) (17/10) ≤ (1041703925701/1200000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(67/40)-(1/40)) (by norm_num : ((67/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel13


noncomputable section
namespace Hf4Quad.Panel14
open Hf4Quad.Dag

def p0 : Cubic := ⟨(69/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((69/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((69/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((69/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((69/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(151142857142857/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((69/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-151142857142857/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((69/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-210857142857143/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((69/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((69/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(4761/1600),(69/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((69/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(360223809523809/100000000000000),(10441269841269/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((69/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-360223809523809/100000000000000),(-10441269841269/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((69/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-71385119047619/12500000000000),(-14822222222221/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((69/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((69/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(328509/64000),(14283/64000),(207/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((69/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(64010587/1280000),(2783069/1280000),(1575559895833/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((69/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-64010587/1280000),(-2783069/1280000),(-1575559895833/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((69/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-348244253859747/6250000000000),(-232249487847221/100000000000000),(-3226781167327/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((69/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((69/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(22667121/2560000),(328509/640000),(14283/1280000),(69/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((69/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(618398638392857/25000000000000),(28679357142857/20000000000000),(3117321428571/100000000000000),(30119047619/100000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((69/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-774578377046131/25000000000000),(-11106587766617/12500000000000),(-27364934689/25000000000000),(7448123347/50000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((69/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((69/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(381843591064453/25000000000000),(27669825439453/25000000000000),(328509/10240000),(4761/10240000)⟩
def e22 : ℝ := (168945313/50000000000000)
theorem h22 : Model (fun x => f22 ((69/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(621910071002197/6250000000000),(5633243396759/781250000000),(10450074707031/50000000000000),(60580143229/20000000000000)⟩
def e23 : ℝ := (110064743/5000000000000)
theorem h23 : Model (fun x => f23 ((69/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(1713061906962657/25000000000000),(79025306581527/12500000000000),(10395344837653/50000000000000),(317796962839/100000000000000)⟩
def e24 : ℝ := (577605463/25000000000000)
theorem h24 : Model (fun x => f24 ((69/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((69/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(105388831133789/4000000000000),(229106154638671/100000000000000),(1660189526367/20000000000000),(40101196289/25000000000000)⟩
def e26 : ℝ := (1753662113/100000000000000)
theorem h26 : Model (fun x => f26 ((69/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(5916272477933869/100000000000000),(514458476342073/100000000000000),(2329974983433/12500000000000),(360189369419/100000000000000)⟩
def e27 : ℝ := (984463229/25000000000000)
theorem h27 : Model (fun x => f27 ((69/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(12768520105784497/100000000000000),(1146660928994289/100000000000000),(3943048954277/10000000000000),(338993166129/50000000000000)⟩
def e28 : ℝ := (390517173/6250000000000)
theorem h28 : Model (fun x => f28 ((69/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((69/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(90897866852893/2000000000000),(18443045448413/4000000000000),(10023394265441/50000000000000),(484221945189/100000000000000)⟩
def e30 : ℝ := (7079028329/100000000000000)
theorem h30 : Model (fun x => f30 ((69/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(134813800540749/12500000000000),(13676762373699/12500000000000),(4757134738677/100000000000000),(114906636199/100000000000000)⟩
def e31 : ℝ := (839932331/50000000000000)
theorem h31 : Model (fun x => f31 ((69/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(13847030510110489/100000000000000),(1256075027983881/100000000000000),(44187624281447/100000000000000),(792892968457/100000000000000)⟩
def e32 : ℝ := (792813943/10000000000000)
theorem h32 : Model (fun x => f32 ((69/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((69/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2042469/320),(29601/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((69/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((69/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(152421/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((69/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(896241/64),(47273/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((69/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((69/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1042161/64),(47273/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((69/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1042161/64),(-47273/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((69/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((69/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(109/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((69/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(11881/1600),(109/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((69/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((69/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(249501/160),(2289/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((69/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(32063999743/50000000000000),(-588330271/50000000000000),(253009/1562500000000),(-7923/4000000000000)⟩
def e46 : ℝ := (467/20000000000000)
theorem h46 : Model (fun x => f46 ((69/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (122451/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-208849062726029/20000000000000),(213446237977/100000000000000),(-998000249/50000000000000),(291713/1562500000000)⟩
def e47 : ℝ := (15159097/20000000000000)
theorem h47 : Model (fun x => f47 ((69/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((69/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(149/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((69/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((69/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((69/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(24833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((69/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(44833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((69/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((69/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(28020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((69/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((69/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(588437499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((69/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((69/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(3020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((69/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(142205729166649/50000000000000),(2172916666663/20000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (107/100000000000000)
theorem h60 : Model (fun x => f60 ((69/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(31406684027777/25000000000000),(58376736111/6250000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/10000000000000)
theorem h61 : Model (fun x => f61 ((69/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((69/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(28020833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((69/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(311615017361107/25000000000000),(1275173611109/25000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (1/2000000000000)
theorem h64 : Model (fun x => f64 ((69/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(336615017361107/25000000000000),(1275173611109/25000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (1/2000000000000)
theorem h65 : Model (fun x => f65 ((69/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1914743359691217/50000000000000),(80397117874573/50000000000000),(131250474717/12500000000000),(2048249421/100000000000000)⟩
def e66 : ℝ := (317277/50000000000000)
theorem h66 : Model (fun x => f66 ((69/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(53020833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((69/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(112448350694443/25000000000000),(441840277777/25000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (9/50000000000000)
theorem h68 : Model (fun x => f68 ((69/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(476968420862259/50000000000000),(702802191839/12500000000000),(345187717/3125000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (59/100000000000000)
theorem h69 : Model (fun x => f69 ((69/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(18265442332568323/50000000000000),(218648148372563/12500000000000),(9739950870309/50000000000000),(96612963179/100000000000000)⟩
def e70 : ℝ := (249169857/100000000000000)
theorem h70 : Model (fun x => f70 ((69/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((69/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(659540364583317/3125000000000),(1225911458331/781250000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1250000000000)
theorem h72 : Model (fun x => f72 ((69/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(255022274305521/10000000000000),(21379895833297/20000000000000),(137812499999/20000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (133/12500000000000)
theorem h73 : Model (fun x => f73 ((69/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(24327514292041239/100000000000000),(46525507442419/4000000000000),(12865253892417/100000000000000),(62327555071/100000000000000)⟩
def e74 : ℝ := (152370727/100000000000000)
theorem h74 : Model (fun x => f74 ((69/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(12171679791435577/20000000000000),(2912322873040979/100000000000000),(6469031126607/20000000000000),(635762073/400000000000)⟩
def e75 : ℝ := (50192573/12500000000000)
theorem h75 : Model (fun x => f75 ((69/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((69/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(219846788194439/3125000000000),(408637152777/781250000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1250000000000)
theorem h77 : Model (fun x => f77 ((69/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(365017361111/25000000000000),(25173611111/25000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((69/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(17642505787/10000000000000),(3650173611/20000000000000),(629340277/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((69/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(3102918586379/25000000000000),(688123209113/50000000000000),(53992442637/100000000000000),(855828409/100000000000000)⟩
def e80 : ℝ := (137587/3125000000000)
theorem h80 : Model (fun x => f80 ((69/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(1645193292153/6250000000000),(2970504588427/100000000000000),(15030416521/12500000000000),(255004741/12500000000000)⟩
def e81 : ℝ := (1292187/10000000000000)
theorem h81 : Model (fun x => f81 ((69/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(60884722049852333/100000000000000),(1457646688814703/50000000000000),(32465398965203/100000000000000),(80490278089/50000000000000)⟩
def e82 : ℝ := (207231227/50000000000000)
theorem h82 : Model (fun x => f82 ((69/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(852721113/4000000000000),(2940417631/100000000000000),(152090567/100000000000000),(1748167/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((69/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(1287964181/50000000000000),(444125579/100000000000000),(612587/2000000000000),(132023/12500000000000)⟩
def e84 : ℝ := (9169/50000000000000)
theorem h84 : Model (fun x => f84 ((69/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(31125801/10000000000000),(503111/781250000000),(5551569/100000000000000),(63811/25000000000000)⟩
def e85 : ℝ := (837/12500000000000)
theorem h85 : Model (fun x => f85 ((69/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(18805171/50000000000000),(4539179/50000000000000),(46957/5000000000000),(53973/100000000000000)⟩
def e86 : ℝ := (1903/100000000000000)
theorem h86 : Model (fun x => f86 ((69/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(56415513/50000000000000),(13617537/50000000000000),(140871/5000000000000),(161919/100000000000000)⟩
def e87 : ℝ := (5709/100000000000000)
theorem h87 : Model (fun x => f87 ((69/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-56415513/50000000000000),(-13617537/50000000000000),(-140871/5000000000000),(-161919/100000000000000)⟩
def e88 : ℝ := (5709/100000000000000)
theorem h88 : Model (fun x => f88 ((69/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(60884721937021307/100000000000000),(728823337598583/25000000000000),(32465396147783/100000000000000),(160980394259/100000000000000)⟩
def e89 : ℝ := (414468163/100000000000000)
theorem h89 : Model (fun x => f89 ((69/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(659540364583317/2500000000000),(1225911458331/625000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1000000000000)
theorem h90 : Model (fun x => f90 ((69/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2023141051824069/100000000000000),(15898947362047/100000000000000),(23426739727/50000000000000),(3835419/6250000000000)⟩
def e91 : ℝ := (30307/100000000000000)
theorem h91 : Model (fun x => f91 ((69/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(13343431869235219/2500000000000),(816270589146371/10000000000000),(25460931123597/50000000000000),(83027793653/50000000000000)⟩
def e92 : ℝ := (299509797/100000000000000)
theorem h92 : Model (fun x => f92 ((69/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(18735809681/100000000000000),(-143267963/50000000000000),(2594621/100000000000000),(-18173/100000000000000)⟩
def e93 : ℝ := (27/20000000000000)
theorem h93 : Model (fun x => f93 ((69/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (525523480660600753/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(5703622813463/50000000000000),(371747211977/100000000000000),(-345490091/50000000000000),(1712189/100000000000000)⟩
def e94 : ℝ := (315491/100000000000000)
theorem h94 : Model (fun x => f94 ((69/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(24833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((69/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(44609665427509/100000000000000),(-165835187463/100000000000000),(123297537/20000000000000),(-35809/1562500000000)⟩
def e96 : ℝ := (1711/20000000000000)
theorem h96 : Model (fun x => f96 ((69/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (223333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(110780669144979/100000000000000),(13266814997/4000000000000),(-616487687/50000000000000),(4583551/100000000000000)⟩
def e97 : ℝ := (5959/10000000000000)
theorem h97 : Model (fun x => f97 ((69/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2326394052044559/100000000000000),(278603114937/4000000000000),(-12946241427/50000000000000),(96254571/100000000000000)⟩
def e98 : ℝ := (125139/10000000000000)
theorem h98 : Model (fun x => f98 ((69/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(10780669144979/100000000000000),(13266814997/4000000000000),(-616487687/50000000000000),(4583551/100000000000000)⟩
def e99 : ℝ := (5959/10000000000000)
theorem h99 : Model (fun x => f99 ((69/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(125400422879697/50000000000000),(8466841875873/100000000000000),(-4187074389/50000000000000),(-27373523/50000000000000)⟩
def e100 : ℝ := (2489663/100000000000000)
theorem h100 : Model (fun x => f100 ((69/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(122723566562093/100000000000000),(146970664279/20000000000000),(-407936091/25000000000000),(494137/25000000000000)⟩
def e101 : ℝ := (178147/100000000000000)
theorem h101 : Model (fun x => f101 ((69/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(110780669144979/10000000000000),(13266814997/400000000000),(-616487687/5000000000000),(4583551/10000000000000)⟩
def e102 : ℝ := (5959/1000000000000)
theorem h102 : Model (fun x => f102 ((69/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1230530258011883/100000000000000),(810311414129/20000000000000),(-1745187263/12500000000000),(23906029/50000000000000)⟩
def e103 : ℝ := (774047/100000000000000)
theorem h103 : Model (fun x => f103 ((69/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1330530258011883/100000000000000),(810311414129/20000000000000),(-1745187263/12500000000000),(23906029/50000000000000)⟩
def e104 : ℝ := (774047/100000000000000)
theorem h104 : Model (fun x => f104 ((69/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(3336981140178449/100000000000000),(122815232456113/100000000000000),(98301396007/50000000000000),(-133118397/6250000000000)⟩
def e105 : ℝ := (19118373/50000000000000)
theorem h105 : Model (fun x => f105 ((69/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(210780669144979/100000000000000),(13266814997/4000000000000),(-616487687/50000000000000),(4583551/100000000000000)⟩
def e106 : ℝ := (5959/10000000000000)
theorem h106 : Model (fun x => f106 ((69/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(444284904852051/100000000000000),(279638814249/20000000000000),(-512211889/12500000000000),(222873/2000000000000)⟩
def e107 : ℝ := (297327/100000000000000)
theorem h107 : Model (fun x => f107 ((69/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(468233347678643/50000000000000),(4420684228973/100000000000000),(-4738838563/50000000000000),(2604491/20000000000000)⟩
def e108 : ℝ := (522591/50000000000000)
theorem h108 : Model (fun x => f108 ((69/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(7812429252031251/25000000000000),(648820573882401/50000000000000),(1390824996619/20000000000000),(-22460036959/100000000000000)⟩
def e109 : ℝ := (492955063/100000000000000)
theorem h109 : Model (fun x => f109 ((69/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2577194897803953/12500000000000),(3086383949859/2500000000000),(-8566657911/3125000000000),(10376877/3125000000000)⟩
def e110 : ℝ := (3741087/12500000000000)
theorem h110 : Model (fun x => f110 ((69/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(222271084122819/10000000000000),(20422912381969/25000000000000),(3928188869/3125000000000),(-1450577651/100000000000000)⟩
def e111 : ℝ := (25842537/100000000000000)
theorem h111 : Model (fun x => f111 ((69/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(10407473381098881/50000000000000),(215818529582601/25000000000000),(915565257147/20000000000000),(-3870076357/25000000000000)⟩
def e112 : ℝ := (166396513/50000000000000)
theorem h112 : Model (fun x => f112 ((69/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(26032331885161383/50000000000000),(1080457633047603/50000000000000),(1153195126883/10000000000000),(-37940342387/100000000000000)⟩
def e113 : ℝ := (825748089/100000000000000)
theorem h113 : Model (fun x => f113 ((69/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(859064965934651/12500000000000),(1028794649953/2500000000000),(-2855552637/3125000000000),(3458959/3125000000000)⟩
def e114 : ℝ := (1247029/12500000000000)
theorem h114 : Model (fun x => f114 ((69/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(232445654427/20000000000000),(14302514309/20000000000000),(52137899/6250000000000),(-3595277/50000000000000)⟩
def e115 : ℝ := (58967/100000000000000)
theorem h115 : Model (fun x => f115 ((69/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(15661998091/12500000000000),(11564300603/100000000000000),(4887329/1562500000000),(290791/25000000000000)⟩
def e116 : ℝ := (19137/50000000000000)
theorem h116 : Model (fun x => f116 ((69/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(1076373908521/12500000000000),(169264075157/20000000000000),(5228182649/20000000000000),(99114227/50000000000000)⟩
def e117 : ℝ := (2866223/100000000000000)
theorem h117 : Model (fun x => f117 ((69/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(907515250753/5000000000000),(1812439858213/100000000000000),(2890040721/5000000000000),(247244347/50000000000000)⟩
def e118 : ℝ := (6431839/100000000000000)
theorem h118 : Model (fun x => f118 ((69/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(26041407037668913/50000000000000),(2162727705953419/100000000000000),(46359008333/400000000000),(-37445853693/100000000000000)⟩
def e119 : ℝ := (104022491/12500000000000)
theorem h119 : Model (fun x => f119 ((69/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(2701549113/20000000000000),(1662278649/100000000000000),(70531243/100000000000000),(1025983/100000000000000)⟩
def e120 : ℝ := (4869/100000000000000)
theorem h120 : Model (fun x => f120 ((69/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(728112679/50000000000000),(224005951/100000000000000),(6475239/50000000000000),(162331/50000000000000)⟩
def e121 : ℝ := (793/25000000000000)
theorem h121 : Model (fun x => f121 ((69/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(156990837/100000000000000),(3622401/12500000000000),(1060577/50000000000000),(37629/50000000000000)⟩
def e122 : ℝ := (1287/100000000000000)
theorem h122 : Model (fun x => f122 ((69/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(8462331/50000000000000),(911211/25000000000000),(161427/50000000000000),(7399/50000000000000)⟩
def e123 : ℝ := (371/100000000000000)
theorem h123 : Model (fun x => f123 ((69/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(25386993/50000000000000),(2733633/25000000000000),(484281/50000000000000),(22197/50000000000000)⟩
def e124 : ℝ := (1113/100000000000000)
theorem h124 : Model (fun x => f124 ((69/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-25386993/50000000000000),(-2733633/25000000000000),(-484281/50000000000000),(-22197/50000000000000)⟩
def e125 : ℝ := (1113/100000000000000)
theorem h125 : Model (fun x => f125 ((69/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(81379396913381/156250000000),(2162727695018887/100000000000000),(181089861167/1562500000000),(-37445898087/100000000000000)⟩
def e126 : ℝ := (832181041/100000000000000)
theorem h126 : Model (fun x => f126 ((69/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2577194897803953/10000000000000),(3086383949859/2000000000000),(-8566657911/2500000000000),(10376877/2500000000000)⟩
def e127 : ℝ := (3741087/10000000000000)
theorem h127 : Model (fun x => f127 ((69/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1973890766793959/100000000000000),(2484786079631/20000000000000),(-16861415049/100000000000000),(-15568349/100000000000000)⟩
def e128 : ℝ := (391309/12500000000000)
theorem h128 : Model (fun x => f128 ((69/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(254355060650186179/50000000000000),(1561995348495881/25000000000000),(8063135622989/100000000000000),(-16103040831/25000000000000)⟩
def e129 : ℝ := (328013603/20000000000000)
theorem h129 : Model (fun x => f129 ((69/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(9828780263/50000000000000),(-241434301/100000000000000),(1326861/50000000000000),(-13139/50000000000000)⟩
def e130 : ℝ := (161/50000000000000)
theorem h130 : Model (fun x => f130 ((69/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (251227005359267253/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(5119105345261/50000000000000),(299393727679/100000000000000),(-1561171059/100000000000000),(4181937/50000000000000)⟩
def e131 : ℝ := (128683/25000000000000)
theorem h131 : Model (fun x => f131 ((69/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(2705682039681/12500000000000),(83892617457/12500000000000),(-2252151241/100000000000000),(10076063/100000000000000)⟩
def e132 : ℝ := (830223/100000000000000)
theorem h132 : Model (fun x => f132 ((69/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-226031663208811/100000000000000),(-6962156398009/100000000000000),(24518465461/100000000000000),(-59690399/50000000000000)⟩
def e133 : ℝ := (25780427/100000000000000)
theorem h133 : Model (fun x => f133 ((69/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(57971014492753/100000000000000),(-84015963033/10000000000000),(6088113263/50000000000000),(-44116763/25000000000000)⟩
def e134 : ℝ := (2595107/100000000000000)
theorem h134 : Model (fun x => f134 ((69/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (17/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-131032848236991/100000000000000),(-427401181691/20000000000000),(45184703289/100000000000000),(-72405703/10000000000000)⟩
def e135 : ℝ := (37544377/100000000000000)
theorem h135 : Model (fun x => f135 ((69/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(22667121/256000),(328509/64000),(14283/128000),(69/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((69/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((69/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(2956581/32000),(128547/32000),(1863/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((69/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(46319769/256000),(585603/64000),(4347/25600),(87/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((69/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-4761/1600),(-69/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((69/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(45558009/256000),(580083/64000),(4331/25600),(87/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((69/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((69/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(207/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((69/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-207/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((69/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(42908409/256000),(570483/64000),(4331/25600),(87/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((69/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(43676409/256000),(570483/64000),(4331/25600),(87/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((69/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((69/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(43676409/4000),(570483/1000),(4331/400),(87/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((69/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((69/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(4284085869/512000),(62088201/128000),(2699487/256000),(13041/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((69/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(5975603847/50000000000000),(-138564727/20000000000000),(5020461/20000000000000),(-181901/25000000000000)⟩
def e151 : ℝ := (21433/100000000000000)
theorem h151 : Model (fun x => f151 ((69/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (2015140869/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(32624114705443/25000000000000),(-373525646443/50000000000000),(4126115273/50000000000000),(-86137049/100000000000000)⟩
def e152 : ℝ := (458981379/100000000000000)
theorem h152 : Model (fun x => f152 ((69/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(189/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((69/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(28161/1600),(169/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((69/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(327/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((69/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(611620795107/10000000000000),(-876749993/1562500000000),(257394493/50000000000000),(-944567/20000000000000)⟩
def e156 : ℝ := (43733/100000000000000)
theorem h156 : Model (fun x => f156 ((69/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (81/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(107649082568801/100000000000000),(76110666887/25000000000000),(25739449/2500000000000),(-377827/4000000000000)⟩
def e157 : ℝ := (291581/20000000000000)
theorem h157 : Model (fun x => f157 ((69/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(207649082568801/100000000000000),(76110666887/25000000000000),(25739449/2500000000000),(-377827/4000000000000)⟩
def e158 : ℝ := (291581/20000000000000)
theorem h158 : Model (fun x => f158 ((69/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(259561353211/250000000000),(76110666887/50000000000000),(25739449/5000000000000),(-2361419/50000000000000)⟩
def e159 : ℝ := (364477/50000000000000)
theorem h159 : Model (fun x => f159 ((69/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(9561353211/250000000000),(76110666887/50000000000000),(25739449/5000000000000),(-2361419/50000000000000)⟩
def e160 : ℝ := (364477/50000000000000)
theorem h160 : Model (fun x => f160 ((69/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((69/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((69/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(38316199759719/10000000000000),(22470768319/4000000000000),(1899816473/100000000000000),(-8714761/50000000000000)⟩
def e163 : ℝ := (269019/10000000000000)
theorem h163 : Model (fun x => f163 ((69/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(109555051332459/4000000000000),(22470768319/4000000000000),(1899816473/100000000000000),(-8714761/50000000000000)⟩
def e164 : ℝ := (2690191/100000000000000)
theorem h164 : Model (fun x => f164 ((69/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((69/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1421812868747681/50000000000000),(4752408312133/100000000000000),(16927041601/100000000000000),(-442703/312500000000)⟩
def e166 : ℝ := (22809911/100000000000000)
theorem h166 : Model (fun x => f166 ((69/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4063003344938157/50000000000000),(4752408312133/100000000000000),(16927041601/100000000000000),(-442703/312500000000)⟩
def e167 : ℝ := (2851239/12500000000000)
theorem h167 : Model (fun x => f167 ((69/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((69/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8436789170503739/100000000000000),(17303681895927/100000000000000),(66640389567/100000000000000),(-120157421/25000000000000)⟩
def e169 : ℝ := (83341237/100000000000000)
theorem h169 : Model (fun x => f169 ((69/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(6852918394775679/50000000000000),(17303681895927/100000000000000),(66640389567/100000000000000),(-120157421/25000000000000)⟩
def e170 : ℝ := (41670619/50000000000000)
theorem h170 : Model (fun x => f170 ((69/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((69/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(14230022175940233/100000000000000),(388286759197/1000000000000),(166085111561/100000000000000),(-14934339/1562500000000)⟩
def e172 : ℝ := (9395163/5000000000000)
theorem h172 : Model (fun x => f172 ((69/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(8282868230827259/50000000000000),(388286759197/1000000000000),(166085111561/100000000000000),(-14934339/1562500000000)⟩
def e173 : ℝ := (187903261/100000000000000)
theorem h173 : Model (fun x => f173 ((69/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((69/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(8599649945847699/50000000000000),(65530279651851/100000000000000),(39602652419/12500000000000),(-661011377/50000000000000)⟩
def e175 : ℝ := (79716033/25000000000000)
theorem h175 : Model (fun x => f175 ((69/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(352033616881527/2000000000000),(65530279651851/100000000000000),(39602652419/12500000000000),(-661011377/50000000000000)⟩
def e176 : ℝ := (318864133/100000000000000)
theorem h176 : Model (fun x => f176 ((69/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((69/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2284358049338297/12500000000000),(47415012799207/50000000000000),(20772030267/4000000000000),(-346067697/25000000000000)⟩
def e178 : ℝ := (92766517/20000000000000)
theorem h178 : Model (fun x => f178 ((69/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(570538917096479/3125000000000),(47415012799207/50000000000000),(20772030267/4000000000000),(-346067697/25000000000000)⟩
def e179 : ℝ := (231916293/50000000000000)
theorem h179 : Model (fun x => f179 ((69/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((69/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(236943765409761/1250000000000),(3156206536379/2500000000000),(388749722693/50000000000000),(-510405929/50000000000000)⟩
def e181 : ℝ := (77500843/12500000000000)
theorem h181 : Model (fun x => f181 ((69/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(18958834566114213/100000000000000),(3156206536379/2500000000000),(388749722693/50000000000000),(-510405929/50000000000000)⟩
def e182 : ℝ := (124001349/20000000000000)
theorem h182 : Model (fun x => f182 ((69/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(145017691004427/20000000000000),(6737561544947/20000000000000),(319510565811/100000000000000),(898995749/100000000000000)⟩
def e183 : ℝ := (167342509/100000000000000)
theorem h183 : Model (fun x => f183 ((69/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(2694883843229/2500000000000),(63217240611/20000000000000),(650333969/50000000000000),(-8239693/100000000000000)⟩
def e184 : ℝ := (1527673/100000000000000)
theorem h184 : Model (fun x => f184 ((69/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(509561353211/250000000000),(76110666887/50000000000000),(25739449/5000000000000),(-2361419/50000000000000)⟩
def e185 : ℝ := (364477/50000000000000)
theorem h185 : Model (fun x => f185 ((69/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(10386110907449/2500000000000),(620528870603/100000000000000),(1165122949/50000000000000),(-17685369/100000000000000)⟩
def e186 : ℝ := (2985581/100000000000000)
theorem h186 : Model (fun x => f186 ((69/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(423388858287939/50000000000000),(948592593033/50000000000000),(7832852511/100000000000000),(-9785269/20000000000000)⟩
def e187 : ℝ := (9167283/100000000000000)
theorem h187 : Model (fun x => f187 ((69/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(17259407965093/1000000000000),(5155905337087/100000000000000),(2901539333/12500000000000),(-59013033/50000000000000)⟩
def e188 : ℝ := (25010063/100000000000000)
theorem h188 : Model (fun x => f188 ((69/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1860483986753081/100000000000000),(11013287126717/100000000000000),(31883830341/50000000000000),(-129006707/100000000000000)⟩
def e189 : ℝ := (1349609/2500000000000)
theorem h189 : Model (fun x => f189 ((69/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((69/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(259561353211/31250000000),(76110666887/6250000000000),(25739449/625000000000),(-2361419/6250000000000)⟩
def e191 : ℝ := (364477/6250000000000)
theorem h191 : Model (fun x => f191 ((69/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(23459792100109/2500000000000),(1533856873247/100000000000000),(2709489889/50000000000000),(-46022397/100000000000000)⟩
def e192 : ℝ := (1471861/20000000000000)
theorem h192 : Model (fun x => f192 ((69/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(25959792100109/2500000000000),(1533856873247/100000000000000),(2709489889/50000000000000),(-46022397/100000000000000)⟩
def e193 : ℝ := (1471861/20000000000000)
theorem h193 : Model (fun x => f193 ((69/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(19319111000676771/100000000000000),(142898219165823/100000000000000),(116488174773/12500000000000),(-155230449/25000000000000)⟩
def e194 : ℝ := (351381099/50000000000000)
theorem h194 : Model (fun x => f194 ((69/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(129405540447/25000000000000),(-3828710603/100000000000000),(3351139/100000000000000),(22067/12500000000000)⟩
def e195 : ℝ := (5181/25000000000000)
theorem h195 : Model (fun x => f195 ((69/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (1917527955242877/10000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(46915231697/1250000000000),(29322804009/20000000000000),(388347553/100000000000000),(-5170767/100000000000000)⟩
def e196 : ℝ := (1066287/100000000000000)
theorem h196 : Model (fun x => f196 ((69/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(107649082568801/50000000000000),(76110666887/12500000000000),(25739449/1250000000000),(-377827/2000000000000)⟩
def e197 : ℝ := (291581/10000000000000)
theorem h197 : Model (fun x => f197 ((69/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(6019771359143/12500000000000),(-70606630299/100000000000000),(-4226921/3125000000000),(342381/12500000000000)⟩
def e198 : ℝ := (172851/50000000000000)
theorem h198 : Model (fun x => f198 ((69/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (207343599419713/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(10368365825371/10000000000000),(141213260597/100000000000000),(270522941/100000000000000),(-5478097/100000000000000)⟩
def e199 : ℝ := (1089991/50000000000000)
theorem h199 : Model (fun x => f199 ((69/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(368365825371/10000000000000),(141213260597/100000000000000),(270522941/100000000000000),(-5478097/100000000000000)⟩
def e200 : ℝ := (1089991/50000000000000)
theorem h200 : Model (fun x => f200 ((69/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(191321036063393/50000000000000),(130286044003/25000000000000),(124794809/12500000000000),(-20216787/100000000000000)⟩
def e201 : ℝ := (321807/4000000000000)
theorem h201 : Model (fun x => f201 ((69/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2738356357841071/100000000000000),(130286044003/25000000000000),(124794809/12500000000000),(-20216787/100000000000000)⟩
def e202 : ℝ := (1005647/12500000000000)
theorem h202 : Model (fun x => f202 ((69/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(709807011958169/25000000000000),(2203631823069/50000000000000),(9178941423/100000000000000),(-168151693/100000000000000)⟩
def e203 : ℝ := (17028621/25000000000000)
theorem h203 : Model (fun x => f203 ((69/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(2030402250053407/25000000000000),(2203631823069/50000000000000),(9178941423/100000000000000),(-168151693/100000000000000)⟩
def e204 : ℝ := (13622897/20000000000000)
theorem h204 : Model (fun x => f204 ((69/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8420781320484051/100000000000000),(8019200529671/50000000000000),(18855759239/50000000000000),(-118874181/20000000000000)⟩
def e205 : ℝ := (248320887/100000000000000)
theorem h205 : Model (fun x => f205 ((69/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(1368982893953167/10000000000000),(8019200529671/50000000000000),(18855759239/50000000000000),(-118874181/20000000000000)⟩
def e206 : ℝ := (31040111/12500000000000)
theorem h206 : Model (fun x => f206 ((69/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(3548528863295377/25000000000000),(35961054759391/100000000000000),(98783158889/100000000000000),(-317391597/25000000000000)⟩
def e207 : ℝ := (558225431/100000000000000)
theorem h207 : Model (fun x => f207 ((69/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16529829738895793/100000000000000),(35961054759391/100000000000000),(98783158889/100000000000000),(-317391597/25000000000000)⟩
def e208 : ℝ := (69778179/12500000000000)
theorem h208 : Model (fun x => f208 ((69/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(8569366088198419/50000000000000),(60628048666583/100000000000000),(197920752397/100000000000000),(-49626879/2500000000000)⟩
def e209 : ℝ := (944216293/100000000000000)
theorem h209 : Model (fun x => f209 ((69/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(1754111312877779/10000000000000),(60628048666583/100000000000000),(197920752397/100000000000000),(-49626879/2500000000000)⟩
def e210 : ℝ := (472108147/50000000000000)
theorem h210 : Model (fun x => f210 ((69/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(18187267790338621/100000000000000),(21907939144877/25000000000000),(338279056007/100000000000000),(-2575614609/100000000000000)⟩
def e211 : ℝ := (684829241/50000000000000)
theorem h211 : Model (fun x => f211 ((69/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(18169648742719573/100000000000000),(21907939144877/25000000000000),(338279056007/100000000000000),(-2575614609/100000000000000)⟩
def e212 : ℝ := (1369658483/100000000000000)
theorem h212 : Model (fun x => f212 ((69/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(18838956508300877/100000000000000),(29129441110559/25000000000000),(261820414653/50000000000000),(-1475541771/50000000000000)⟩
def e213 : ℝ := (1827611011/100000000000000)
theorem h213 : Model (fun x => f213 ((69/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(1884228984163421/10000000000000),(29129441110559/25000000000000),(261820414653/50000000000000),(-1475541771/50000000000000)⟩
def e214 : ℝ := (456902753/25000000000000)
theorem h214 : Model (fun x => f214 ((69/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(694085564939319/100000000000000),(30899928103423/100000000000000),(234800389603/100000000000000),(-3449967/4000000000000)⟩
def e215 : ℝ := (15387171/3125000000000)
theorem h215 : Model (fun x => f215 ((69/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(107503009888721/100000000000000),(73207537263/25000000000000),(190097003/25000000000000),(-2119151/20000000000000)⟩
def e216 : ℝ := (567689/12500000000000)
theorem h216 : Model (fun x => f216 ((69/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(20368365825371/10000000000000),(141213260597/100000000000000),(270522941/100000000000000),(-5478097/100000000000000)⟩
def e217 : ℝ := (1089991/50000000000000)
theorem h217 : Model (fun x => f217 ((69/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(414870326396141/100000000000000),(287628335123/50000000000000),(650716947/50000000000000),(-21551949/100000000000000)⟩
def e218 : ℝ := (2225369/25000000000000)
theorem h218 : Model (fun x => f218 ((69/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(845023057812767/100000000000000),(878777872729/50000000000000),(2292733137/50000000000000),(-63230799/100000000000000)⟩
def e219 : ℝ := (13629337/50000000000000)
theorem h219 : Model (fun x => f219 ((69/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(860586938620203/50000000000000),(477313845093/10000000000000),(14107728457/100000000000000),(-16385211/10000000000000)⟩
def e220 : ℝ := (14838679/20000000000000)
theorem h220 : Model (fun x => f220 ((69/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(462578430862959/25000000000000),(158927867673/1562500000000),(21115510493/50000000000000),(-280911263/100000000000000)⟩
def e221 : ℝ := (79621877/50000000000000)
theorem h221 : Model (fun x => f221 ((69/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(10368365825371/1250000000000),(141213260597/12500000000000),(270522941/12500000000000),(-5478097/12500000000000)⟩
def e222 : ℝ := (1089991/6250000000000)
theorem h222 : Model (fun x => f222 ((69/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(936972275918401/100000000000000),(355634058457/25000000000000),(146228577/5000000000000),(-54420531/100000000000000)⟩
def e223 : ℝ := (2747671/12500000000000)
theorem h223 : Model (fun x => f223 ((69/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1036972275918401/100000000000000),(355634058457/25000000000000),(146228577/5000000000000),(-54420531/100000000000000)⟩
def e224 : ℝ := (2747671/12500000000000)
theorem h224 : Model (fun x => f224 ((69/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(4796810082427253/25000000000000),(131795810450141/100000000000000),(63672934423/10000000000000),(-755425377/25000000000000)⟩
def e225 : ℝ := (2070880743/100000000000000)
theorem h225 : Model (fun x => f225 ((69/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(13029492293/2500000000000),(-3579946813/100000000000000),(3647517/50000000000000),(150769/100000000000000)⟩
def e226 : ℝ := (58893/100000000000000)
theorem h226 : Model (fun x => f226 ((69/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (1905480269733239/10000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(3617433007623/100000000000000),(136196255969/100000000000000),(168164733/100000000000000),(-5554617/100000000000000)⟩
def e227 : ℝ := (3078157/100000000000000)
theorem h227 : Model (fun x => f227 ((69/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(7370651543383/100000000000000),(141405138007/50000000000000),(278256143/50000000000000),(-1340673/12500000000000)⟩
def e228 : ℝ := (1036111/25000000000000)
theorem h228 : Model (fun x => f228 ((69/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(9618439256207/100000000000000),(313994847733/100000000000000),(-9728323/1250000000000),(-232877/20000000000000)⟩
def e229 : ℝ := (20344589/50000000000000)
theorem h229 : Model (fun x => f229 ((69/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(696988351899/12500000000000),(101215754987/100000000000000),(-1918063603/100000000000000),(27123017/100000000000000)⟩
def e230 : ℝ := (12416451/50000000000000)
theorem h230 : Model (fun x => f230 ((69/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-125456941421799/100000000000000),(-508947538367/25000000000000),(21633319843/50000000000000),(-696934013/100000000000000)⟩
def e231 : ℝ := (62377279/100000000000000)
theorem h231 : Model (fun x => f231 ((69/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((69/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-4761/320),(-69/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((69/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1449/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((69/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6831/320),(3/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((69/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((69/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15151/320),(3/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((69/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((69/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(378775/32),(375/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((69/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(11799/1600),(51/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((69/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(21399/1600),(51/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((69/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((69/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4044411/1600),(9639/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((69/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(39560766697/100000000000000),(-47142369/25000000000000),(2747551/100000000000000),(-21909/100000000000000)⟩
def e244 : ℝ := (119/50000000000000)
theorem h244 : Model (fun x => f244 ((69/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (251559/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(93653933785351/20000000000000),(-652419191393/50000000000000),(-1402228819/50000000000000),(-23807521/50000000000000)⟩
def e245 : ℝ := (2750019/50000000000000)
theorem h245 : Model (fun x => f245 ((69/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(621/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((69/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(54441/1600),(429/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((69/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(88041/1600),(429/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((69/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(22201/1600),(149/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((69/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1954598241/2560000),(11321169/640000),(182963/1280000),(289/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((69/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((69/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(106929/160),(981/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((69/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(74815999401/50000000000000),(-2745541263/100000000000000),(37782677/100000000000000),(-231087/50000000000000)⟩
def e253 : ℝ := (5443/100000000000000)
theorem h253 : Model (fun x => f253 ((69/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (52479/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(114246266271759/100000000000000),(34414220257/6250000000000),(1669236819/100000000000000),(-9405681/100000000000000)⟩
def e254 : ℝ := (4188153/50000000000000)
theorem h254 : Model (fun x => f254 ((69/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(214246266271759/100000000000000),(34414220257/6250000000000),(1669236819/100000000000000),(-9405681/100000000000000)⟩
def e255 : ℝ := (4188153/50000000000000)
theorem h255 : Model (fun x => f255 ((69/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(107123133135879/100000000000000),(34414220257/12500000000000),(834618409/100000000000000),(-4702841/100000000000000)⟩
def e256 : ℝ := (837631/20000000000000)
theorem h256 : Model (fun x => f256 ((69/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(7123133135879/100000000000000),(34414220257/12500000000000),(834618409/100000000000000),(-4702841/100000000000000)⟩
def e257 : ℝ := (837631/20000000000000)
theorem h257 : Model (fun x => f257 ((69/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(98833843071793/25000000000000),(508019441889/50000000000000),(1540069683/50000000000000),(-17355723/100000000000000)⟩
def e258 : ℝ := (483009/3125000000000)
theorem h258 : Model (fun x => f258 ((69/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2751049658001457/100000000000000),(508019441889/50000000000000),(1540069683/50000000000000),(-17355723/100000000000000)⟩
def e259 : ℝ := (15456289/100000000000000)
theorem h259 : Model (fun x => f259 ((69/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(736752646943761/25000000000000),(4331215497827/50000000000000),(5811520711/20000000000000),(-131009391/100000000000000)⟩
def e260 : ℝ := (65965501/50000000000000)
theorem h260 : Model (fun x => f260 ((69/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(2057347885038999/25000000000000),(4331215497827/50000000000000),(5811520711/20000000000000),(-131009391/100000000000000)⟩
def e261 : ℝ := (131931003/100000000000000)
theorem h261 : Model (fun x => f261 ((69/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(881558205583407/10000000000000),(31936114931799/100000000000000),(15457537093/12500000000000),(-375058739/100000000000000)⟩
def e262 : ℝ := (48724467/10000000000000)
theorem h262 : Model (fun x => f262 ((69/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(14084629674881689/100000000000000),(31936114931799/100000000000000),(15457537093/12500000000000),(-375058739/100000000000000)⟩
def e263 : ℝ := (487244671/100000000000000)
theorem h263 : Model (fun x => f263 ((69/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(15087896598319033/100000000000000),(7298789074639/10000000000000),(42243276987/12500000000000),(-228576951/50000000000000)⟩
def e264 : ℝ := (1116037537/100000000000000)
theorem h264 : Model (fun x => f264 ((69/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(8711805442016659/50000000000000),(7298789074639/10000000000000),(42243276987/12500000000000),(-228576951/50000000000000)⟩
def e265 : ℝ := (558018769/50000000000000)
theorem h265 : Model (fun x => f265 ((69/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(3732943576876103/20000000000000),(31539128497039/25000000000000),(708384946591/100000000000000),(230460513/100000000000000)⟩
def e266 : ℝ := (1933305529/100000000000000)
theorem h266 : Model (fun x => f266 ((69/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(19067098836761467/100000000000000),(31539128497039/25000000000000),(708384946591/100000000000000),(230460513/100000000000000)⟩
def e267 : ℝ := (193330553/10000000000000)
theorem h267 : Model (fun x => f267 ((69/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(10212636836026811/50000000000000),(187637157561539/100000000000000),(158163488893/12500000000000),(588346979/25000000000000)⟩
def e268 : ℝ := (2880874647/100000000000000)
theorem h268 : Model (fun x => f268 ((69/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(10203827312217287/50000000000000),(187637157561539/100000000000000),(158163488893/12500000000000),(588346979/25000000000000)⟩
def e269 : ℝ := (360109331/12500000000000)
theorem h269 : Model (fun x => f269 ((69/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(2732664879155427/12500000000000),(32148485475119/12500000000000),(2042354438071/100000000000000),(826363049/12500000000000)⟩
def e270 : ℝ := (3964910157/100000000000000)
theorem h270 : Model (fun x => f270 ((69/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(21864652366576749/100000000000000),(32148485475119/12500000000000),(2042354438071/100000000000000),(826363049/12500000000000)⟩
def e271 : ℝ := (1982455079/50000000000000)
theorem h271 : Model (fun x => f271 ((69/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(77872414888419/5000000000000),(3925811618169/5000000000000),(103603967789/10000000000000),(7212063947/100000000000000)⟩
def e272 : ℝ := (1243150633/100000000000000)
theorem h272 : Model (fun x => f272 ((69/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(14344207066059/12500000000000),(589849455737/100000000000000),(1273057727/50000000000000),(-5480023/100000000000000)⟩
def e273 : ℝ := (2253777/25000000000000)
theorem h273 : Model (fun x => f273 ((69/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(207123133135879/100000000000000),(34414220257/12500000000000),(834618409/100000000000000),(-4702841/100000000000000)⟩
def e274 : ℝ := (837631/20000000000000)
theorem h274 : Model (fun x => f274 ((69/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(42899992280023/10000000000000),(1140476979849/100000000000000),(263459517/6250000000000),(-2977141/20000000000000)⟩
def e275 : ℝ := (8695709/50000000000000)
theorem h275 : Model (fun x => f275 ((69/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(444279040627169/50000000000000),(708657496007/20000000000000),(15451372107/100000000000000),(-933839/3125000000000)⟩
def e276 : ℝ := (27072281/50000000000000)
theorem h276 : Model (fun x => f276 ((69/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(920204668813017/50000000000000),(9785290726213/100000000000000),(49174593403/100000000000000),(-15784541/50000000000000)⟩
def e277 : ℝ := (374449/250000000000)
theorem h277 : Model (fun x => f277 ((69/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(422387402003461/20000000000000),(2208462337159/10000000000000),(32201414933/20000000000000),(20105967/5000000000000)⟩
def e278 : ℝ := (2657027/781250000000)
theorem h278 : Model (fun x => f278 ((69/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(107123133135879/12500000000000),(34414220257/1562500000000),(834618409/12500000000000),(-4702841/12500000000000)⟩
def e279 : ℝ := (837631/2500000000000)
theorem h279 : Model (fun x => f279 ((69/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(60733670100969/6250000000000),(558471910437/20000000000000),(4611531363/50000000000000),(-43102751/100000000000000)⟩
def e280 : ℝ := (10630087/25000000000000)
theorem h280 : Model (fun x => f280 ((69/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(66983670100969/6250000000000),(558471910437/20000000000000),(4611531363/50000000000000),(-43102751/100000000000000)⟩
def e281 : ℝ := (10630087/25000000000000)
theorem h281 : Model (fun x => f281 ((69/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(22634446712484163/100000000000000),(2365298680253/800000000000),(2537042529173/100000000000000),(4966070409/50000000000000)⟩
def e282 : ℝ := (915711977/20000000000000)
theorem h282 : Model (fun x => f282 ((69/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(441804481771/100000000000000),(-5771068601/100000000000000),(12931857/50000000000000),(57577/50000000000000)⟩
def e283 : ℝ := (46837/50000000000000)
theorem h283 : Model (fun x => f283 ((69/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (11168116412111331/50000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(3440438190403/50000000000000),(257006823809/100000000000000),(44885807/10000000000000),(-2913331/50000000000000)⟩
def e284 : ℝ := (1789681/25000000000000)
theorem h284 : Model (fun x => f284 ((69/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(114246266271759/50000000000000),(34414220257/3125000000000),(1669236819/50000000000000),(-9405681/50000000000000)⟩
def e285 : ℝ := (4188153/25000000000000)
theorem h285 : Model (fun x => f285 ((69/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(291720369683/625000000000),(-119958601053/100000000000000),(-27677387/50000000000000),(312599/10000000000000)⟩
def e286 : ℝ := (1847197/100000000000000)
theorem h286 : Model (fun x => f286 ((69/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (213693951728841/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(106649481701439/100000000000000),(239917202103/100000000000000),(110709547/100000000000000),(-3125991/50000000000000)⟩
def e287 : ℝ := (3033951/25000000000000)
theorem h287 : Model (fun x => f287 ((69/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(6649481701439/100000000000000),(239917202103/100000000000000),(110709547/100000000000000),(-3125991/50000000000000)⟩
def e288 : ℝ := (3033951/25000000000000)
theorem h288 : Model (fun x => f288 ((69/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(196793686472893/50000000000000),(442704361023/50000000000000),(408570947/100000000000000),(-23072791/100000000000000)⟩
def e289 : ℝ := (22393449/50000000000000)
theorem h289 : Model (fun x => f289 ((69/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2749301658660071/100000000000000),(442704361023/50000000000000),(408570947/100000000000000),(-23072791/100000000000000)⟩
def e290 : ℝ := (44786899/100000000000000)
theorem h290 : Model (fun x => f290 ((69/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(2932115969370031/100000000000000),(754033142983/10000000000000),(2801863021/50000000000000),(-194532393/100000000000000)⟩
def e291 : ℝ := (190870091/50000000000000)
theorem h291 : Model (fun x => f291 ((69/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8214496921750983/100000000000000),(754033142983/10000000000000),(2801863021/50000000000000),(-194532393/100000000000000)⟩
def e292 : ℝ := (381740183/100000000000000)
theorem h292 : Model (fun x => f292 ((69/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(2190179597857021/25000000000000),(13874857784993/50000000000000),(6632225861/20000000000000),(-699244489/100000000000000)⟩
def e293 : ℝ := (1406783823/100000000000000)
theorem h293 : Model (fun x => f293 ((69/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14029766010475703/100000000000000),(13874857784993/50000000000000),(6632225861/20000000000000),(-699244489/100000000000000)⟩
def e294 : ℝ := (87923989/6250000000000)
theorem h294 : Model (fun x => f294 ((69/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(14962672734096993/100000000000000),(1976710934467/3125000000000),(7342175257/6250000000000),(-1512598231/100000000000000)⟩
def e295 : ℝ := (64261599/2000000000000)
theorem h295 : Model (fun x => f295 ((69/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(8649193509905639/50000000000000),(1976710934467/3125000000000),(7342175257/6250000000000),(-1512598231/100000000000000)⟩
def e296 : ℝ := (3213079951/100000000000000)
theorem h296 : Model (fun x => f296 ((69/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(36032500194019/195312500000),(108962669069911/100000000000000),(296196261787/100000000000000),(-2342798907/100000000000000)⟩
def e297 : ℝ := (5548897969/100000000000000)
theorem h297 : Model (fun x => f297 ((69/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(471275526292967/2500000000000),(108962669069911/100000000000000),(296196261787/100000000000000),(-2342798907/100000000000000)⟩
def e298 : ℝ := (554889797/10000000000000)
theorem h298 : Model (fun x => f298 ((69/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(20104516247087127/100000000000000),(32286992817249/20000000000000),(119636368999/20000000000000),(-1422943737/50000000000000)⟩
def e299 : ℝ := (8244299989/100000000000000)
theorem h299 : Model (fun x => f299 ((69/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(20086897199468079/100000000000000),(32286992817249/20000000000000),(119636368999/20000000000000),(-1422943737/50000000000000)⟩
def e300 : ℝ := (824429999/10000000000000)
theorem h300 : Model (fun x => f300 ((69/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(21422571753133571/100000000000000),(110180737116577/50000000000000),(523753099633/50000000000000),(-21416707/800000000000)⟩
def e301 : ℝ := (5642981667/50000000000000)
theorem h301 : Model (fun x => f301 ((69/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(2678238135808363/12500000000000),(110180737116577/50000000000000),(523753099633/50000000000000),(-21416707/800000000000)⟩
def e302 : ℝ := (2257192667/20000000000000)
theorem h302 : Model (fun x => f302 ((69/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(89044477380769/6250000000000),(1321146558297/2000000000000),(155514834749/25000000000000),(309888131/25000000000000)⟩
def e303 : ℝ := (136949369/4000000000000)
theorem h303 : Model (fun x => f303 ((69/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(22748223894371/20000000000000),(51174090511/10000000000000),(405872477/50000000000000),(-12804191/100000000000000)⟩
def e304 : ℝ := (259737/1000000000000)
theorem h304 : Model (fun x => f304 ((69/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(206649481701439/100000000000000),(239917202103/100000000000000),(110709547/100000000000000),(-3125991/50000000000000)⟩
def e305 : ℝ := (3033951/25000000000000)
theorem h305 : Model (fun x => f305 ((69/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(427040082874733/100000000000000),(247893827329/25000000000000),(64572753/6250000000000),(-5061631/20000000000000)⟩
def e306 : ℝ := (12561327/25000000000000)
theorem h306 : Model (fun x => f306 ((69/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(882476117918031/100000000000000),(384203482009/12500000000000),(498676203/10000000000000),(-37710567/50000000000000)⟩
def e307 : ℝ := (39004789/25000000000000)
theorem h307 : Model (fun x => f307 ((69/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(182363232381659/10000000000000),(8468848045339/100000000000000),(4664066289/25000000000000),(-48915683/25000000000000)⟩
def e308 : ℝ := (86124897/20000000000000)
theorem h308 : Model (fun x => f308 ((69/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2074219820159593/100000000000000),(4741208783229/25000000000000),(79361647847/100000000000000),(-291833161/100000000000000)⟩
def e309 : ℝ := (969812029/100000000000000)
theorem h309 : Model (fun x => f309 ((69/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(106649481701439/12500000000000),(239917202103/12500000000000),(110709547/12500000000000),(-3125991/6250000000000)⟩
def e310 : ℝ := (3033951/3125000000000)
theorem h310 : Model (fun x => f310 ((69/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(966936973083367/100000000000000),(1215539260967/50000000000000),(169742133/10000000000000),(-62820047/100000000000000)⟩
def e311 : ℝ := (30765033/25000000000000)
theorem h311 : Model (fun x => f311 ((69/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1066936973083367/100000000000000),(1215539260967/50000000000000),(169742133/10000000000000),(-62820047/100000000000000)⟩
def e312 : ℝ := (30765033/25000000000000)
theorem h312 : Model (fun x => f312 ((69/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(1106530908215301/5000000000000),(126384375231491/50000000000000),(671498523311/50000000000000),(-2165444629/100000000000000)⟩
def e313 : ℝ := (1296456839/10000000000000)
theorem h313 : Model (fun x => f313 ((69/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(451862660399/100000000000000),(-2580514453/50000000000000),(985197/3125000000000),(-2673/100000000000000)⟩
def e314 : ℝ := (68321/25000000000000)
theorem h314 : Model (fun x => f314 ((69/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (21876491286783397/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(3218869955449/50000000000000),(44991723967/20000000000000),(-37306247/25000000000000),(-1429059/25000000000000)⟩
def e315 : ℝ := (397097/2000000000000)
theorem h315 : Model (fun x => f315 ((69/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1664827036463/12500000000000),(120491360911/25000000000000),(149816541/50000000000000),(-5771449/50000000000000)⟩
def e316 : ℝ := (13506787/50000000000000)
theorem h316 : Model (fun x => f316 ((69/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(62367040414787/100000000000000),(1041555784931/50000000000000),(-1314823553/25000000000000),(-389099/500000000000)⟩
def e317 : ℝ := (31924037/25000000000000)
theorem h317 : Model (fun x => f317 ((69/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(36154806037557/100000000000000),(170904553467/25000000000000),(-12956376557/100000000000000),(28532129/20000000000000)⟩
def e318 : ℝ := (80450983/100000000000000)
theorem h318 : Model (fun x => f318 ((69/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-44651067692121/50000000000000),(-3380429849/250000000000),(30310263129/100000000000000),(-69284171/12500000000000)⟩
def e319 : ℝ := (71414131/50000000000000)
theorem h319 : Model (fun x => f319 ((69/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((69/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-52371/1600),(-759/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((69/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((69/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(6693/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((69/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(215349/1600),(1181/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((69/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((69/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(388149/1600),(1181/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((69/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1940745/32),(5905/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((69/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((69/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(97899602801365133/10000000000000),(4666460809261761/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (63499/50000000000000)
theorem h329 : Model (fun x => f329 ((69/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(5107273019/50000000000000),(-4868843/10000000000000),(354707/50000000000000),(-5657/100000000000000)⟩
def e330 : ℝ := (1/1562500000000)
theorem h330 : Model (fun x => f330 ((69/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (487141908794242747/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(619494660953697/100000000000000),(102117037611/12500000000000),(1499883019/20000000000000),(37719/1562500000000)⟩
def e331 : ℝ := (1805509/25000000000000)
theorem h331 : Model (fun x => f331 ((69/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((69/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(429/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((69/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((69/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((69/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(595806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((69/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((69/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((69/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1321645646299957/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (13/1250000000000)
theorem h339 : Model (fun x => f339 ((69/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3694193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((69/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((69/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((69/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2081708707399827/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1039/100000000000000)
theorem h343 : Model (fun x => f343 ((69/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(1200936514851/25000000000000),(-6501752371/100000000000000),(4399981/50000000000000),(-11911/100000000000000)⟩
def e344 : ℝ := (1/5000000000000)
theorem h344 : Model (fun x => f344 ((69/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2078891165764307/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(126977001306837/100000000000000),(893728715323/100000000000000),(-302409971/25000000000000),(327441/20000000000000)⟩
def e345 : ℝ := (807/25000000000000)
theorem h345 : Model (fun x => f345 ((69/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(226977001306837/100000000000000),(893728715323/100000000000000),(-302409971/25000000000000),(327441/20000000000000)⟩
def e346 : ℝ := (807/25000000000000)
theorem h346 : Model (fun x => f346 ((69/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(56744250326709/50000000000000),(446864357661/100000000000000),(-302409971/50000000000000),(409301/50000000000000)⟩
def e347 : ℝ := (101/6250000000000)
theorem h347 : Model (fun x => f347 ((69/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(6744250326709/50000000000000),(446864357661/100000000000000),(-302409971/50000000000000),(409301/50000000000000)⟩
def e348 : ℝ := (101/6250000000000)
theorem h348 : Model (fun x => f348 ((69/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(10470665238857/2500000000000),(5153569601/312500000000),(-558018399/25000000000000),(3021031/100000000000000)⟩
def e349 : ℝ := (2983/50000000000000)
theorem h349 : Model (fun x => f349 ((69/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(554908179053713/20000000000000),(5153569601/312500000000),(-558018399/25000000000000),(3021031/100000000000000)⟩
def e350 : ℝ := (5967/100000000000000)
theorem h350 : Model (fun x => f350 ((69/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(629756972411243/20000000000000),(14270021188181/100000000000000),(-11944694469/100000000000000),(6192287/100000000000000)⟩
def e351 : ℝ := (92199/100000000000000)
theorem h351 : Model (fun x => f351 ((69/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8431165814437167/100000000000000),(14270021188181/100000000000000),(-11944694469/100000000000000),(6192287/100000000000000)⟩
def e352 : ℝ := (461/500000000000)
theorem h352 : Model (fun x => f352 ((69/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(9568403670408279/100000000000000),(5387070804941/10000000000000),(-781588329/100000000000000),(-63639291/100000000000000)⟩
def e353 : ℝ := (229197/50000000000000)
theorem h353 : Model (fun x => f353 ((69/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(7418725644727949/50000000000000),(5387070804941/10000000000000),(-781588329/100000000000000),(-63639291/100000000000000)⟩
def e354 : ℝ := (91679/20000000000000)
theorem h354 : Model (fun x => f354 ((69/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(8419400501792367/50000000000000),(63720170127273/50000000000000),(150102116333/100000000000000),(-28007703/10000000000000)⟩
def e355 : ℝ := (184927/20000000000000)
theorem h355 : Model (fun x => f355 ((69/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(19174515289299019/100000000000000),(63720170127273/50000000000000),(150102116333/100000000000000),(-28007703/10000000000000)⟩
def e356 : ℝ := (231159/25000000000000)
theorem h356 : Model (fun x => f356 ((69/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(21760869909385851/100000000000000),(115157102982317/50000000000000),(623862806903/100000000000000),(-260923991/100000000000000)⟩
def e357 : ℝ := (1242263/50000000000000)
theorem h357 : Model (fun x => f357 ((69/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(22163250861766803/100000000000000),(115157102982317/50000000000000),(623862806903/100000000000000),(-260923991/100000000000000)⟩
def e358 : ℝ := (2484527/100000000000000)
theorem h358 : Model (fun x => f358 ((69/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(3144092637384361/12500000000000),(180209903870659/50000000000000),(801578440883/50000000000000),(1280144367/100000000000000)⟩
def e359 : ℝ := (6253217/100000000000000)
theorem h359 : Model (fun x => f359 ((69/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(157094512821599/625000000000),(180209903870659/50000000000000),(801578440883/50000000000000),(1280144367/100000000000000)⟩
def e360 : ℝ := (3126609/50000000000000)
theorem h360 : Model (fun x => f360 ((69/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(891421036050121/3125000000000),(5213549375661/1000000000000),(3277964136371/100000000000000),(6642619089/100000000000000)⟩
def e361 : ℝ := (267731/3125000000000)
theorem h361 : Model (fun x => f361 ((69/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(5705761297387441/20000000000000),(5213549375661/1000000000000),(3277964136371/100000000000000),(6642619089/100000000000000)⟩
def e362 : ℝ := (8567393/100000000000000)
theorem h362 : Model (fun x => f362 ((69/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(3848108249402881/100000000000000),(12363002001027/6250000000000),(1299674847997/50000000000000),(12624321851/100000000000000)⟩
def e363 : ℝ := (1580239/10000000000000)
theorem h363 : Model (fun x => f363 ((69/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(16099549725701/12500000000000),(1014279318927/100000000000000),(624075373/100000000000000),(-886853/25000000000000)⟩
def e364 : ℝ := (1467/10000000000000)
theorem h364 : Model (fun x => f364 ((69/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(106744250326709/50000000000000),(446864357661/100000000000000),(-302409971/50000000000000),(409301/50000000000000)⟩
def e365 : ℝ := (101/6250000000000)
theorem h365 : Model (fun x => f365 ((69/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(113943349778111/25000000000000),(1908008034249/100000000000000),(-585564511/100000000000000),(-29847/1562500000000)⟩
def e366 : ℝ := (8951/50000000000000)
theorem h366 : Model (fun x => f366 ((69/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(38920951845691/4000000000000),(3055033308499/50000000000000),(4519486543/100000000000000),(-14503797/100000000000000)⟩
def e367 : ℝ := (56329/100000000000000)
theorem h367 : Model (fun x => f367 ((69/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2077293913385113/100000000000000),(17392386146073/100000000000000),(31067252039/100000000000000),(-19878837/50000000000000)⟩
def e368 : ℝ := (44647/25000000000000)
theorem h368 : Model (fun x => f368 ((69/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(668869933068793/25000000000000),(21735164702689/50000000000000),(229384757009/100000000000000),(59750737/20000000000000)⟩
def e369 : ℝ := (683413/50000000000000)
theorem h369 : Model (fun x => f369 ((69/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(56744250326709/6250000000000),(446864357661/12500000000000),(-302409971/6250000000000),(409301/6250000000000)⟩
def e370 : ℝ := (101/781250000000)
theorem h370 : Model (fun x => f370 ((69/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(129588050379119/12500000000000),(917838836043/20000000000000),(-4214484163/100000000000000),(750351/25000000000000)⟩
def e371 : ℝ := (13799/50000000000000)
theorem h371 : Model (fun x => f371 ((69/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(142088050379119/12500000000000),(917838836043/20000000000000),(-4214484163/100000000000000),(750351/25000000000000)⟩
def e372 : ℝ := (13799/50000000000000)
theorem h372 : Model (fun x => f372 ((69/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(7603073979756529/25000000000000),(616912108530263/100000000000000),(2244803395199/50000000000000),(12171110017/100000000000000)⟩
def e373 : ℝ := (4340687/20000000000000)
theorem h373 : Model (fun x => f373 ((69/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(41101796567/12500000000000),(-6669985339/100000000000000),(86759233/100000000000000),(-453423/50000000000000)⟩
def e374 : ℝ := (4389/50000000000000)
theorem h374 : Model (fun x => f374 ((69/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (29790882010892003/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(632656649739/5000000000000),(98438245809/25000000000000),(-65407107/5000000000000),(37927/781250000000)⟩
def e375 : ℝ := (801823/100000000000000)
theorem h375 : Model (fun x => f375 ((69/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(126977001306837/50000000000000),(893728715323/50000000000000),(-302409971/12500000000000),(327441/10000000000000)⟩
def e376 : ℝ := (807/12500000000000)
theorem h376 : Model (fun x => f376 ((69/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(22028663570371/50000000000000),(-86738520113/50000000000000),(917867939/100000000000000),(-2428221/50000000000000)⟩
def e377 : ℝ := (26031/100000000000000)
theorem h377 : Model (fun x => f377 ((69/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (226082061311197/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(55942672859257/50000000000000),(346954080451/100000000000000),(-1835735879/100000000000000),(4856441/50000000000000)⟩
def e378 : ℝ := (11517/6250000000000)
theorem h378 : Model (fun x => f378 ((69/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(5942672859257/50000000000000),(346954080451/100000000000000),(-1835735879/100000000000000),(4856441/50000000000000)⟩
def e379 : ℝ := (11517/6250000000000)
theorem h379 : Model (fun x => f379 ((69/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(412910204437373/100000000000000),(320106443273/25000000000000),(-3387369777/50000000000000),(35845159/100000000000000)⟩
def e380 : ℝ := (340027/50000000000000)
theorem h380 : Model (fun x => f380 ((69/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1384312245075829/50000000000000),(320106443273/25000000000000),(-3387369777/50000000000000),(35845159/100000000000000)⟩
def e381 : ℝ := (136011/20000000000000)
theorem h381 : Model (fun x => f381 ((69/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(774421270613407/25000000000000),(11038464443839/100000000000000),(-26981042213/50000000000000),(262008239/100000000000000)⟩
def e382 : ℝ := (6241847/100000000000000)
theorem h382 : Model (fun x => f382 ((69/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(419003301741729/5000000000000),(11038464443839/100000000000000),(-26981042213/50000000000000),(262008239/100000000000000)⟩
def e383 : ℝ := (780231/12500000000000)
theorem h383 : Model (fun x => f383 ((69/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(9376065854514437/100000000000000),(41425405157351/100000000000000),(-43978285199/25000000000000),(717234043/100000000000000)⟩
def e384 : ℝ := (25449923/100000000000000)
theorem h384 : Model (fun x => f384 ((69/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(1830639184195257/12500000000000),(41425405157351/100000000000000),(-43978285199/25000000000000),(717234043/100000000000000)⟩
def e385 : ℝ := (6362481/25000000000000)
theorem h385 : Model (fun x => f385 ((69/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(819286792038179/5000000000000),(242901941397/250000000000),(-160969747381/50000000000000),(854143533/100000000000000)⟩
def e386 : ℝ := (16349677/25000000000000)
theorem h386 : Model (fun x => f386 ((69/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3744290025295573/20000000000000),(242901941397/250000000000),(-160969747381/50000000000000),(854143533/100000000000000)⟩
def e387 : ℝ := (65398709/100000000000000)
theorem h387 : Model (fun x => f387 ((69/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4189311839505787/20000000000000),(8683175294451/5000000000000),(-91694053723/25000000000000),(-25308729/20000000000000)⟩
def e388 : ℝ := (126435299/100000000000000)
theorem h388 : Model (fun x => f388 ((69/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(21348940149909887/100000000000000),(8683175294451/5000000000000),(-91694053723/25000000000000),(-25308729/20000000000000)⟩
def e389 : ℝ := (1264353/1000000000000)
theorem h389 : Model (fun x => f389 ((69/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(11943167746982659/50000000000000),(33546879116747/12500000000000),(-49936592557/25000000000000),(-63213369/2500000000000)⟩
def e390 : ℝ := (51189857/25000000000000)
theorem h390 : Model (fun x => f390 ((69/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(2386871644634627/10000000000000),(33546879116747/12500000000000),(-49936592557/25000000000000),(-63213369/2500000000000)⟩
def e391 : ℝ := (204759429/100000000000000)
theorem h391 : Model (fun x => f391 ((69/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(26705595914566333/100000000000000),(47885727385279/12500000000000),(67371154781/25000000000000),(-6130404547/100000000000000)⟩
def e392 : ℝ := (73819111/25000000000000)
theorem h392 : Model (fun x => f392 ((69/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(13354464623949833/50000000000000),(47885727385279/12500000000000),(67371154781/25000000000000),(-6130404547/100000000000000)⟩
def e393 : ℝ := (59055289/20000000000000)
theorem h393 : Model (fun x => f393 ((69/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(49600759044159/1562500000000),(69099396933441/50000000000000),(34834226499/4000000000000),(-211593447/5000000000000)⟩
def e394 : ℝ := (48589663/50000000000000)
theorem h394 : Model (fun x => f394 ((69/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(125183305865513/100000000000000),(388190772397/50000000000000),(-290406753/10000000000000),(4498131/50000000000000)⟩
def e395 : ℝ := (515089/100000000000000)
theorem h395 : Model (fun x => f395 ((69/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(105942672859257/50000000000000),(346954080451/100000000000000),(-1835735879/100000000000000),(4856441/50000000000000)⟩
def e396 : ℝ := (11517/6250000000000)
theorem h396 : Model (fun x => f396 ((69/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(448953997302541/100000000000000),(45946553303/3125000000000),(-821942411/12500000000000),(14211013/50000000000000)⟩
def e397 : ℝ := (883633/100000000000000)
theorem h397 : Model (fun x => f397 ((69/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(951267729301577/100000000000000),(2336496319483/50000000000000),(-8536491817/50000000000000),(27011871/50000000000000)⟩
def e398 : ℝ := (3068683/100000000000000)
theorem h398 : Model (fun x => f398 ((69/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(251949614617413/12500000000000),(13201848811299/100000000000000),(-3742477477/10000000000000),(3865293/6250000000000)⟩
def e399 : ℝ := (2307937/25000000000000)
theorem h399 : Model (fun x => f399 ((69/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1261595426773989/50000000000000),(2010952078619/6250000000000),(-90223379/3125000000000),(-83040409/20000000000000)⟩
def e400 : ℝ := (12419349/50000000000000)
theorem h400 : Model (fun x => f400 ((69/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(55942672859257/6250000000000),(346954080451/12500000000000),(-1835735879/12500000000000),(4856441/6250000000000)⟩
def e401 : ℝ := (11517/781250000000)
theorem h401 : Model (fun x => f401 ((69/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(8162128572909/800000000000),(1776007094201/50000000000000),(-8794977281/50000000000000),(43349659/50000000000000)⟩
def e402 : ℝ := (397853/20000000000000)
theorem h402 : Model (fun x => f402 ((69/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(8962128572909/800000000000),(1776007094201/50000000000000),(-8794977281/50000000000000),(43349659/50000000000000)⟩
def e403 : ℝ := (397853/20000000000000)
theorem h403 : Model (fun x => f403 ((69/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(28266451054356227/100000000000000),(450072318769327/100000000000000),(133339396981/20000000000000),(-8225939199/100000000000000)⟩
def e404 : ℝ := (343705653/100000000000000)
theorem h404 : Model (fun x => f404 ((69/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(176888141719/50000000000000),(-704124971/12500000000000),(16269433/20000000000000),(-211887/20000000000000)⟩
def e405 : ℝ := (18021/100000000000000)
theorem h405 : Model (fun x => f405 ((69/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (27815703468957143/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(11230446201821/100000000000000),(310097875617/100000000000000),(-1060766509/50000000000000),(2952587/20000000000000)⟩
def e406 : ℝ := (738263/50000000000000)
theorem h406 : Model (fun x => f406 ((69/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(23883579196601/100000000000000),(703850858853/100000000000000),(-1714837579/50000000000000),(19617591/100000000000000)⟩
def e407 : ℝ := (2278349/100000000000000)
theorem h407 : Model (fun x => f407 ((69/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(147957497967591/100000000000000),(4555432120079/100000000000000),(-13705512579/100000000000000),(73436459/50000000000000)⟩
def e408 : ℝ := (15990339/100000000000000)
theorem h408 : Model (fun x => f408 ((69/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(42886231294953/50000000000000),(174718880821/12500000000000),(-28202486229/100000000000000),(493875403/100000000000000)⟩
def e409 : ℝ := (3043533/12500000000000)
theorem h409 : Model (fun x => f409 ((69/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-110302274823/3125000000000),(5697388371/12500000000000),(21077769/1000000000000),(-12079593/20000000000000)⟩
def e410 : ℝ := (83588263/50000000000000)
theorem h410 : Model (fun x => f410 ((69/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(301601097290039/12500000000000),(40502208251953/25000000000000),(442773/10240000),(1173/2048000)⟩
def e411 : ℝ := (188476563/50000000000000)
theorem h411 : Model (fun x => f411 ((69/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(35721/1600),(189/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((69/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(6751269/64000),(107163/64000),(567/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((69/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(127261883656264019/50000000000000),(21130141236296211/100000000000000),(748774984769713/100000000000000),(3688755407501/25000000000000)⟩
def e414 : ℝ := (177716748691/100000000000000)
theorem h414 : Model (fun x => f414 ((69/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(39289061707/100000000000000),(-1630856387/50000000000000),(77599403/50000000000000),(-2783227/50000000000000)⟩
def e415 : ℝ := (50801/20000000000000)
theorem h415 : Model (fun x => f415 ((69/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (232629918353083419/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(680046045213/12500000000000),(20924864931/50000000000000),(-42364613/2000000000000),(12217921/25000000000000)⟩
def e416 : ℝ := (70338473/100000000000000)
theorem h416 : Model (fun x => f416 ((69/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(238836945921/12500000000000),(8742883683/10000000000000),(-8363/80000000000),(-11526281/100000000000000)⟩
def e417 : ℝ := (237514999/100000000000000)
theorem h417 : Model (fun x => f417 ((69/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((69/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((5731363703357/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (17/10) (7/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (17/10) (7/4) ≤ (5732788793351/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(69/40)-(1/40)) (by norm_num : ((69/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel14


noncomputable section
namespace Hf4Quad.Panel15
open Hf4Quad.Dag

def p0 : Cubic := ⟨(71/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((71/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((71/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((71/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((71/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(311047619047619/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((71/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-311047619047619/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((71/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-27452380952381/12500000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((71/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((71/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(5041/1600),(71/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((71/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(190704497354497/50000000000000),(2148783068783/20000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((71/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-190704497354497/50000000000000),(-2148783068783/20000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((71/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-300514021164021/50000000000000),(-15124867724867/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((71/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((71/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(357911/64000),(15123/64000),(213/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((71/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(2724203951099537/50000000000000),(230214418402777/100000000000000),(1621228298611/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((71/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-2724203951099537/50000000000000),(-230214418402777/100000000000000),(-1621228298611/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((71/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1512358986131779/25000000000000),(-61334821531911/25000000000000),(-3318117972883/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((71/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((71/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(25411681/2560000),(357911/640000),(15123/1280000),(71/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((71/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(346637513640873/12500000000000),(39057748015873/25000000000000),(206290922619/6250000000000),(7748015873/25000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((71/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-819083958850033/25000000000000),(-11138536758019/12500000000000),(-17463210979/100000000000000),(15769262567/100000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((71/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((71/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(1761942725585937/100000000000000),(31020118408203/25000000000000),(357911/10240000),(5041/10240000)⟩
def e22 : ℝ := (347656251/100000000000000)
theorem h22 : Model (fun x => f22 ((71/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(1434841321437807/12500000000000),(404180653926141/50000000000000),(22770741066261/100000000000000),(64142932581/20000000000000)⟩
def e23 : ℝ := (17694657/781250000000)
theorem h23 : Model (fun x => f23 ((71/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(2050598684025581/25000000000000),(71925301378813/10000000000000),(11376638927641/50000000000000),(10515122671/3125000000000)⟩
def e24 : ℝ := (148377693/6250000000000)
theorem h24 : Model (fun x => f24 ((71/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((71/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(1563724168957519/50000000000000),(264291408837889/100000000000000),(465301776123/5000000000000),(43690307617/25000000000000)⟩
def e26 : ℝ := (371298829/20000000000000)
theorem h26 : Model (fun x => f26 ((71/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(7022693516461069/100000000000000),(593467057729101/100000000000000),(835869095393/4000000000000),(392426805347/100000000000000)⟩
def e27 : ℝ := (1042190629/25000000000000)
theorem h27 : Model (fun x => f27 ((71/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(15225088252563393/100000000000000),(1312720071517231/100000000000000),(43650005240107/100000000000000),(728910730819/100000000000000)⟩
def e28 : ℝ := (1635701401/25000000000000)
theorem h28 : Model (fun x => f28 ((71/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((71/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(693902599974899/12500000000000),(68412932391891/12500000000000),(23125498273313/100000000000000),(271426036071/50000000000000)⟩
def e30 : ℝ := (308428809/4000000000000)
theorem h30 : Model (fun x => f30 ((71/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(263462701450787/20000000000000),(25975195917683/20000000000000),(5487717447397/100000000000000),(128819658389/100000000000000)⟩
def e31 : ℝ := (36595323/2000000000000)
theorem h31 : Model (fun x => f31 ((71/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(1033900109988583/6250000000000),(721298025552823/50000000000000),(3071107667969/6250000000000),(107216298651/12500000000000)⟩
def e32 : ℝ := (4186285877/50000000000000)
theorem h32 : Model (fun x => f32 ((71/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((71/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(2162589/320),(30459/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((71/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((71/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(156839/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((71/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(4672013/320),(48131/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((71/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((71/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(5401613/320),(48131/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((71/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-5401613/320),(-48131/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((71/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((71/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(111/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((71/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(12321/1600),(111/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((71/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((71/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(258741/160),(2331/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((71/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(2473515987/4000000000000),(-1114196391/100000000000000),(15056707/100000000000000),(-90431/50000000000000)⟩
def e46 : ℝ := (2093/100000000000000)
theorem h46 : Model (fun x => f46 ((71/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (127029/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-41753050347147/4000000000000),(205680661449/100000000000000),(-59002953/3125000000000),(3467533/20000000000000)⟩
def e47 : ℝ := (35213049/50000000000000)
theorem h47 : Model (fun x => f47 ((71/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((71/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(151/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((71/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((71/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((71/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(31458333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((71/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(56458333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((71/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((71/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(56458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((71/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((71/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1185624999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((71/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((71/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((71/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(61257291666663/20000000000000),(1376302083331/12500000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (41/50000000000000)
theorem h60 : Model (fun x => f60 ((71/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(127501736111109/100000000000000),(47048611111/5000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (9/100000000000000)
theorem h61 : Model (fun x => f61 ((71/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((71/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(56458333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((71/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1256668402777769/100000000000000),(63845486111/1250000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (39/100000000000000)
theorem h64 : Model (fun x => f64 ((71/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1356668402777769/100000000000000),(63845486111/1250000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (39/100000000000000)
theorem h65 : Model (fun x => f65 ((71/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(4155291602195181/100000000000000),(41254712546949/25000000000000),(265577121309/25000000000000),(1026656539/50000000000000)⟩
def e66 : ℝ := (3171/500000000000)
theorem h66 : Model (fun x => f66 ((71/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(106458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((71/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(453335069444441/100000000000000),(55447048611/3125000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (3/20000000000000)
theorem h68 : Model (fun x => f68 ((71/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(965225918692119/100000000000000),(1416672092011/25000000000000),(11089409721/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (49/100000000000000)
theorem h69 : Model (fun x => f69 ((71/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(20053975770812453/50000000000000),(457068034655057/25000000000000),(4013115627101/20000000000000),(49308511559/50000000000000)⟩
def e70 : ℝ := (126280003/50000000000000)
theorem h70 : Model (fun x => f70 ((71/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((71/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2677536458333289/12500000000000),(988020833331/625000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (189/12500000000000)
theorem h72 : Model (fun x => f72 ((71/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1383393836805461/50000000000000),(54835156249903/50000000000000),(696354166661/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (213/25000000000000)
theorem h73 : Model (fun x => f73 ((71/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(834554741902229/3125000000000),(243070303325551/20000000000000),(2648577233073/20000000000000),(63552330721/100000000000000)⟩
def e74 : ℝ := (154215811/100000000000000)
theorem h74 : Model (fun x => f74 ((71/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(33406851641248117/50000000000000),(3043623655247983/100000000000000),(3330846430087/10000000000000),(162169353839/100000000000000)⟩
def e75 : ℝ := (406775817/100000000000000)
theorem h75 : Model (fun x => f75 ((71/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((71/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(892512152777763/12500000000000),(329340277777/625000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (63/12500000000000)
theorem h77 : Model (fun x => f77 ((71/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(1668402777777/100000000000000),(13454861111/12500000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((71/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(107751012731/50000000000000),(10427517361/50000000000000),(134548611/20000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((71/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(3846763533461/25000000000000),(801313674981/50000000000000),(29616734363/50000000000000),(89127401/10000000000000)⟩
def e80 : ℝ := (4473117/100000000000000)
theorem h80 : Model (fun x => f80 ((71/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(4095200344997/12500000000000),(434546682273/12500000000000),(207493033/156250000000),(268059629/12500000000000)⟩
def e81 : ℝ := (2651259/20000000000000)
theorem h81 : Model (fun x => f81 ((71/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(6684646488525621/10000000000000),(3047100028706167/100000000000000),(3344125984199/10000000000000),(164313830871/100000000000000)⟩
def e82 : ℝ := (26252007/6250000000000)
theorem h82 : Model (fun x => f82 ((71/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(1739729893/6250000000000),(448962553/12500000000000),(34758391/20000000000000),(3737461/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((71/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(1797720889/50000000000000),(144977491/25000000000000),(7482709/20000000000000),(150861/12500000000000)⟩
def e84 : ℝ := (3919/20000000000000)
theorem h84 : Model (fun x => f84 ((71/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(464411229/100000000000000),(22471511/25000000000000),(3624437/50000000000000),(311779/100000000000000)⟩
def e85 : ℝ := (1911/25000000000000)
theorem h85 : Model (fun x => f85 ((71/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1199729/2000000000000),(13545327/100000000000000),(655419/50000000000000),(2819/4000000000000)⟩
def e86 : ℝ := (29/1250000000000)
theorem h86 : Model (fun x => f86 ((71/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(3599187/2000000000000),(40635981/100000000000000),(1966257/50000000000000),(8457/4000000000000)⟩
def e87 : ℝ := (87/1250000000000)
theorem h87 : Model (fun x => f87 ((71/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-3599187/2000000000000),(-40635981/100000000000000),(-1966257/50000000000000),(-8457/4000000000000)⟩
def e88 : ℝ := (87/1250000000000)
theorem h88 : Model (fun x => f88 ((71/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(3342323235264843/5000000000000),(1523549994035093/50000000000000),(8360313977369/25000000000000),(82156809723/50000000000000)⟩
def e89 : ℝ := (13126221/3125000000000)
theorem h89 : Model (fun x => f89 ((71/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2677536458333289/10000000000000),(988020833331/500000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (189/10000000000000)
theorem h90 : Model (fun x => f90 ((71/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2055126851881963/100000000000000),(16087098644837/100000000000000),(5902800383/12500000000000),(61607831/100000000000000)⟩
def e91 : ℝ := (30277/100000000000000)
theorem h91 : Model (fun x => f91 ((71/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(550267707241367301/100000000000000),(4184197801315087/50000000000000),(12981349445909/25000000000000),(658047023/390625000000)⟩
def e92 : ℝ := (302335131/100000000000000)
theorem h92 : Model (fun x => f92 ((71/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(18172972661/100000000000000),(-276372069/100000000000000),(622039/25000000000000),(-4331/25000000000000)⟩
def e93 : ℝ := (1/781250000000)
theorem h93 : Model (fun x => f93 ((71/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (67730902184822559/12500000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(6073994877869/50000000000000),(14760147609/4000000000000),(-340409333/50000000000000),(1674497/100000000000000)⟩
def e94 : ℝ := (12747/4000000000000)
theorem h94 : Model (fun x => f94 ((71/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(31458333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((71/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(11070110701107/25000000000000),(-163396467913/100000000000000),(120587799/20000000000000),(-556217/25000000000000)⟩
def e96 : ℝ := (2061/25000000000000)
theorem h96 : Model (fun x => f96 ((71/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (112499999999997/50000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(55719557195571/50000000000000),(13071717433/4000000000000),(-241175599/20000000000000),(1112433/25000000000000)⟩
def e97 : ℝ := (57973/100000000000000)
theorem h97 : Model (fun x => f97 ((71/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1170110701106991/50000000000000),(274506066093/4000000000000),(-5064687579/20000000000000),(23361093/25000000000000)⟩
def e98 : ℝ := (1217433/100000000000000)
theorem h98 : Model (fun x => f98 ((71/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(5719557195571/50000000000000),(13071717433/4000000000000),(-241175599/20000000000000),(1112433/25000000000000)⟩
def e99 : ℝ := (57973/100000000000000)
theorem h99 : Model (fun x => f99 ((71/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(66925150801311/25000000000000),(67461638383/800000000000),(-8690331143/100000000000000),(-6335953/12500000000000)⟩
def e100 : ℝ := (605579/25000000000000)
theorem h100 : Model (fun x => f100 ((71/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(6209338108141/5000000000000),(45521894197/6250000000000),(-202462911/12500000000000),(407207/20000000000000)⟩
def e101 : ℝ := (43331/25000000000000)
theorem h101 : Model (fun x => f101 ((71/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(55719557195571/5000000000000),(13071717433/400000000000),(-241175599/2000000000000),(1112433/2500000000000)⟩
def e102 : ℝ := (57973/10000000000000)
theorem h102 : Model (fun x => f102 ((71/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1935277978241/156250000000),(1998139832701/50000000000000),(-6839241619/50000000000000),(9306671/20000000000000)⟩
def e103 : ℝ := (376527/50000000000000)
theorem h103 : Model (fun x => f103 ((71/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(2091527978241/156250000000),(1998139832701/50000000000000),(-6839241619/50000000000000),(9306671/20000000000000)⟩
def e104 : ℝ := (376527/50000000000000)
theorem h104 : Model (fun x => f104 ((71/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(6998791267447/195312500000),(61788194039433/50000000000000),(92025116149/50000000000000),(-2054679313/100000000000000)⟩
def e105 : ℝ := (37691243/100000000000000)
theorem h105 : Model (fun x => f105 ((71/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(105719557195571/50000000000000),(13071717433/4000000000000),(-241175599/20000000000000),(1112433/25000000000000)⟩
def e106 : ℝ := (57973/100000000000000)
theorem h106 : Model (fun x => f106 ((71/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(27941561934069/6250000000000),(690968089401/50000000000000),(-2015729639/50000000000000),(10935499/100000000000000)⟩
def e107 : ℝ := (28927/10000000000000)
theorem h107 : Model (fun x => f107 ((71/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(945270257607167/100000000000000),(876586085373/20000000000000),(-4699535167/50000000000000),(13176127/100000000000000)⟩
def e108 : ℝ := (254679/25000000000000)
theorem h108 : Model (fun x => f108 ((71/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(8468159007127573/25000000000000),(662593971872633/50000000000000),(1363846941171/20000000000000),(-22498359587/100000000000000)⟩
def e109 : ℝ := (243497071/50000000000000)
theorem h109 : Model (fun x => f109 ((71/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(130396100270961/625000000000),(955959778137/781250000000),(-4251721131/1562500000000),(8551347/2500000000000)⟩
def e110 : ℝ := (909951/3125000000000)
theorem h110 : Model (fun x => f110 ((71/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(298323181431669/12500000000000),(5136079103203/6250000000000),(23431860557/20000000000000),(-1397291203/100000000000000)⟩
def e111 : ℝ := (5090563/20000000000000)
theorem h111 : Model (fun x => f111 ((71/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(22559682444968269/100000000000000),(11017495382887/1250000000000),(4484927578277/100000000000000),(-3870651723/25000000000000)⟩
def e112 : ℝ := (82110029/25000000000000)
theorem h112 : Model (fun x => f112 ((71/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(56432318473478561/100000000000000),(1103293787188113/50000000000000),(2826040571033/25000000000000),(-37980966479/100000000000000)⟩
def e113 : ℝ := (407717129/50000000000000)
theorem h113 : Model (fun x => f113 ((71/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(43465366756987/625000000000),(318653259379/781250000000),(-1417240377/1562500000000),(2850449/2500000000000)⟩
def e114 : ℝ := (303317/3125000000000)
theorem h114 : Model (fun x => f114 ((71/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(163566672567/12500000000000),(37382217751/50000000000000),(396026351/50000000000000),(-6863429/100000000000000)⟩
def e115 : ℝ := (28689/50000000000000)
theorem h115 : Model (fun x => f115 ((71/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(29936926049/20000000000000),(12828583951/100000000000000),(19946837/6250000000000),(191983/20000000000000)⟩
def e116 : ℝ := (4541/12500000000000)
theorem h116 : Model (fun x => f116 ((71/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(2602438940593/25000000000000),(953211364237/100000000000000),(13645908643/50000000000000),(185465031/100000000000000)⟩
def e117 : ℝ := (167141/6250000000000)
theorem h117 : Model (fun x => f117 ((71/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(68782173107/312500000000),(1024740006643/50000000000000),(30347537609/50000000000000),(47030199/10000000000000)⟩
def e118 : ℝ := (2995113/50000000000000)
theorem h118 : Model (fun x => f118 ((71/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(56454328768872801/100000000000000),(276079631798689/12500000000000),(227297147187/2000000000000),(-37510664489/100000000000000)⟩
def e119 : ℝ := (205356121/25000000000000)
theorem h119 : Model (fun x => f119 ((71/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(17122596079/100000000000000),(195663519/10000000000000),(19156439/25000000000000),(502363/50000000000000)⟩
def e120 : ℝ := (903/20000000000000)
theorem h120 : Model (fun x => f120 ((71/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(244834169/12500000000000),(69944293/25000000000000),(598119/4000000000000),(171253/50000000000000)⟩
def e121 : ℝ := (3/100000000000)
theorem h121 : Model (fun x => f121 ((71/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(44810977/20000000000000),(9601209/25000000000000),(65029/2500000000000),(42379/50000000000000)⟩
def e122 : ℝ := (41/3125000000000)
theorem h122 : Model (fun x => f122 ((71/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(12814947/50000000000000),(640671/12500000000000),(821/195312500000),(8871/50000000000000)⟩
def e123 : ℝ := (81/20000000000000)
theorem h123 : Model (fun x => f123 ((71/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(38444841/50000000000000),(1922013/12500000000000),(2463/195312500000),(26613/50000000000000)⟩
def e124 : ℝ := (243/20000000000000)
theorem h124 : Model (fun x => f124 ((71/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-38444841/50000000000000),(-1922013/12500000000000),(-2463/195312500000),(-26613/50000000000000)⟩
def e125 : ℝ := (243/20000000000000)
theorem h125 : Model (fun x => f125 ((71/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(56454328691983119/100000000000000),(69019907469169/3125000000000),(5682428049147/50000000000000),(-7502143543/20000000000000)⟩
def e126 : ℝ := (821425699/100000000000000)
theorem h126 : Model (fun x => f126 ((71/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(130396100270961/500000000000),(955959778137/625000000000),(-4251721131/1250000000000),(8551347/2000000000000)⟩
def e127 : ℝ := (909951/2500000000000)
theorem h127 : Model (fun x => f127 ((71/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(99933553064373/5000000000000),(6178152852629/50000000000000),(-2118626261/12500000000000),(-13646813/100000000000000)⟩
def e128 : ℝ := (1529931/50000000000000)
theorem h128 : Model (fun x => f128 ((71/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(32577364014538459/6250000000000),(6279466786350463/100000000000000),(3840503395467/50000000000000),(-62965885433/100000000000000)⟩
def e129 : ℝ := (812146889/50000000000000)
theorem h129 : Model (fun x => f129 ((71/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(9592550209/50000000000000),(-28890891/12500000000000),(1250863/50000000000000),(-763/3125000000000)⟩
def e130 : ℝ := (297/100000000000000)
theorem h130 : Model (fun x => f130 ((71/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (32184413240580921/6250000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(1353852456233/12500000000000),(146623982633/50000000000000),(-1512067683/100000000000000),(8006423/100000000000000)⟩
def e131 : ℝ := (101149/20000000000000)
theorem h131 : Model (fun x => f131 ((71/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(11489404702801/50000000000000),(662251655491/100000000000000),(-2192886349/100000000000000),(242023/2500000000000)⟩
def e132 : ℝ := (41221/5000000000000)
theorem h132 : Model (fun x => f132 ((71/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-239858846507399/100000000000000),(-6865493711371/100000000000000),(23818185483/100000000000000),(-114082277/100000000000000)⟩
def e133 : ℝ := (12717477/50000000000000)
theorem h133 : Model (fun x => f133 ((71/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(28169014084507/50000000000000),(-396746677247/50000000000000),(11175962739/100000000000000),(-78703963/50000000000000)⟩
def e134 : ℝ := (2248687/100000000000000)
theorem h134 : Model (fun x => f134 ((71/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (7/4))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-135131744511211/100000000000000),(-491154943463/25000000000000),(41089397087/100000000000000),(-80374451/12500000000000)⟩
def e135 : ℝ := (34507257/100000000000000)
theorem h135 : Model (fun x => f135 ((71/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(25411681/256000),(357911/64000),(15123/128000),(71/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((71/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((71/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(3221199/32000),(136107/32000),(1917/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((71/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(51181273/256000),(5041/512),(22791/128000),(89/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((71/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-5041/1600),(-71/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((71/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(50374713/256000),(124889/12800),(22711/128000),(89/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((71/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((71/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(213/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((71/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-213/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((71/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(47648313/256000),(122969/12800),(22711/128000),(89/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((71/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(48416313/256000),(122969/12800),(22711/128000),(89/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((71/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((71/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(48416313/4000),(122969/200),(22711/2000),(89/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((71/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((71/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(4802807709/512000),(67645179/128000),(2858247/256000),(13419/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((71/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(133255387/1250000000000),(-30029383/5000000000000),(5286863/25000000000000),(-595703/100000000000000)⟩
def e151 : ℝ := (17007/100000000000000)
theorem h151 : Model (fun x => f151 ((71/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (2263228317/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(64517345259281/50000000000000),(-44690459939/6250000000000),(7756617749/100000000000000),(-79225419/100000000000000)⟩
def e152 : ℝ := (403838883/100000000000000)
theorem h152 : Model (fun x => f152 ((71/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(191/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((71/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(28841/1600),(171/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((71/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(333/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((71/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3003003003003/50000000000000),(-54108162217/100000000000000),(12186523/2500000000000),(-219577/5000000000000)⟩
def e156 : ℝ := (1597/4000000000000)
theorem h156 : Model (fun x => f156 ((71/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (33/2))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(108262012012011/100000000000000),(15422517111/5000000000000),(38996873/4000000000000),(-8783083/100000000000000)⟩
def e157 : ℝ := (1365009/100000000000000)
theorem h157 : Model (fun x => f157 ((71/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(208262012012011/100000000000000),(15422517111/5000000000000),(38996873/4000000000000),(-8783083/100000000000000)⟩
def e158 : ℝ := (1365009/100000000000000)
theorem h158 : Model (fun x => f158 ((71/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(20826201201201/20000000000000),(15422517111/10000000000000),(30466307/6250000000000),(-2195771/50000000000000)⟩
def e159 : ℝ := (341253/50000000000000)
theorem h159 : Model (fun x => f159 ((71/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(826201201201/20000000000000),(15422517111/10000000000000),(30466307/6250000000000),(-2195771/50000000000000)⟩
def e160 : ℝ := (341253/50000000000000)
theorem h160 : Model (fun x => f160 ((71/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((71/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((71/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(192146499177747/50000000000000),(569164321953/100000000000000),(1798962889/100000000000000),(-8103441/50000000000000)⟩
def e163 : ℝ := (100751/4000000000000)
theorem h163 : Model (fun x => f163 ((71/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2740007284069779/100000000000000),(569164321953/100000000000000),(1798962889/100000000000000),(-8103441/50000000000000)⟩
def e164 : ℝ := (314847/12500000000000)
theorem h164 : Model (fun x => f164 ((71/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((71/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(713299287384919/25000000000000),(4818457456559/100000000000000),(16107537299/100000000000000),(-131656053/100000000000000)⟩
def e166 : ℝ := (21372717/100000000000000)
theorem h166 : Model (fun x => f166 ((71/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(2033894525480157/25000000000000),(4818457456559/100000000000000),(16107537299/100000000000000),(-131656053/100000000000000)⟩
def e167 : ℝ := (10686359/50000000000000)
theorem h167 : Model (fun x => f167 ((71/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((71/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(2117914830483549/25000000000000),(17564617471961/100000000000000),(63861978101/100000000000000),(-446042129/100000000000000)⟩
def e169 : ℝ := (7818499/10000000000000)
theorem h169 : Model (fun x => f169 ((71/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(2748141388196363/20000000000000),(17564617471961/100000000000000),(63861978101/100000000000000),(-446042129/100000000000000)⟩
def e170 : ℝ := (78184991/100000000000000)
theorem h170 : Model (fun x => f170 ((71/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((71/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(14308336369981319/100000000000000),(616903776033/1562500000000),(40142439243/25000000000000),(-27618287/3125000000000)⟩
def e172 : ℝ := (88295109/50000000000000)
theorem h172 : Model (fun x => f172 ((71/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(4161012663923901/25000000000000),(616903776033/1562500000000),(40142439243/25000000000000),(-27618287/3125000000000)⟩
def e173 : ℝ := (176590219/100000000000000)
theorem h173 : Model (fun x => f173 ((71/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((71/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(17331617387924903/100000000000000),(33391077260001/50000000000000),(309227082263/100000000000000),(-1211127351/100000000000000)⟩
def e175 : ℝ := (300351167/100000000000000)
theorem h175 : Model (fun x => f175 ((71/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(3546799668061171/20000000000000),(33391077260001/50000000000000),(309227082263/100000000000000),(-1211127351/100000000000000)⟩
def e176 : ℝ := (4692987/1562500000000)
theorem h176 : Model (fun x => f176 ((71/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((71/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(4616647719212179/25000000000000),(12111402327393/12500000000000),(255721236863/50000000000000),(-154689023/12500000000000)⟩
def e178 : ℝ := (43802971/10000000000000)
theorem h178 : Model (fun x => f178 ((71/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(4612242957307417/25000000000000),(12111402327393/12500000000000),(255721236863/50000000000000),(-154689023/12500000000000)⟩
def e179 : ℝ := (438029711/100000000000000)
theorem h179 : Model (fun x => f179 ((71/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((71/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(4802774990885329/25000000000000),(129346759051257/100000000000000),(24122886471/3125000000000),(-167549677/20000000000000)⟩
def e181 : ℝ := (587081621/100000000000000)
theorem h181 : Model (fun x => f181 ((71/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(19214433296874649/100000000000000),(129346759051257/100000000000000),(24122886471/3125000000000),(-167549677/20000000000000)⟩
def e182 : ℝ := (293540811/50000000000000)
theorem h182 : Model (fun x => f182 ((71/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(198437348378429/25000000000000),(34976815014901/100000000000000),(162518342351/50000000000000),(23565289/2500000000000)⟩
def e183 : ℝ := (160435921/100000000000000)
theorem h183 : Model (fun x => f183 ((71/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(54216332059113/50000000000000),(160596222191/50000000000000),(1253049937/100000000000000),(-7642339/100000000000000)⟩
def e184 : ℝ := (1434727/100000000000000)
theorem h184 : Model (fun x => f184 ((71/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(40826201201201/20000000000000),(15422517111/10000000000000),(30466307/6250000000000),(-2195771/50000000000000)⟩
def e185 : ℝ := (341253/50000000000000)
theorem h185 : Model (fun x => f185 ((71/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(104173669032559/25000000000000),(314821393301/50000000000000),(2227971761/100000000000000),(-16425423/100000000000000)⟩
def e186 : ℝ := (2799739/100000000000000)
theorem h186 : Model (fun x => f186 ((71/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(170120606871623/20000000000000),(1927944231803/100000000000000),(3775136251/50000000000000),(-11330837/25000000000000)⟩
def e187 : ℝ := (8610049/100000000000000)
theorem h187 : Model (fun x => f187 ((71/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(217043066394103/12500000000000),(5247375940819/100000000000000),(22532179813/100000000000000),(-108831201/100000000000000)⟩
def e188 : ℝ := (23526047/100000000000000)
theorem h188 : Model (fun x => f188 ((71/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1882764633400127/100000000000000),(11266876971431/100000000000000),(63043681959/100000000000000),(-56291003/50000000000000)⟩
def e189 : ℝ := (51044531/100000000000000)
theorem h189 : Model (fun x => f189 ((71/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((71/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(20826201201201/2500000000000),(15422517111/1250000000000),(30466307/781250000000),(-2195771/6250000000000)⟩
def e191 : ℝ := (341253/6250000000000)
theorem h191 : Model (fun x => f191 ((71/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(470740356083133/50000000000000),(777496906631/50000000000000),(5152737233/100000000000000),(-1710987/4000000000000)⟩
def e192 : ℝ := (275791/4000000000000)
theorem h192 : Model (fun x => f192 ((71/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(520740356083133/50000000000000),(777496906631/50000000000000),(5152737233/100000000000000),(-1710987/4000000000000)⟩
def e193 : ℝ := (275791/4000000000000)
theorem h193 : Model (fun x => f193 ((71/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(19608630512350229/100000000000000),(146619224088613/100000000000000),(92880094197/10000000000000),(-104247103/25000000000000)⟩
def e194 : ℝ := (333181631/50000000000000)
theorem h194 : Model (fun x => f194 ((71/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(127494880299/25000000000000),(-3813259761/100000000000000),(4356639/100000000000000),(158891/100000000000000)⟩
def e195 : ℝ := (19089/100000000000000)
theorem h195 : Model (fun x => f195 ((71/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (4865270350991993/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(4047959356537/100000000000000),(37026716879/25000000000000),(358444511/100000000000000),(-2401179/50000000000000)⟩
def e196 : ℝ := (508463/50000000000000)
theorem h196 : Model (fun x => f196 ((71/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(108262012012011/50000000000000),(15422517111/2500000000000),(38996873/2000000000000),(-8783083/50000000000000)⟩
def e197 : ℝ := (1365009/50000000000000)
theorem h197 : Model (fun x => f197 ((71/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(12004109514969/25000000000000),(-1111181911/1562500000000),(-119448713/100000000000000),(633707/25000000000000)⟩
def e198 : ℝ := (20117/6250000000000)
theorem h198 : Model (fun x => f198 ((71/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (103976288299937/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(20793424776049/20000000000000),(142231284607/100000000000000),(14931089/6250000000000),(-253483/5000000000000)⟩
def e199 : ℝ := (2037599/100000000000000)
theorem h199 : Model (fun x => f199 ((71/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(793424776049/20000000000000),(142231284607/100000000000000),(14931089/6250000000000),(-253483/5000000000000)⟩
def e200 : ℝ := (2037599/100000000000000)
theorem h200 : Model (fun x => f200 ((71/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(95922048818083/25000000000000),(262450584691/50000000000000),(176329051/20000000000000),(-935473/5000000000000)⟩
def e201 : ℝ := (3759857/50000000000000)
theorem h201 : Model (fun x => f201 ((71/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2739402480986617/100000000000000),(262450584691/50000000000000),(176329051/20000000000000),(-935473/5000000000000)⟩
def e202 : ℝ := (1503943/20000000000000)
theorem h202 : Model (fun x => f202 ((71/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2848077970985861/100000000000000),(4442011988283/100000000000000),(164151137/2000000000000),(-155822129/100000000000000)⟩
def e203 : ℝ := (1990897/3125000000000)
theorem h203 : Model (fun x => f203 ((71/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8130458923366813/100000000000000),(4442011988283/100000000000000),(164151137/2000000000000),(-155822129/100000000000000)⟩
def e204 : ℝ := (12741741/20000000000000)
theorem h204 : Model (fun x => f204 ((71/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(1056625537611151/12500000000000),(8091144138891/50000000000000),(17137274219/50000000000000),(-137976211/25000000000000)⟩
def e205 : ℝ := (116255861/50000000000000)
theorem h205 : Model (fun x => f205 ((71/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13722051919936827/100000000000000),(8091144138891/50000000000000),(17137274219/50000000000000),(-137976211/25000000000000)⟩
def e206 : ℝ := (232511723/100000000000000)
theorem h206 : Model (fun x => f206 ((71/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(7133211359256129/50000000000000),(7268262084117/20000000000000),(45716083643/50000000000000),(-118205277/10000000000000)⟩
def e207 : ℝ := (261762217/50000000000000)
theorem h207 : Model (fun x => f207 ((71/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(16602137004226543/100000000000000),(7268262084117/20000000000000),(45716083643/50000000000000),(-118205277/10000000000000)⟩
def e208 : ℝ := (104704887/20000000000000)
theorem h208 : Model (fun x => f208 ((71/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(8630382172976103/50000000000000),(61396447957999/100000000000000),(93205092457/50000000000000),(-1853754567/100000000000000)⟩
def e209 : ℝ := (887379279/100000000000000)
theorem h209 : Model (fun x => f209 ((71/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(8831572649166579/50000000000000),(61396447957999/100000000000000),(93205092457/50000000000000),(-1853754567/100000000000000)⟩
def e210 : ℝ := (11092241/1250000000000)
theorem h210 : Model (fun x => f210 ((71/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2295483019183213/12500000000000),(88954639566383/100000000000000),(323327063623/100000000000000),(-1205474293/50000000000000)⟩
def e211 : ℝ := (1290323807/100000000000000)
theorem h211 : Model (fun x => f211 ((71/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(143330039889427/781250000000),(88954639566383/100000000000000),(323327063623/100000000000000),(-1205474293/50000000000000)⟩
def e212 : ℝ := (40322619/3125000000000)
theorem h212 : Model (fun x => f212 ((71/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(9537031688284489/50000000000000),(118577680406401/100000000000000),(253251941153/50000000000000),(-110572143/4000000000000)⟩
def e213 : ℝ := (172618173/10000000000000)
theorem h213 : Model (fun x => f213 ((71/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(19077396709902311/100000000000000),(118577680406401/100000000000000),(253251941153/50000000000000),(-110572143/4000000000000)⟩
def e214 : ℝ := (1726181731/100000000000000)
theorem h214 : Model (fun x => f214 ((71/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(94602995075951/12500000000000),(3183814988611/10000000000000),(117161801937/50000000000000),(-14627299/20000000000000)⟩
def e215 : ℝ := (470852133/100000000000000)
theorem h215 : Model (fun x => f215 ((71/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(54045814239651/50000000000000),(295747551727/100000000000000),(21845217/3125000000000),(-4930993/50000000000000)⟩
def e216 : ℝ := (85131/2000000000000)
theorem h216 : Model (fun x => f216 ((71/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(40793424776049/20000000000000),(142231284607/100000000000000),(14931089/6250000000000),(-253483/5000000000000)⟩
def e217 : ℝ := (2037599/100000000000000)
theorem h217 : Model (fun x => f217 ((71/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(26001617264987/6250000000000),(580210120941/100000000000000),(18388153/1562500000000),(-10000653/50000000000000)⟩
def e218 : ℝ := (2082937/25000000000000)
theorem h218 : Model (fun x => f218 ((71/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(848556014363891/100000000000000),(887578422109/50000000000000),(843897153/20000000000000),(-29413621/50000000000000)⟩
def e219 : ℝ := (12774923/50000000000000)
theorem h219 : Model (fun x => f219 ((71/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1730775297010867/100000000000000),(2413824239677/50000000000000),(65791853/500000000000),(-76382453/50000000000000)⟩
def e220 : ℝ := (69640059/100000000000000)
theorem h220 : Model (fun x => f220 ((71/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(935411601928261/50000000000000),(2067401885079/20000000000000),(40599681067/100000000000000),(-52630361/20000000000000)⟩
def e221 : ℝ := (37549301/25000000000000)
theorem h221 : Model (fun x => f221 ((71/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(20793424776049/2500000000000),(142231284607/12500000000000),(14931089/781250000000),(-253483/625000000000)⟩
def e222 : ℝ := (2037599/12500000000000)
theorem h222 : Model (fun x => f222 ((71/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(469914309760631/50000000000000),(1433597828583/100000000000000),(81569573/3125000000000),(-25209633/50000000000000)⟩
def e223 : ℝ := (10278671/50000000000000)
theorem h223 : Model (fun x => f223 ((71/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(519914309760631/50000000000000),(1433597828583/100000000000000),(81569573/3125000000000),(-25209633/50000000000000)⟩
def e224 : ℝ := (10278671/50000000000000)
theorem h224 : Model (fun x => f224 ((71/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(19453355094344717/100000000000000),(134307263234981/100000000000000),(309595482899/50000000000000),(-2827727621/100000000000000)⟩
def e225 : ℝ := (1958627817/100000000000000)
theorem h225 : Model (fun x => f225 ((71/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(803203351/156250000000),(-1774518271/50000000000000),(1628163/20000000000000),(131481/100000000000000)⟩
def e226 : ℝ := (54179/100000000000000)
theorem h226 : Model (fun x => f226 ((71/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (38636847707577/200000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(3890454664173/100000000000000),(136804096619/100000000000000),(136204889/100000000000000),(-638153/12500000000000)⟩
def e227 : ℝ := (2928419/100000000000000)
theorem h227 : Model (fun x => f227 ((71/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(793841402071/10000000000000),(56982192827/20000000000000),(2473247/500000000000),(-4953791/50000000000000)⟩
def e228 : ℝ := (789069/20000000000000)
theorem h228 : Model (fun x => f228 ((71/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(2048661592741/20000000000000),(310870561021/100000000000000),(-195806643/25000000000000),(-510983/100000000000000)⟩
def e229 : ℝ := (19224051/50000000000000)
theorem h229 : Model (fun x => f229 ((71/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(577087772603/10000000000000),(11732297033/12500000000000),(-1763203369/100000000000000),(6136493/25000000000000)⟩
def e230 : ℝ := (11390843/50000000000000)
theorem h230 : Model (fun x => f230 ((71/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-129360866785181/100000000000000),(-467690349397/25000000000000),(19663096859/50000000000000),(-154612409/25000000000000)⟩
def e231 : ℝ := (57288943/100000000000000)
theorem h231 : Model (fun x => f231 ((71/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((71/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-5041/320),(-71/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((71/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1491/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((71/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6887/320),(13/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((71/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((71/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15207/320),(13/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((71/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((71/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(380175/32),(325/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((71/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(11999/1600),(49/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((71/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(21599/1600),(49/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((71/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((71/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4082211/1600),(9261/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((71/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(19597223171/50000000000000),(-22229361/12500000000000),(1310761/50000000000000),(-629/3125000000000)⟩
def e244 : ℝ := (217/100000000000000)
theorem h244 : Model (fun x => f244 ((71/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (40635/16))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(232824197469841/50000000000000),(-658312319111/50000000000000),(-3088022169/100000000000000),(-5868363/12500000000000)⟩
def e245 : ℝ := (5055281/100000000000000)
theorem h245 : Model (fun x => f245 ((71/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(639/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((71/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(56161/1600),(431/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((71/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(89761/1600),(431/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((71/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(22801/1600),(151/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((71/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(2046640561/2560000),(11690571/640000),(186443/1280000),(291/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((71/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((71/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(110889/160),(999/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((71/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(2254506759/1562500000000),(-1299895789/50000000000000),(17566159/50000000000000),(-42201/10000000000000)⟩
def e253 : ℝ := (4877/100000000000000)
theorem h253 : Model (fun x => f253 ((71/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (54441/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(115354124450451/100000000000000),(278597220381/50000000000000),(807455347/50000000000000),(-1089331/12500000000000)⟩
def e254 : ℝ := (245791/3125000000000)
theorem h254 : Model (fun x => f254 ((71/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(215354124450451/100000000000000),(278597220381/50000000000000),(807455347/50000000000000),(-1089331/12500000000000)⟩
def e255 : ℝ := (245791/3125000000000)
theorem h255 : Model (fun x => f255 ((71/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(4307082489009/4000000000000),(278597220381/100000000000000),(807455347/100000000000000),(-1089331/25000000000000)⟩
def e256 : ℝ := (3932657/100000000000000)
theorem h256 : Model (fun x => f256 ((71/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(307082489009/4000000000000),(278597220381/100000000000000),(807455347/100000000000000),(-1089331/25000000000000)⟩
def e257 : ℝ := (3932657/100000000000000)
theorem h257 : Model (fun x => f257 ((71/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(49672454300327/12500000000000),(257039102137/25000000000000),(744973683/25000000000000),(-16080601/100000000000000)⟩
def e258 : ℝ := (725669/5000000000000)
theorem h258 : Model (fun x => f258 ((71/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2753093920116901/100000000000000),(257039102137/25000000000000),(744973683/25000000000000),(-16080601/100000000000000)⟩
def e259 : ℝ := (14513381/100000000000000)
theorem h259 : Model (fun x => f259 ((71/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2964450653483161/100000000000000),(548570734483/6250000000000),(14151541173/50000000000000),(-60336267/50000000000000)⟩
def e260 : ℝ := (124044229/100000000000000)
theorem h260 : Model (fun x => f260 ((71/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8246831605864113/100000000000000),(548570734483/6250000000000),(14151541173/50000000000000),(-60336267/50000000000000)⟩
def e261 : ℝ := (12404423/10000000000000)
theorem h261 : Model (fun x => f261 ((71/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8879945999855823/100000000000000),(32426401241337/100000000000000),(60759127719/50000000000000),(-42444349/12500000000000)⟩
def e262 : ℝ := (459071989/100000000000000)
theorem h262 : Model (fun x => f262 ((71/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7074496809451721/50000000000000),(32426401241337/100000000000000),(60759127719/50000000000000),(-42444349/12500000000000)⟩
def e263 : ℝ := (45907199/10000000000000)
theorem h263 : Model (fun x => f263 ((71/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(15235220663269773/100000000000000),(14866899835237/20000000000000),(335433145573/100000000000000),(-381764927/100000000000000)⟩
def e264 : ℝ := (10546951/1000000000000)
theorem h264 : Model (fun x => f264 ((71/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(8785467474492029/50000000000000),(14866899835237/20000000000000),(335433145573/100000000000000),(-381764927/100000000000000)⟩
def e265 : ℝ := (1054695101/100000000000000)
theorem h265 : Model (fun x => f265 ((71/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(1891986655857137/10000000000000),(128993341295573/100000000000000),(142031171827/20000000000000),(89507371/25000000000000)⟩
def e266 : ℝ := (458541153/25000000000000)
theorem h266 : Model (fun x => f266 ((71/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(9661123755476161/50000000000000),(128993341295573/100000000000000),(142031171827/20000000000000),(89507371/25000000000000)⟩
def e267 : ℝ := (1834164613/100000000000000)
theorem h267 : Model (fun x => f267 ((71/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(520140711892003/2500000000000),(192727484853881/100000000000000),(25601307007/2000000000000),(2563620817/100000000000000)⟩
def e268 : ℝ := (2746217057/100000000000000)
theorem h268 : Model (fun x => f268 ((71/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(1299250589253817/6250000000000),(192727484853881/100000000000000),(25601307007/2000000000000),(2563620817/100000000000000)⟩
def e269 : ℝ := (1373108529/50000000000000)
theorem h269 : Model (fun x => f269 ((71/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(279798973090487/1250000000000),(132719055115171/50000000000000),(1041562036597/50000000000000),(279081821/4000000000000)⟩
def e270 : ℝ := (3798985559/100000000000000)
theorem h270 : Model (fun x => f270 ((71/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(22387251180572293/100000000000000),(132719055115171/50000000000000),(1041562036597/50000000000000),(279081821/4000000000000)⟩
def e271 : ℝ := (94974639/2500000000000)
theorem h271 : Model (fun x => f271 ((71/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1718683203649953/100000000000000),(82748108400631/100000000000000),(216038596993/20000000000000),(1876741759/25000000000000)⟩
def e272 : ℝ := (1217927003/100000000000000)
theorem h272 : Model (fun x => f272 ((71/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(115943497294549/100000000000000),(299985302347/50000000000000),(314381563/12500000000000),(-4884581/100000000000000)⟩
def e273 : ℝ := (2127237/25000000000000)
theorem h273 : Model (fun x => f273 ((71/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(8307082489009/4000000000000),(278597220381/100000000000000),(807455347/100000000000000),(-1089331/25000000000000)⟩
def e274 : ℝ := (3932657/100000000000000)
theorem h274 : Model (fun x => f274 ((71/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(431297621744999/100000000000000),(72322815341/6250000000000),(2064981599/50000000000000),(-13599229/100000000000000)⟩
def e275 : ℝ := (8187131/50000000000000)
theorem h275 : Model (fun x => f275 ((71/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(895706230287277/100000000000000),(3604749557251/100000000000000),(38208379/250000000000),(-26185961/100000000000000)⟩
def e276 : ℝ := (25556859/50000000000000)
theorem h276 : Model (fun x => f276 ((71/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(74407055409157/4000000000000),(1996330128287/20000000000000),(4901517553/10000000000000),(-10862661/50000000000000)⟩
def e277 : ℝ := (141769203/100000000000000)
theorem h277 : Model (fun x => f277 ((71/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1078376778440869/50000000000000),(5683396587059/25000000000000),(163501291181/100000000000000),(429069479/100000000000000)⟩
def e278 : ℝ := (324979071/100000000000000)
theorem h278 : Model (fun x => f278 ((71/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(4307082489009/500000000000),(278597220381/12500000000000),(807455347/12500000000000),(-1089331/3125000000000)⟩
def e279 : ℝ := (3932657/12500000000000)
theorem h279 : Model (fun x => f279 ((71/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(977359995096349/100000000000000),(1414374183871/50000000000000),(112183691/1250000000000),(-39743173/100000000000000)⟩
def e280 : ℝ := (9992551/25000000000000)
theorem h280 : Model (fun x => f280 ((71/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1077359995096349/100000000000000),(1414374183871/50000000000000),(112183691/1250000000000),(-39743173/100000000000000)⟩
def e281 : ℝ := (9992551/25000000000000)
theorem h281 : Model (fun x => f281 ((71/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(929440000586457/4000000000000),(305931695803089/100000000000000),(103925420603/4000000000000),(10430770827/100000000000000)⟩
def e282 : ℝ := (274964399/6250000000000)
theorem h282 : Model (fun x => f282 ((71/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(430366672133/100000000000000),(-5666328359/100000000000000),(26482979/100000000000000),(11463/12500000000000)⟩
def e283 : ℝ := (17069/20000000000000)
theorem h283 : Model (fun x => f283 ((71/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (458549107062841/2000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(7396639708057/100000000000000),(258734046607/100000000000000),(415169581/100000000000000),(-1352383/25000000000000)⟩
def e284 : ℝ := (6915653/100000000000000)
theorem h284 : Model (fun x => f284 ((71/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(115354124450451/50000000000000),(278597220381/25000000000000),(807455347/25000000000000),(-1089331/6250000000000)⟩
def e285 : ℝ := (245791/1562500000000)
theorem h285 : Model (fun x => f285 ((71/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(23217572511133/50000000000000),(-30035882443/25000000000000),(-37358493/100000000000000),(287667/10000000000000)⟩
def e286 : ℝ := (53651/3125000000000)
theorem h286 : Model (fun x => f286 ((71/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (42959059703807/20000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(13391213744433/12500000000000),(120143529771/50000000000000),(37358491/50000000000000),(-1150669/20000000000000)⟩
def e287 : ℝ := (11355399/100000000000000)
theorem h287 : Model (fun x => f287 ((71/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(891213744433/12500000000000),(120143529771/50000000000000),(37358491/50000000000000),(-1150669/20000000000000)⟩
def e288 : ℝ := (11355399/100000000000000)
theorem h288 : Model (fun x => f288 ((71/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(19767982194163/5000000000000),(886773672119/100000000000000),(275741243/100000000000000),(-21232583/100000000000000)⟩
def e289 : ℝ := (41906831/100000000000000)
theorem h289 : Model (fun x => f289 ((71/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(550214785919509/20000000000000),(886773672119/100000000000000),(275741243/100000000000000),(-21232583/100000000000000)⟩
def e290 : ℝ := (2619177/6250000000000)
theorem h290 : Model (fun x => f290 ((71/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(589443504287647/20000000000000),(3780236357079/50000000000000),(1120430647/25000000000000),(-89850019/50000000000000)⟩
def e291 : ℝ := (178796711/50000000000000)
theorem h291 : Model (fun x => f291 ((71/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(8229598473819187/100000000000000),(3780236357079/50000000000000),(1120430647/25000000000000),(-89850019/50000000000000)⟩
def e292 : ℝ := (357593423/100000000000000)
theorem h292 : Model (fun x => f292 ((71/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4408172487750893/50000000000000),(3484271584349/12500000000000),(3639625199/12500000000000),(-324785683/50000000000000)⟩
def e293 : ℝ := (1320175003/100000000000000)
theorem h293 : Model (fun x => f293 ((71/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(2817078518909881/20000000000000),(3484271584349/12500000000000),(3639625199/12500000000000),(-324785683/50000000000000)⟩
def e294 : ℝ := (330043751/25000000000000)
theorem h294 : Model (fun x => f294 ((71/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(7544820116314591/50000000000000),(63706896029379/100000000000000),(54347584747/50000000000000),(-176934253/12500000000000)⟩
def e295 : ℝ := (3023239187/100000000000000)
theorem h295 : Model (fun x => f295 ((71/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(17425354518343467/100000000000000),(63706896029379/100000000000000),(54347584747/50000000000000),(-176934253/12500000000000)⟩
def e296 : ℝ := (755809797/25000000000000)
theorem h296 : Model (fun x => f296 ((71/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(18667731754212697/100000000000000),(110119884924799/100000000000000),(282543946007/100000000000000),(-2210153683/100000000000000)⟩
def e297 : ℝ := (523901247/10000000000000)
theorem h297 : Model (fun x => f297 ((71/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(19070112706593649/100000000000000),(110119884924799/100000000000000),(282543946007/100000000000000),(-2210153683/100000000000000)⟩
def e298 : ℝ := (5239012471/100000000000000)
theorem h298 : Model (fun x => f298 ((71/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(20429756430753861/100000000000000),(163794126397247/100000000000000),(581540955989/100000000000000),(-675926453/25000000000000)⟩
def e299 : ℝ := (7814609837/100000000000000)
theorem h299 : Model (fun x => f299 ((71/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(20412137383134813/100000000000000),(163794126397247/100000000000000),(581540955989/100000000000000),(-675926453/25000000000000)⟩
def e300 : ℝ := (3907304919/50000000000000)
theorem h300 : Model (fun x => f300 ((71/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(5466865893565791/25000000000000),(28064987155133/12500000000000),(51591528123/5000000000000),(-2551103189/100000000000000)⟩
def e301 : ℝ := (2685655103/25000000000000)
theorem h301 : Model (fun x => f301 ((71/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(21870796907596497/100000000000000),(28064987155133/12500000000000),(51591528123/5000000000000),(-2551103189/100000000000000)⟩
def e302 : ℝ := (10742620413/100000000000000)
theorem h302 : Model (fun x => f302 ((71/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(77966219223011/5000000000000),(68560312253259/100000000000000),(629399984891/100000000000000),(24138423/2000000000000)⟩
def e303 : ℝ := (3319207353/100000000000000)
theorem h303 : Model (fun x => f303 ((71/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(57383873775709/50000000000000),(102967531979/20000000000000),(368733441/50000000000000),(-5984007/50000000000000)⟩
def e304 : ℝ := (24412207/100000000000000)
theorem h304 : Model (fun x => f304 ((71/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(25891213744433/12500000000000),(120143529771/50000000000000),(37358491/50000000000000),(-1150669/20000000000000)⟩
def e305 : ℝ := (11355399/100000000000000)
theorem h305 : Model (fun x => f305 ((71/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(214513583731173/50000000000000),(995411778979/100000000000000),(443450423/50000000000000),(-1467169/6250000000000)⟩
def e306 : ℝ := (9424601/20000000000000)
theorem h306 : Model (fun x => f306 ((71/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(8886427275949/1000000000000),(3092690295993/100000000000000),(909887399/20000000000000),(-1408633/2000000000000)⟩
def e307 : ℝ := (29332597/20000000000000)
theorem h307 : Model (fun x => f307 ((71/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(46016077605191/2500000000000),(4270586959941/50000000000000),(4379634313/25000000000000),(-91884541/50000000000000)⟩
def e308 : ℝ := (81147979/20000000000000)
theorem h308 : Model (fun x => f308 ((71/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(264058078894951/12500000000000),(19278836807019/100000000000000),(38826471927/50000000000000),(-55603141/20000000000000)⟩
def e309 : ℝ := (460512099/50000000000000)
theorem h309 : Model (fun x => f309 ((71/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(13391213744433/1562500000000),(120143529771/6250000000000),(37358491/6250000000000),(-1150669/2500000000000)⟩
def e310 : ℝ := (11355399/12500000000000)
theorem h310 : Model (fun x => f310 ((71/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(97180542719513/10000000000000),(2437134136231/100000000000000),(667601369/50000000000000),(-28997387/50000000000000)⟩
def e311 : ℝ := (115255399/100000000000000)
theorem h311 : Model (fun x => f311 ((71/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(107180542719513/10000000000000),(2437134136231/100000000000000),(667601369/50000000000000),(-28997387/50000000000000)⟩
def e312 : ℝ := (115255399/100000000000000)
theorem h312 : Model (fun x => f312 ((71/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(22641510564346263/100000000000000),(258115215839519/100000000000000),(133034526509/10000000000000),(-8027299/390625000000)⟩
def e313 : ℝ := (12368055507/100000000000000)
theorem h313 : Model (fun x => f313 ((71/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(55208330577/12500000000000),(-5035038673/100000000000000),(7862229/25000000000000),(-22591/100000000000000)⟩
def e314 : ℝ := (31117/12500000000000)
theorem h314 : Model (fun x => f314 ((71/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (22382050580197603/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1721753921881/25000000000000),(28036930609/12500000000000),(-90898913/50000000000000),(-5150757/100000000000000)⟩
def e315 : ℝ := (1900389/10000000000000)
theorem h315 : Model (fun x => f315 ((71/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(14283655395581/100000000000000),(483029491479/100000000000000),(46674351/20000000000000),(-10560289/100000000000000)⟩
def e316 : ℝ := (25919543/100000000000000)
theorem h316 : Model (fun x => f316 ((71/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(33255806044119/50000000000000),(103057847399/5000000000000),(-5714075909/100000000000000),(-73868239/100000000000000)⟩
def e317 : ℝ := (121877681/100000000000000)
theorem h317 : Model (fun x => f317 ((71/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(2341958172121/6250000000000),(633449960073/100000000000000),(-303525703/2500000000000),(64692243/50000000000000)⟩
def e318 : ℝ := (74484253/100000000000000)
theorem h318 : Model (fun x => f318 ((71/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-18377907206249/20000000000000),(-247462287503/20000000000000),(13592582799/50000000000000),(-9781303/2000000000000)⟩
def e319 : ℝ := (32943299/25000000000000)
theorem h319 : Model (fun x => f319 ((71/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((71/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-55451/1600),(-781/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((71/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((71/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(6887/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((71/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(220029/1600),(1159/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((71/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((71/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(392829/1600),(1159/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((71/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1964145/32),(5795/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((71/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((71/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(247036487792266637/25000000000000),(4483462346153457/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (32039/25000000000000)
theorem h329 : Model (fun x => f329 ((71/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(10119962529/100000000000000),(-45916771/100000000000000),(338437/50000000000000),(-2599/50000000000000)⟩
def e330 : ℝ := (59/100000000000000)
theorem h330 : Model (fun x => f330 ((71/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (491808369603503929/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(38822409768599/6250000000000),(423487023989/50000000000000),(3761021371/50000000000000),(1255987/25000000000000)⟩
def e331 : ℝ := (6697827/100000000000000)
theorem h331 : Model (fun x => f331 ((71/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((71/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(431/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((71/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((71/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((71/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(605806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((71/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((71/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((71/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(335957026166369/12500000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (521/50000000000000)
theorem h339 : Model (fun x => f339 ((71/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3704193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((71/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((71/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((71/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2087343790668789/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (521/50000000000000)
theorem h343 : Model (fun x => f343 ((71/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(1197694414871/25000000000000),(-1293338987/20000000000000),(2182221/25000000000000),(-11783/100000000000000)⟩
def e344 : ℝ := (21/100000000000000)
theorem h344 : Model (fun x => f344 ((71/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1042263124516633/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(128759633240361/100000000000000),(44445486587/5000000000000),(-1199869519/100000000000000),(809797/50000000000000)⟩
def e345 : ℝ := (647/20000000000000)
theorem h345 : Model (fun x => f345 ((71/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(228759633240361/100000000000000),(44445486587/5000000000000),(-1199869519/100000000000000),(809797/50000000000000)⟩
def e346 : ℝ := (647/20000000000000)
theorem h346 : Model (fun x => f346 ((71/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(5718990831009/5000000000000),(44445486587/10000000000000),(-14998369/2500000000000),(809797/100000000000000)⟩
def e347 : ℝ := (1619/100000000000000)
theorem h347 : Model (fun x => f347 ((71/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(718990831009/5000000000000),(44445486587/10000000000000),(-14998369/2500000000000),(809797/100000000000000)⟩
def e348 : ℝ := (1619/100000000000000)
theorem h348 : Model (fun x => f348 ((71/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(422115989907807/100000000000000),(820125050117/50000000000000),(-553511237/25000000000000),(373567/12500000000000)⟩
def e349 : ℝ := (5977/100000000000000)
theorem h349 : Model (fun x => f349 ((71/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(694457568905523/25000000000000),(820125050117/50000000000000),(-553511237/25000000000000),(373567/12500000000000)⟩
def e350 : ℝ := (2989/50000000000000)
theorem h350 : Model (fun x => f350 ((71/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3177277175276389/100000000000000),(3555579220593/25000000000000),(-5953709283/50000000000000),(6232207/100000000000000)⟩
def e351 : ℝ := (367/400000000000)
theorem h351 : Model (fun x => f351 ((71/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8459658127657341/100000000000000),(3555579220593/25000000000000),(-5953709283/50000000000000),(6232207/100000000000000)⟩
def e352 : ℝ := (91751/100000000000000)
theorem h352 : Model (fun x => f352 ((71/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(9676141453108619/100000000000000),(53866822153537/100000000000000),(-580166891/50000000000000),(-391333/625000000000)⟩
def e353 : ℝ := (45699/10000000000000)
theorem h353 : Model (fun x => f353 ((71/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(7472594536078119/50000000000000),(53866822153537/100000000000000),(-580166891/50000000000000),(-391333/625000000000)⟩
def e354 : ℝ := (456991/100000000000000)
theorem h354 : Model (fun x => f354 ((71/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(3418855970854297/20000000000000),(32009348110751/25000000000000),(148425140307/100000000000000),(-278914213/100000000000000)⟩
def e355 : ℝ := (932829/100000000000000)
theorem h355 : Model (fun x => f355 ((71/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(1942999413998577/10000000000000),(32009348110751/25000000000000),(148425140307/100000000000000),(-278914213/100000000000000)⟩
def e356 : ℝ := (93283/10000000000000)
theorem h356 : Model (fun x => f356 ((71/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(22223991666627443/100000000000000),(23280648907499/10000000000000),(124453907087/20000000000000),(-270136121/100000000000000)⟩
def e357 : ℝ := (2483907/100000000000000)
theorem h357 : Model (fun x => f357 ((71/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(4525274523801679/20000000000000),(23280648907499/10000000000000),(124453907087/20000000000000),(-270136121/100000000000000)⟩
def e358 : ℝ := (620977/25000000000000)
theorem h358 : Model (fun x => f358 ((71/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(1294000175471021/5000000000000),(366847649358913/100000000000000),(201340881/12500000000),(155408333/12500000000000)⟩
def e359 : ℝ := (6277493/100000000000000)
theorem h359 : Model (fun x => f359 ((71/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(6465596115450343/25000000000000),(366847649358913/100000000000000),(201340881/12500000000),(155408333/12500000000000)⟩
def e360 : ℝ := (3138747/50000000000000)
theorem h360 : Model (fun x => f360 ((71/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(5916269584202867/20000000000000),(66818286847831/12500000000000),(829415359377/25000000000000),(6589587119/100000000000000)⟩
def e361 : ℝ := (8805231/100000000000000)
theorem h361 : Model (fun x => f361 ((71/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(7396170313586917/25000000000000),(66818286847831/12500000000000),(829415359377/25000000000000),(6589587119/100000000000000)⟩
def e362 : ℝ := (550327/6250000000000)
theorem h362 : Model (fun x => f362 ((71/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(2127111456019981/50000000000000),(208357332326789/100000000000000),(2675401861801/100000000000000),(6362862533/50000000000000)⟩
def e363 : ℝ := (969903/6250000000000)
theorem h363 : Model (fun x => f363 ((71/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(6541371225033/5000000000000),(1016733321083/100000000000000),(602992721/100000000000000),(-348039/10000000000000)⟩
def e364 : ℝ := (14527/100000000000000)
theorem h364 : Model (fun x => f364 ((71/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(10718990831009/5000000000000),(44445486587/10000000000000),(-14998369/2500000000000),(809797/100000000000000)⟩
def e365 : ℝ := (1619/100000000000000)
theorem h365 : Model (fun x => f365 ((71/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(22979352887051/5000000000000),(1905643052823/100000000000000),(-596876799/100000000000000),(-465199/25000000000000)⟩
def e366 : ℝ := (3553/20000000000000)
theorem h366 : Model (fun x => f366 ((71/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(985261891595279/100000000000000),(1225594224623/20000000000000),(35463339/800000000000),(-897057/6250000000000)⟩
def e367 : ℝ := (28193/50000000000000)
theorem h367 : Model (fun x => f367 ((71/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(84488105457219/4000000000000),(17516177675029/100000000000000),(3082841741/10000000000000),(-19926319/50000000000000)⟩
def e368 : ℝ := (17807/10000000000000)
theorem h368 : Model (fun x => f368 ((71/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2763340309477029/100000000000000),(22195716068291/50000000000000),(14447579229/6250000000000),(293412999/100000000000000)⟩
def e369 : ℝ := (274883/20000000000000)
theorem h369 : Model (fun x => f369 ((71/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(5718990831009/625000000000),(44445486587/1250000000000),(-14998369/312500000000),(809797/12500000000000)⟩
def e370 : ℝ := (1619/12500000000000)
theorem h370 : Model (fun x => f370 ((71/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(10458659574621/1000000000000),(4572372248043/100000000000000),(-4196485359/100000000000000),(1498993/50000000000000)⟩
def e371 : ℝ := (27479/100000000000000)
theorem h371 : Model (fun x => f371 ((71/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(11458659574621/1000000000000),(4572372248043/100000000000000),(-4196485359/100000000000000),(1498993/50000000000000)⟩
def e372 : ℝ := (27479/100000000000000)
theorem h372 : Model (fun x => f372 ((71/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(6332835179025023/20000000000000),(39688532144531/6250000000000),(2281288312507/50000000000000),(6075818963/50000000000000)⟩
def e373 : ℝ := (4326997/20000000000000)
theorem h373 : Model (fun x => f373 ((71/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(315814314357/100000000000000),(-1266714193/20000000000000),(81511521/100000000000000),(-84327/10000000000000)⟩
def e374 : ℝ := (8073/100000000000000)
theorem h374 : Model (fun x => f374 ((71/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (15512292315457347/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(13435444920877/100000000000000),(388578053357/100000000000000),(-159934457/12500000000000),(470183/10000000000000)⟩
def e375 : ℝ := (805031/100000000000000)
theorem h375 : Model (fun x => f375 ((71/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(128759633240361/50000000000000),(44445486587/2500000000000),(-1199869519/50000000000000),(809797/25000000000000)⟩
def e376 : ℝ := (647/10000000000000)
theorem h376 : Model (fun x => f376 ((71/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(4371400608731/10000000000000),(-84931517143/50000000000000),(889335259/100000000000000),(-4656203/100000000000000)⟩
def e377 : ℝ := (24709/100000000000000)
theorem h377 : Model (fun x => f377 ((71/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (227869522016273/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(56285993912689/50000000000000),(339726068571/100000000000000),(-1778670519/100000000000000),(9312403/100000000000000)⟩
def e378 : ℝ := (176677/100000000000000)
theorem h378 : Model (fun x => f378 ((71/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(6285993912689/50000000000000),(339726068571/100000000000000),(-1778670519/100000000000000),(9312403/100000000000000)⟩
def e379 : ℝ := (176677/100000000000000)
theorem h379 : Model (fun x => f379 ((71/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(415444240784133/100000000000000),(250750193469/20000000000000),(-3282070601/50000000000000),(34367201/100000000000000)⟩
def e380 : ℝ := (26081/4000000000000)
theorem h380 : Model (fun x => f380 ((71/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1385579263249209/50000000000000),(250750193469/20000000000000),(-3282070601/50000000000000),(34367201/100000000000000)⟩
def e381 : ℝ := (326013/50000000000000)
theorem h381 : Model (fun x => f381 ((71/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3119548239071723/100000000000000),(10825720302263/100000000000000),(-5241984511/10000000000000),(252149093/100000000000000)⟩
def e382 : ℝ := (5985943/100000000000000)
theorem h382 : Model (fun x => f382 ((71/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(336077167658107/4000000000000),(10825720302263/100000000000000),(-5241984511/10000000000000),(252149093/100000000000000)⟩
def e383 : ℝ := (748243/12500000000000)
theorem h383 : Model (fun x => f383 ((71/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(1891643741299797/20000000000000),(20365136133457/50000000000000),(-85837452617/50000000000000),(695632977/100000000000000)⟩
def e384 : ℝ := (4885791/20000000000000)
theorem h384 : Model (fun x => f384 ((71/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3681816581386651/25000000000000),(20365136133457/50000000000000),(-85837452617/50000000000000),(695632977/100000000000000)⟩
def e385 : ℝ := (6107239/25000000000000)
theorem h385 : Model (fun x => f385 ((71/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(4144694113751329/25000000000000),(95883240033313/100000000000000),(-79209011279/25000000000000),(846868509/100000000000000)⟩
def e386 : ℝ := (62913721/100000000000000)
theorem h386 : Model (fun x => f386 ((71/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(18914490740719601/100000000000000),(95883240033313/100000000000000),(-79209011279/25000000000000),(846868509/100000000000000)⟩
def e387 : ℝ := (31456861/50000000000000)
theorem h387 : Model (fun x => f387 ((71/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(10646209106937559/50000000000000),(172195125080551/100000000000000),(-14694189719/4000000000000),(-33545623/50000000000000)⟩
def e388 : ℝ := (7631987/6250000000000)
theorem h388 : Model (fun x => f388 ((71/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(2169479916625607/10000000000000),(172195125080551/100000000000000),(-14694189719/4000000000000),(-33545623/50000000000000)⟩
def e389 : ℝ := (122111793/100000000000000)
theorem h389 : Model (fun x => f389 ((71/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(2442226667617799/10000000000000),(66886590883367/25000000000000),(-107212902379/50000000000000),(-591500643/25000000000000)⟩
def e390 : ℝ := (99444967/50000000000000)
theorem h390 : Model (fun x => f390 ((71/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(12202323814279471/50000000000000),(66886590883367/25000000000000),(-107212902379/50000000000000),(-591500643/25000000000000)⟩
def e391 : ℝ := (39777987/20000000000000)
theorem h391 : Model (fun x => f391 ((71/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(6868199239311943/25000000000000),(192045604860623/50000000000000),(9338523159/4000000000000),(-5878025639/100000000000000)⟩
def e392 : ℝ := (1444387/500000000000)
theorem h392 : Model (fun x => f392 ((71/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(5495226058116221/20000000000000),(192045604860623/50000000000000),(9338523159/4000000000000),(-5878025639/100000000000000)⟩
def e393 : ℝ := (288877401/100000000000000)
theorem h393 : Model (fun x => f393 ((71/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(3454295755016853/100000000000000),(70815738678069/50000000000000),(845499087137/100000000000000),(-210943943/5000000000000)⟩
def e394 : ℝ := (49150227/50000000000000)
theorem h394 : Model (fun x => f394 ((71/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(12672452442957/10000000000000),(382436388551/50000000000000),(-178151969/6250000000000),(8881099/100000000000000)⟩
def e395 : ℝ := (494229/100000000000000)
theorem h395 : Model (fun x => f395 ((71/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(106285993912689/50000000000000),(339726068571/100000000000000),(-1778670519/100000000000000),(9312403/100000000000000)⟩
def e396 : ℝ := (176677/100000000000000)
theorem h396 : Model (fun x => f396 ((71/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(225934250040163/50000000000000),(361081228561/25000000000000),(-3203886271/50000000000000),(5501181/20000000000000)⟩
def e397 : ℝ := (847583/100000000000000)
theorem h397 : Model (fun x => f397 ((71/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(240136463244367/25000000000000),(4605345271299/100000000000000),(-3350326603/20000000000000),(53091009/100000000000000)⟩
def e398 : ℝ := (147427/5000000000000)
theorem h398 : Model (fun x => f398 ((71/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(510462853412109/25000000000000),(3263224663141/25000000000000),(-2315541673/6250000000000),(63482931/100000000000000)⟩
def e399 : ℝ := (889277/10000000000000)
theorem h399 : Model (fun x => f399 ((71/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(161720405844027/6250000000000),(8039697338401/25000000000000),(-5313254313/100000000000000),(-196825907/50000000000000)⟩
def e400 : ℝ := (24199669/100000000000000)
theorem h400 : Model (fun x => f400 ((71/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(56285993912689/6250000000000),(339726068571/12500000000000),(-1778670519/12500000000000),(9312403/12500000000000)⟩
def e401 : ℝ := (176677/12500000000000)
theorem h401 : Model (fun x => f401 ((71/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(513650213516297/50000000000000),(348268132567/10000000000000),(-2134974457/12500000000000),(83380323/100000000000000)⟩
def e402 : ℝ := (381529/20000000000000)
theorem h402 : Model (fun x => f402 ((71/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(563650213516297/50000000000000),(348268132567/10000000000000),(-2134974457/12500000000000),(83380323/100000000000000)⟩
def e403 : ℝ := (381529/20000000000000)
theorem h403 : Model (fun x => f403 ((71/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(29169197210856967/100000000000000),(113160367924433/25000000000000),(38634223449/6250000000000),(-31085351/390625000000)⟩
def e404 : ℝ := (337699421/100000000000000)
theorem h404 : Model (fun x => f404 ((71/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(42853424829/12500000000000),(-5319923519/100000000000000),(75288327/100000000000000),(-962041/100000000000000)⟩
def e405 : ℝ := (16209/100000000000000)
theorem h405 : Model (fun x => f405 ((71/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (14357964648017387/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(11842272277979/100000000000000),(301785617177/100000000000000),(-407080453/20000000000000),(279137/2000000000000)⟩
def e406 : ℝ := (143821/10000000000000)
theorem h406 : Model (fun x => f406 ((71/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(3159714649857/12500000000000),(345181835267/50000000000000),(-3314877921/100000000000000),(466467/2500000000000)⟩
def e407 : ℝ := (2243241/100000000000000)
theorem h407 : Model (fun x => f407 ((71/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(785073516087/500000000000),(4502348713687/100000000000000),(-642102301/5000000000000),(141023221/100000000000000)⟩
def e408 : ℝ := (7875321/50000000000000)
theorem h408 : Model (fun x => f408 ((71/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(5528686733007/6250000000000),(51625330039/4000000000000),(-12706444309/50000000000000),(43737771/10000000000000)⟩
def e409 : ℝ := (11155079/50000000000000)
theorem h409 : Model (fun x => f409 ((71/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3430548303133/100000000000000),(2666090673/5000000000000),(88613849/5000000000000),(-646093/1250000000000)⟩
def e410 : ℝ := (77041677/50000000000000)
theorem h410 : Model (fun x => f410 ((71/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(2754586514648437/100000000000000),(45001016845703/25000000000000),(95779/2048000),(6177/10240000)⟩
def e411 : ℝ := (386718751/100000000000000)
theorem h411 : Model (fun x => f411 ((71/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(36481/1600),(191/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((71/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(6967871/64000),(109443/64000),(573/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((71/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(29990005456890499/10000000000000),(24308052076897039/100000000000000),(84164481448651/10000000000000),(4054873999237/25000000000000)⟩
def e414 : ℝ := (191219714513/100000000000000)
theorem h414 : Model (fun x => f414 ((71/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(16672221041/50000000000000),(-2702695189/100000000000000),(125485401/100000000000000),(-4389551/100000000000000)⟩
def e415 : ℝ := (194997/100000000000000)
theorem h415 : Model (fun x => f415 ((71/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (13736697348090499/5000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2757985786887/50000000000000),(3393490823/10000000000000),(-369195081/20000000000000),(42072823/100000000000000)⟩
def e416 : ℝ := (64159569/100000000000000)
theorem h416 : Model (fun x => f416 ((71/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2085423270641/100000000000000),(8725672169/10000000000000),(-2947937/4000000000000),(-9614617/100000000000000)⟩
def e417 : ℝ := (218242923/100000000000000)
theorem h417 : Model (fun x => f417 ((71/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((71/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((6255541384729/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (7/4) (9/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (7/4) (9/5) ≤ (6256850842267/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(71/40)-(1/40)) (by norm_num : ((71/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel15

