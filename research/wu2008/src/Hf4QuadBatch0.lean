import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel1
open Hf4Quad.Dag

def p0 : Cubic := ⟨(43/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((43/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((43/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((43/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((43/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(23547619047619/12500000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((43/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-23547619047619/12500000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((43/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-96952380952381/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((43/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((43/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(1849/1600),(43/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((43/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(139897883597883/100000000000000),(3253439153439/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((43/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-139897883597883/100000000000000),(-3253439153439/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((43/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-29606283068783/12500000000000),(-1088783068783/10000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((43/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((43/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(79507/64000),(5547/64000),(129/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((43/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(151289904152199/12500000000000),(84440876736111/100000000000000),(490935329861/25000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((43/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-151289904152199/12500000000000),(-84440876736111/100000000000000),(-490935329861/25000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((43/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-90448093610491/6250000000000),(-95328707423941/100000000000000),(-407880539021/20000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((43/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((43/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(3418801/2560000),(79507/640000),(5547/1280000),(43/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((43/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(373083442460317/100000000000000),(1084544890873/3125000000000),(75665922619/6250000000000),(18769841269/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((43/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1074086055307539/100000000000000),(-12124654183201/20000000000000),(-828747933201/100000000000000),(443380043/12500000000000)⟩
def e20 : ℝ := (54563497/50000000000000)
theorem h20 : Model (fun x => f20 ((43/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((43/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(143562932617187/100000000000000),(4173341064453/25000000000000),(79507/10240000),(1849/10240000)⟩
def e22 : ℝ := (210937501/100000000000000)
theorem h22 : Model (fun x => f22 ((43/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(93528592027271/10000000000000),(108754176775893/100000000000000),(505833380353/10000000000000),(117635669849/100000000000000)⟩
def e23 : ℝ := (1374218759/100000000000000)
theorem h23 : Model (fun x => f23 ((43/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(-138800135034829/100000000000000),(3008181616243/6250000000000),(4229585870329/100000000000000),(121182710193/100000000000000)⟩
def e24 : ℝ := (1483345753/100000000000000)
theorem h24 : Model (fun x => f24 ((43/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((43/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(38582538140869/25000000000000),(21534439892577/100000000000000),(250400463867/20000000000000),(38821777343/100000000000000)⟩
def e26 : ℝ := (683447269/100000000000000)
theorem h26 : Model (fun x => f26 ((43/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(10829648933191/3125000000000),(48355641748199/100000000000000),(1405687260121/50000000000000),(43587201863/50000000000000)⟩
def e27 : ℝ := (1534682653/100000000000000)
theorem h27 : Model (fun x => f27 ((43/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(207748630827283/100000000000000),(96486547608087/100000000000000),(7040960390571/100000000000000),(208357113919/100000000000000)⟩
def e28 : ℝ := (1509014203/50000000000000)
theorem h28 : Model (fun x => f28 ((43/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((43/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(20738114250717/12500000000000),(27007776698607/100000000000000),(1884263490599/100000000000000),(73033468627/100000000000000)⟩
def e30 : ℝ := (1722336431/100000000000000)
theorem h30 : Model (fun x => f30 ((43/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(19684749717347/50000000000000),(3204494140033/50000000000000),(447138717213/100000000000000),(17330958031/100000000000000)⟩
def e31 : ℝ := (408713171/100000000000000)
theorem h31 : Model (fun x => f31 ((43/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(247118130261977/100000000000000),(102895535888153/100000000000000),(936012388473/12500000000000),(4513761439/2000000000000)⟩
def e32 : ℝ := (3426741577/100000000000000)
theorem h32 : Model (fun x => f32 ((43/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((43/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(793221/320),(18447/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((43/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((43/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(94987/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((43/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(2313013/320),(36119/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((43/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((43/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(3042613/320),(36119/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((43/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-3042613/320),(-36119/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((43/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((43/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(83/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((43/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(6889/1600),(83/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((43/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((43/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(144669/160),(1743/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((43/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(110597294513/100000000000000),(-2664995049/100000000000000),(48162561/100000000000000),(-12089/1562500000000)⟩
def e46 : ℝ := (12059/100000000000000)
theorem h46 : Model (fun x => f46 ((43/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (70581/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-262894348476627/25000000000000),(372566312477/100000000000000),(-575141097/12500000000000),(56791569/100000000000000)⟩
def e47 : ℝ := (228523721/100000000000000)
theorem h47 : Model (fun x => f47 ((43/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((43/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(123/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((43/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((43/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((43/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(51249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((43/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(101249999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((43/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((43/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(101249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((43/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((43/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2126249999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((43/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((43/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(1249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((43/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(13289062499989/50000000000000),(1793749999997/20000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (67/100000000000000)
theorem h60 : Model (fun x => f60 ((43/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(102515624999997/100000000000000),(421874999999/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((43/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((43/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(101249999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((43/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1115015624999987/100000000000000),(2505208333329/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((43/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1215015624999987/100000000000000),(2505208333329/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((43/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1009151161193/312500000000),(13787923583961/12500000000000),(892807617181/100000000000000),(991210937/50000000000000)⟩
def e66 : ℝ := (633791/100000000000000)
theorem h66 : Model (fun x => f66 ((43/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(201249999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((43/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(81003124999999/20000000000000),(167708333333/10000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((43/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(163018789062497/20000000000000),(506269531249/10000000000000),(10481770833/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (43/100000000000000)
theorem h69 : Model (fun x => f69 ((43/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(2632169604459129/100000000000000),(228856280517049/25000000000000),(6447696965297/50000000000000),(72943838451/100000000000000)⟩
def e70 : ℝ := (51849001/25000000000000)
theorem h70 : Model (fun x => f70 ((43/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((43/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2152828124999937/12500000000000),(8859374999979/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((43/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(215282812499821/100000000000000),(73532812499877/100000000000000),(59427083333/10000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (273/50000000000000)
theorem h73 : Model (fun x => f73 ((43/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(175475716998447/10000000000000),(19070644230047/3125000000000),(8589173283853/100000000000000),(23857445607/50000000000000)⟩
def e74 : ℝ := (25862039/20000000000000)
theorem h74 : Model (fun x => f74 ((43/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(4386926774443599/100000000000000),(15256857374297/1000000000000),(21484567214447/100000000000000),(24131745933/20000000000000)⟩
def e75 : ℝ := (336706199/100000000000000)
theorem h75 : Model (fun x => f75 ((43/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((43/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(717609374999979/12500000000000),(2953124999993/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((43/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(15624999999/100000000000000),(5208333333/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((43/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(195312499/100000000000000),(195312499/100000000000000),(32552083/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((43/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(5606323213/50000000000000),(5652465791/50000000000000),(478752979/12500000000000),(446234791/100000000000000)⟩
def e80 : ℝ := (139539/4000000000000)
theorem h80 : Model (fun x => f80 ((43/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(5641362733/25000000000000),(2849736771/12500000000000),(7755026843/100000000000000),(914005949/100000000000000)⟩
def e81 : ℝ := (4447203/50000000000000)
theorem h81 : Model (fun x => f81 ((43/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(4386949339894531/100000000000000),(381427133830967/25000000000000),(2149232224129/10000000000000),(60786367807/50000000000000)⟩
def e82 : ℝ := (69120121/20000000000000)
theorem h82 : Model (fun x => f82 ((43/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(1220703/50000000000000),(406901/12500000000000),(406901/25000000000000),(361689/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((43/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(30517/100000000000000),(25431/50000000000000),(8477/25000000000000),(5651/50000000000000)⟩
def e84 : ℝ := (503/25000000000000)
theorem h84 : Model (fun x => f84 ((43/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(381/100000000000000),(381/50000000000000),(127/20000000000000),(141/50000000000000)⟩
def e85 : ℝ := (21/25000000000000)
theorem h85 : Model (fun x => f85 ((43/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(1/25000000000000),(11/100000000000000),(11/100000000000000),(3/50000000000000)⟩
def e86 : ℝ := (1/25000000000000)
theorem h86 : Model (fun x => f86 ((43/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(3/25000000000000),(33/100000000000000),(33/100000000000000),(9/50000000000000)⟩
def e87 : ℝ := (3/25000000000000)
theorem h87 : Model (fun x => f87 ((43/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-3/25000000000000),(-33/100000000000000),(-33/100000000000000),(-9/50000000000000)⟩
def e88 : ℝ := (3/25000000000000)
theorem h88 : Model (fun x => f88 ((43/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(4386949339894519/100000000000000),(305141707064767/20000000000000),(21492322241257/100000000000000),(30393183899/25000000000000)⟩
def e89 : ℝ := (345600617/100000000000000)
theorem h89 : Model (fun x => f89 ((43/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2152828124999937/10000000000000),(8859374999979/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((43/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1640376564941367/100000000000000),(2716979817703/20000000000000),(42189127603/100000000000000),(58232059/100000000000000)⟩
def e91 : ℝ := (1891/6250000000000)
theorem h91 : Model (fun x => f91 ((43/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(7062897609193121/2000000000000),(1166227501860541/20000000000000),(39133876678999/100000000000000),(68409249917/50000000000000)⟩
def e92 : ℝ := (65950467/25000000000000)
theorem h92 : Model (fun x => f92 ((43/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(14158494931/50000000000000),(-233785439/50000000000000),(916517/20000000000000),(-1393/4000000000000)⟩
def e93 : ℝ := (279/100000000000000)
theorem h93 : Model (fun x => f93 ((43/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (86818617997843161/25000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(1242251999829/100000000000000),(16460905349/4000000000000),(-423377201/50000000000000),(1161517/50000000000000)⟩
def e94 : ℝ := (232873/100000000000000)
theorem h94 : Model (fun x => f94 ((43/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(51249999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((43/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(49382716049383/100000000000000),(-101610526851/50000000000000),(104537579/12500000000000),(-3441567/100000000000000)⟩
def e96 : ℝ := (569/4000000000000)
theorem h96 : Model (fun x => f96 ((43/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (10083333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(101234567901233/100000000000000),(2032210537/500000000000),(-1672601267/100000000000000),(6883131/100000000000000)⟩
def e97 : ℝ := (17353/20000000000000)
theorem h97 : Model (fun x => f97 ((43/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2125925925925893/100000000000000),(42676421277/500000000000),(-35124626607/100000000000000),(144545751/100000000000000)⟩
def e98 : ℝ := (364413/20000000000000)
theorem h98 : Model (fun x => f98 ((43/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1234567901233/100000000000000),(2032210537/500000000000),(-1672601267/100000000000000),(6883131/100000000000000)⟩
def e99 : ℝ := (17353/20000000000000)
theorem h99 : Model (fun x => f99 ((43/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(26245999085471/100000000000000),(1093254001849/12500000000000),(-650456069/50000000000000),(-34351941/25000000000000)⟩
def e100 : ℝ := (3649259/100000000000000)
theorem h100 : Model (fun x => f100 ((43/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(102484377381493/100000000000000),(82291982239/10000000000000),(-346909893/20000000000000),(5311/1562500000000)⟩
def e101 : ℝ := (260541/100000000000000)
theorem h101 : Model (fun x => f101 ((43/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(101234567901233/10000000000000),(2032210537/50000000000),(-1672601267/10000000000000),(6883131/10000000000000)⟩
def e102 : ℝ := (17353/2000000000000)
theorem h102 : Model (fun x => f102 ((43/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1114830056393823/100000000000000),(488734089639/10000000000000),(-3692112427/20000000000000),(34585607/50000000000000)⟩
def e103 : ℝ := (1128191/100000000000000)
theorem h103 : Model (fun x => f103 ((43/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1214830056393823/100000000000000),(488734089639/10000000000000),(-3692112427/20000000000000),(34585607/50000000000000)⟩
def e104 : ℝ := (1128191/100000000000000)
theorem h104 : Model (fun x => f104 ((43/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(318844285491149/100000000000000),(107532157104489/100000000000000),(406799368841/100000000000000),(-3329262827/100000000000000)⟩
def e105 : ℝ := (362851/800000000000)
theorem h105 : Model (fun x => f105 ((43/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(201234567901233/100000000000000),(2032210537/500000000000),(-1672601267/100000000000000),(6883131/100000000000000)⟩
def e106 : ℝ := (17353/20000000000000)
theorem h106 : Model (fun x => f106 ((43/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(404953513183959/100000000000000),(163580403719/10000000000000),(-5079751999/100000000000000),(7053083/50000000000000)⟩
def e107 : ℝ := (434071/100000000000000)
theorem h107 : Model (fun x => f107 ((43/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(407453226228301/50000000000000),(197508191157/4000000000000),(-10346878177/100000000000000),(515827/6250000000000)⟩
def e108 : ℝ := (92721/6250000000000)
theorem h108 : Model (fun x => f108 ((43/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(1299141327878261/50000000000000),(223007519058069/25000000000000),(8591664335673/100000000000000),(-18143732059/100000000000000)⟩
def e109 : ℝ := (576171473/100000000000000)
theorem h109 : Model (fun x => f109 ((43/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2152171925011353/12500000000000),(1728131627019/1250000000000),(-7285107753/2500000000000),(111531/195312500000)⟩
def e110 : ℝ := (5471361/12500000000000)
theorem h110 : Model (fun x => f110 ((43/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(53140047531077/25000000000000),(17921365020939/25000000000000),(135166372559/50000000000000),(-2310970449/100000000000000)⟩
def e111 : ℝ := (7427/24414062500)
theorem h111 : Model (fun x => f111 ((43/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(866083352338503/50000000000000),(594665034361589/100000000000000),(2860291013747/50000000000000),(-12883678569/100000000000000)⟩
def e112 : ℝ := (97513489/25000000000000)
theorem h112 : Model (fun x => f112 ((43/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(541306170054191/12500000000000),(297339022118773/20000000000000),(14312246363167/100000000000000),(-7756852657/25000000000000)⟩
def e113 : ℝ := (966225429/100000000000000)
theorem h113 : Model (fun x => f113 ((43/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(717390641670451/12500000000000),(576043875673/1250000000000),(-2428369251/2500000000000),(37177/195312500000)⟩
def e114 : ℝ := (1823787/12500000000000)
theorem h114 : Model (fun x => f114 ((43/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(15241579027/100000000000000),(1003560759/10000000000000),(1610653069/100000000000000),(-6713179/50000000000000)⟩
def e115 : ℝ := (87011/100000000000000)
theorem h115 : Model (fun x => f115 ((43/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(94083821/50000000000000),(23230573/12500000000000),(60418609/100000000000000),(388363/6250000000000)⟩
def e116 : ℝ := (82611/100000000000000)
theorem h116 : Model (fun x => f116 ((43/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(5399588217/50000000000000),(10752567483/100000000000000),(710592101/20000000000000),(96070187/25000000000000)⟩
def e117 : ℝ := (7590281/100000000000000)
theorem h117 : Model (fun x => f117 ((43/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(21731676033/100000000000000),(2710221889/12500000000000),(3596653527/50000000000000),(393783663/50000000000000)⟩
def e118 : ℝ := (16814673/100000000000000)
theorem h118 : Model (fun x => f118 ((43/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(4330471092109561/100000000000000),(1486716792368977/100000000000000),(14319439670221/100000000000000),(-15119921651/50000000000000)⟩
def e119 : ℝ := (491520051/50000000000000)
theorem h119 : Model (fun x => f119 ((43/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(2323057/100000000000000),(305917/10000000000000),(1463/97656250000),(19949/6250000000000)⟩
def e120 : ℝ := (25717/100000000000000)
theorem h120 : Model (fun x => f120 ((43/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(28679/100000000000000),(47209/100000000000000),(3089/10000000000000),(4989/50000000000000)⟩
def e121 : ℝ := (851/50000000000000)
theorem h121 : Model (fun x => f121 ((43/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(177/50000000000000),(699/100000000000000),(143/25000000000000),(247/100000000000000)⟩
def e122 : ℝ := (71/100000000000000)
theorem h122 : Model (fun x => f122 ((43/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(1/25000000000000),(1/10000000000000),(9/100000000000000),(1/20000000000000)⟩
def e123 : ℝ := (1/25000000000000)
theorem h123 : Model (fun x => f123 ((43/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(3/25000000000000),(3/10000000000000),(27/100000000000000),(3/20000000000000)⟩
def e124 : ℝ := (3/25000000000000)
theorem h124 : Model (fun x => f124 ((43/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-3/25000000000000),(-3/10000000000000),(-27/100000000000000),(-3/20000000000000)⟩
def e125 : ℝ := (3/25000000000000)
theorem h125 : Model (fun x => f125 ((43/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(4330471092109549/100000000000000),(1486716792368947/100000000000000),(7159719835097/50000000000000),(-30239843317/100000000000000)⟩
def e126 : ℝ := (491520057/50000000000000)
theorem h126 : Model (fun x => f126 ((43/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2152171925011353/10000000000000),(1728131627019/1000000000000),(-7285107753/2000000000000),(111531/156250000000)⟩
def e127 : ℝ := (5471361/10000000000000)
theorem h127 : Model (fun x => f127 ((43/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1639873478400309/100000000000000),(13248491834811/100000000000000),(-14382719879/100000000000000),(-51942749/100000000000000)⟩
def e128 : ℝ := (2125059/50000000000000)
theorem h128 : Model (fun x => f128 ((43/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(176464483039192821/50000000000000),(5685220439895471/100000000000000),(6913200830717/50000000000000),(-41561005971/50000000000000)⟩
def e129 : ℝ := (1854645619/100000000000000)
theorem h129 : Model (fun x => f129 ((43/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(2833431359/10000000000000),(-114107111/25000000000000),(624243/10000000000000),(-76003/100000000000000)⟩
def e130 : ℝ := (1047/100000000000000)
theorem h130 : Model (fun x => f130 ((43/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (43403729282521397/12500000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(613504629581/50000000000000),(401485496321/100000000000000),(-614539189/25000000000000),(15589719/100000000000000)⟩
def e131 : ℝ := (90997/20000000000000)
theorem h131 : Model (fun x => f131 ((43/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(2469261258991/100000000000000),(406504065023/50000000000000),(-1652455579/50000000000000),(17912753/100000000000000)⟩
def e132 : ℝ := (343929/50000000000000)
theorem h132 : Model (fun x => f132 ((43/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-25966193196041/100000000000000),(-1067526258821/12500000000000),(18834539573/50000000000000),(-118342333/50000000000000)⟩
def e133 : ℝ := (7713773/50000000000000)
theorem h133 : Model (fun x => f133 ((43/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(93023255813953/100000000000000),(-1081665765279/50000000000000),(25155017797/50000000000000),(-292500207/25000000000000)⟩
def e134 : ℝ := (5571433/20000000000000)
theorem h134 : Model (fun x => f134 ((43/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (21/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-24154598321899/100000000000000),(-3691323308149/50000000000000),(206730460049/100000000000000),(-50278569/1000000000000)⟩
def e135 : ℝ := (9304417/6250000000000)
theorem h135 : Model (fun x => f135 ((43/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(3418801/256000),(79507/64000),(5547/128000),(43/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((43/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((43/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(715563/32000),(49923/32000),(1161/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((43/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(1828661/51200),(179353/64000),(10191/128000),(61/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((43/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-1849/1600),(-43/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((43/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(1769493/51200),(175913/64000),(10111/128000),(61/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((43/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((43/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(129/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((43/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-129/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((43/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(1439253/51200),(166313/64000),(10111/128000),(61/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((43/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(1592853/51200),(166313/64000),(10111/128000),(61/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((43/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((43/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(1592853/800),(166313/1000),(10111/2000),(61/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((43/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((43/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(646153389/512000),(15026823/128000),(1048383/256000),(8127/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((43/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(79238151299/100000000000000),(-7370990819/100000000000000),(428545977/100000000000000),(-4983093/25000000000000)⟩
def e151 : ℝ := (500159/50000000000000)
theorem h151 : Model (fun x => f151 ((43/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (291958317/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(19721051095479/12500000000000),(-1497796391781/100000000000000),(27960309189/100000000000000),(-211105739/25000000000000)⟩
def e152 : ℝ := (3858919597/100000000000000)
theorem h152 : Model (fun x => f152 ((43/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(163/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((43/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(20049/1600),(143/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((43/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(249/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((43/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(1004016064257/12500000000000),(-967726327/1000000000000),(1165935333/100000000000000),(-7023707/50000000000000)⟩
def e156 : ℝ := (10707/6250000000000)
theorem h156 : Model (fun x => f156 ((43/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (123/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(50323795180721/50000000000000),(223121401261/100000000000000),(1165935329/50000000000000),(-1755927/6250000000000)⟩
def e157 : ℝ := (3968423/100000000000000)
theorem h157 : Model (fun x => f157 ((43/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(100323795180721/50000000000000),(223121401261/100000000000000),(1165935329/50000000000000),(-1755927/6250000000000)⟩
def e158 : ℝ := (3968423/100000000000000)
theorem h158 : Model (fun x => f158 ((43/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(100323795180721/100000000000000),(11156070063/10000000000000),(1165935329/100000000000000),(-1755927/12500000000000)⟩
def e159 : ℝ := (496053/25000000000000)
theorem h159 : Model (fun x => f159 ((43/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(323795180721/100000000000000),(11156070063/10000000000000),(1165935329/100000000000000),(-1755927/12500000000000)⟩
def e160 : ℝ := (496053/25000000000000)
theorem h160 : Model (fun x => f160 ((43/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((43/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((43/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(18512128872633/5000000000000),(411712109467/100000000000000),(4302856571/100000000000000),(-10368331/20000000000000)⟩
def e163 : ℝ := (732269/10000000000000)
theorem h163 : Model (fun x => f163 ((43/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(545191372633389/20000000000000),(411712109467/100000000000000),(4302856571/100000000000000),(-10368331/20000000000000)⟩
def e164 : ℝ := (7322691/100000000000000)
theorem h164 : Model (fun x => f164 ((43/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((43/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(683695845029603/25000000000000),(431767723607/12500000000000),(2284937003/6250000000000),(-425335423/100000000000000)⟩
def e166 : ℝ := (15379599/25000000000000)
theorem h166 : Model (fun x => f166 ((43/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(2004291083124841/25000000000000),(431767723607/12500000000000),(2284937003/6250000000000),(-425335423/100000000000000)⟩
def e167 : ℝ := (61518397/100000000000000)
theorem h167 : Model (fun x => f167 ((43/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((43/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8043123524238479/100000000000000),(6204665416749/50000000000000),(134005784419/100000000000000),(-1471858537/100000000000000)⟩
def e169 : ℝ := (27684673/12500000000000)
theorem h169 : Model (fun x => f169 ((43/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(6656085571643049/50000000000000),(6204665416749/50000000000000),(134005784419/100000000000000),(-1471858537/100000000000000)⟩
def e170 : ℝ := (44295477/20000000000000)
theorem h170 : Model (fun x => f170 ((43/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((43/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(1335527531189739/10000000000000),(27300663045211/100000000000000),(37936866441/12500000000000),(-3052457839/100000000000000)⟩
def e172 : ℝ := (488693809/100000000000000)
theorem h172 : Model (fun x => f172 ((43/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(627639583904467/4000000000000),(27300663045211/100000000000000),(37936866441/12500000000000),(-3052457839/100000000000000)⟩
def e173 : ℝ := (48869381/10000000000000)
theorem h173 : Model (fun x => f173 ((43/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((43/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(629671850629447/4000000000000),(11223509801833/25000000000000),(8091894307/1562500000000),(-4609630987/100000000000000)⟩
def e175 : ℝ := (806497907/100000000000000)
theorem h175 : Model (fun x => f175 ((43/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(16144177218117127/100000000000000),(11223509801833/25000000000000),(8091894307/1562500000000),(-4609630987/100000000000000)⟩
def e176 : ℝ := (201624477/25000000000000)
theorem h176 : Model (fun x => f176 ((43/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((43/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(16196451285916447/100000000000000),(15762490289549/25000000000000),(378936440287/50000000000000),(-1158241817/20000000000000)⟩
def e178 : ℝ := (1136792411/100000000000000)
theorem h178 : Model (fun x => f178 ((43/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(16178832238297399/100000000000000),(15762490289549/25000000000000),(378936440287/50000000000000),(-1158241817/20000000000000)⟩
def e179 : ℝ := (284198103/25000000000000)
theorem h179 : Model (fun x => f179 ((43/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((43/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(16231218517381941/100000000000000),(81303332492669/100000000000000),(509650267869/50000000000000),(-3251029271/50000000000000)⟩
def e181 : ℝ := (367674891/25000000000000)
theorem h181 : Model (fun x => f181 ((43/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(8117275925357637/50000000000000),(81303332492669/100000000000000),(509650267869/50000000000000),(-3251029271/50000000000000)⟩
def e182 : ℝ := (294139913/20000000000000)
theorem h182 : Model (fun x => f182 ((43/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(52566696504267/100000000000000),(734985442447/4000000000000),(70821847227/25000000000000),(-216505291/100000000000000)⟩
def e183 : ℝ := (337191957/100000000000000)
theorem h183 : Model (fun x => f183 ((43/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(12581079849329/12500000000000),(55960964401/25000000000000),(1231939521/50000000000000),(-25584351/100000000000000)⟩
def e184 : ℝ := (1000957/25000000000000)
theorem h184 : Model (fun x => f184 ((43/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(200323795180721/100000000000000),(11156070063/10000000000000),(1165935329/100000000000000),(-1755927/12500000000000)⟩
def e185 : ℝ := (496053/25000000000000)
theorem h185 : Model (fun x => f185 ((43/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(200648114578037/50000000000000),(27935328679/6250000000000),(47957497/1000000000000),(-53679183/100000000000000)⟩
def e186 : ℝ := (1993063/25000000000000)
theorem h186 : Model (fun x => f186 ((43/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(80389183616257/10000000000000),(1343066654543/100000000000000),(1478451989/10000000000000),(-15334243/10000000000000)⟩
def e187 : ℝ := (4803781/20000000000000)
theorem h187 : Model (fun x => f187 ((43/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1610386635348843/100000000000000),(3587309458917/100000000000000),(40488104837/100000000000000),(-96988601/25000000000000)⟩
def e188 : ℝ := (64311773/100000000000000)
theorem h188 : Model (fun x => f188 ((43/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(405208056952321/25000000000000),(1443065941331/20000000000000),(5528667317/6250000000000),(-124692139/20000000000000)⟩
def e189 : ℝ := (65152753/50000000000000)
theorem h189 : Model (fun x => f189 ((43/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((43/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(100323795180721/12500000000000),(11156070063/1250000000000),(1165935329/12500000000000),(-1755927/1562500000000)⟩
def e191 : ℝ := (496053/3125000000000)
theorem h191 : Model (fun x => f191 ((43/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(2258097500601/250000000000),(279082365661/25000000000000),(5895680837/50000000000000),(-137963679/100000000000000)⟩
def e192 : ℝ := (4969381/25000000000000)
theorem h192 : Model (fun x => f192 ((43/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(2508097500601/250000000000),(279082365661/25000000000000),(5895680837/50000000000000),(-137963679/100000000000000)⟩
def e193 : ℝ := (4969381/25000000000000)
theorem h193 : Model (fun x => f193 ((43/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(16260821037848063/100000000000000),(45240414656079/50000000000000),(231823397787/20000000000000),(-83158559/1250000000000)⟩
def e194 : ℝ := (1639059461/100000000000000)
theorem h194 : Model (fun x => f194 ((43/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(76871887163/12500000000000),(-3421934027/100000000000000),(-24796329/100000000000000),(633501/100000000000000)⟩
def e195 : ℝ := (65923/100000000000000)
theorem h195 : Model (fun x => f195 ((43/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (16169172799802789/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(20204505811/6250000000000),(111200638321/100000000000000),(27508609/2500000000000),(-7624293/50000000000000)⟩
def e196 : ℝ := (437529/20000000000000)
theorem h196 : Model (fun x => f196 ((43/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(50323795180721/25000000000000),(223121401261/50000000000000),(1165935329/25000000000000),(-1755927/3125000000000)⟩
def e197 : ℝ := (3968423/50000000000000)
theorem h197 : Model (fun x => f197 ((43/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(1993544997373/4000000000000),(-55420869059/100000000000000),(-6469779/1250000000000),(8198083/100000000000000)⟩
def e198 : ℝ := (499487/50000000000000)
theorem h198 : Model (fun x => f198 ((43/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (50105526256567/25000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(100322750131349/100000000000000),(55420869057/50000000000000),(258791159/25000000000000),(-1639617/10000000000000)⟩
def e199 : ℝ := (6019713/100000000000000)
theorem h199 : Model (fun x => f199 ((43/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(322750131349/100000000000000),(55420869057/50000000000000),(258791159/25000000000000),(-1639617/10000000000000)⟩
def e200 : ℝ := (6019713/100000000000000)
theorem h200 : Model (fun x => f200 ((43/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(74047744144567/20000000000000),(20452939771/5000000000000),(1910125221/50000000000000),(-2420387/4000000000000)⟩
def e201 : ℝ := (2221561/10000000000000)
theorem h201 : Model (fun x => f201 ((43/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2129650786279/78125000000),(20452939771/5000000000000),(1910125221/50000000000000),(-2420387/4000000000000)⟩
def e202 : ℝ := (22215611/100000000000000)
theorem h202 : Model (fun x => f202 ((43/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2734751023345907/100000000000000),(137274909029/4000000000000),(325040897/1000000000000),(-124796999/25000000000000)⟩
def e203 : ℝ := (46631859/25000000000000)
theorem h203 : Model (fun x => f203 ((43/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8017131975726859/100000000000000),(137274909029/4000000000000),(325040897/1000000000000),(-124796999/25000000000000)⟩
def e204 : ℝ := (186527437/100000000000000)
theorem h204 : Model (fun x => f204 ((43/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(402150363985447/5000000000000),(12329277528243/100000000000000),(23880691821/20000000000000),(-1743748083/100000000000000)⟩
def e205 : ℝ := (670945203/100000000000000)
theorem h205 : Model (fun x => f205 ((43/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13312054898756559/100000000000000),(12329277528243/100000000000000),(23880691821/20000000000000),(-1743748083/100000000000000)⟩
def e206 : ℝ := (167736301/25000000000000)
theorem h206 : Model (fun x => f206 ((43/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(6677509786713773/50000000000000),(27124383316131/100000000000000),(33907063009/12500000000000),(-1836032997/50000000000000)⟩
def e207 : ℝ := (1478714667/100000000000000)
theorem h207 : Model (fun x => f207 ((43/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(15690733859141831/100000000000000),(27124383316131/100000000000000),(33907063009/12500000000000),(-1836032997/50000000000000)⟩
def e208 : ℝ := (369678667/25000000000000)
theorem h208 : Model (fun x => f208 ((43/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(15741375723281833/100000000000000),(22301904715613/50000000000000),(232311025377/50000000000000),(-2837574771/50000000000000)⟩
def e209 : ℝ := (60928027/2500000000000)
theorem h209 : Model (fun x => f209 ((43/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(3228751335132557/20000000000000),(22301904715613/50000000000000),(232311025377/50000000000000),(-2837574771/50000000000000)⟩
def e210 : ℝ := (2437121081/100000000000000)
theorem h210 : Model (fun x => f210 ((43/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(16195860671538149/100000000000000),(62641788780951/100000000000000),(6826757167/1000000000000),(-3681852933/50000000000000)⟩
def e211 : ℝ := (3431165173/100000000000000)
theorem h211 : Model (fun x => f211 ((43/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(16178241623919101/100000000000000),(62641788780951/100000000000000),(6826757167/1000000000000),(-3681852933/50000000000000)⟩
def e212 : ℝ := (1715582587/50000000000000)
theorem h212 : Model (fun x => f212 ((43/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(8115228460005129/50000000000000),(16155241889751/20000000000000),(1440287089/156250000000),(-4317474481/50000000000000)⟩
def e213 : ℝ := (277208143/6250000000000)
theorem h213 : Model (fun x => f213 ((43/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(16233790253343591/100000000000000),(16155241889751/20000000000000),(1440287089/156250000000),(-4317474481/50000000000000)⟩
def e214 : ℝ := (4435330289/100000000000000)
theorem h214 : Model (fun x => f214 ((43/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(52394579365587/100000000000000),(18254520600681/100000000000000),(130277634271/50000000000000),(-831701287/100000000000000)⟩
def e215 : ℝ := (1585843/156250000000)
theorem h215 : Model (fun x => f215 ((43/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(10064654193917/10000000000000),(111199479969/50000000000000),(2199870171/100000000000000),(-30603389/100000000000000)⟩
def e216 : ℝ := (3029433/25000000000000)
theorem h216 : Model (fun x => f216 ((43/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(200322750131349/100000000000000),(55420869057/50000000000000),(258791159/25000000000000),(-1639617/10000000000000)⟩
def e217 : ℝ := (6019713/100000000000000)
theorem h217 : Model (fun x => f217 ((43/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(100323010550467/25000000000000),(222041218083/50000000000000),(4270199443/100000000000000),(-63395729/100000000000000)⟩
def e218 : ℝ := (12078579/50000000000000)
theorem h218 : Model (fun x => f218 ((43/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(160775850999407/20000000000000),(1334397223467/100000000000000),(13200442959/100000000000000),(-91731223/50000000000000)⟩
def e219 : ℝ := (14540637/20000000000000)
theorem h219 : Model (fun x => f219 ((43/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(80517651567273/5000000000000),(1782067477151/50000000000000),(9061008301/25000000000000),(-235438809/50000000000000)⟩
def e220 : ℝ := (97242161/50000000000000)
theorem h220 : Model (fun x => f220 ((43/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1620764639061803/100000000000000),(56004585739/781250000000),(19957660283/25000000000000),(-201932987/25000000000000)⟩
def e221 : ℝ := (393115493/100000000000000)
theorem h221 : Model (fun x => f221 ((43/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(100322750131349/12500000000000),(55420869057/6250000000000),(258791159/3125000000000),(-1639617/1250000000000)⟩
def e222 : ℝ := (6019713/12500000000000)
theorem h222 : Model (fun x => f222 ((43/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(451614271494981/50000000000000),(22182657297/2000000000000),(10481187259/100000000000000),(-161772749/100000000000000)⟩
def e223 : ℝ := (15068859/25000000000000)
theorem h223 : Model (fun x => f223 ((43/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(501614271494981/50000000000000),(22182657297/2000000000000),(10481187259/100000000000000),(-161772749/100000000000000)⟩
def e224 : ℝ := (15068859/25000000000000)
theorem h224 : Model (fun x => f224 ((43/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(8129986736878121/50000000000000),(89893743931869/100000000000000),(65641769301/6250000000000),(-9088572063/100000000000000)⟩
def e225 : ℝ := (4941945091/100000000000000)
theorem h225 : Model (fun x => f225 ((43/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(153751788343/25000000000000),(-136003409/4000000000000),(-10463613/50000000000000),(169769/25000000000000)⟩
def e226 : ℝ := (48351/25000000000000)
theorem h226 : Model (fun x => f226 ((43/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (16169015430998403/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(322230411077/100000000000000),(27621286789/25000000000000),(19415991/2000000000000),(-1743849/10000000000000)⟩
def e227 : ℝ := (6513489/100000000000000)
theorem h227 : Model (fun x => f227 ((43/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(645502504053/100000000000000),(221685785477/100000000000000),(207114391/10000000000000),(-8171769/25000000000000)⟩
def e228 : ℝ := (4350567/50000000000000)
theorem h228 : Model (fun x => f228 ((43/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(40735961167/4000000000000),(85020455747/25000000000000),(12769359/10000000000000),(-26058139/100000000000000)⟩
def e229 : ℝ := (48236279/100000000000000)
theorem h229 : Model (fun x => f229 ((43/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(236836983529/25000000000000),(294323836869/100000000000000),(-3362977829/50000000000000),(33044361/25000000000000)⟩
def e230 : ℝ := (9936739/20000000000000)
theorem h230 : Model (fun x => f230 ((43/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-23207250387783/100000000000000),(-7088322779429/100000000000000),(200004504391/100000000000000),(-152989983/3125000000000)⟩
def e231 : ℝ := (198554367/100000000000000)
theorem h231 : Model (fun x => f231 ((43/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((43/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-1849/320),(-43/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((43/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(903/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((43/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1075/64),(41/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((43/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((43/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2739/64),(41/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((43/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((43/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(342375/32),(1025/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((43/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(8471/1600),(77/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((43/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(18071/1600),(77/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((43/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((43/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3415419/1600),(14553/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((43/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(46846375217/100000000000000),(-399222057/100000000000000),(5994497/100000000000000),(-73177/100000000000000)⟩
def e244 : ℝ := (971/100000000000000)
theorem h244 : Model (fun x => f244 ((43/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (846531/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(501219616091261/100000000000000),(-1270268205329/100000000000000),(981270517/50000000000000),(-17404407/20000000000000)⟩
def e245 : ℝ := (19880179/100000000000000)
theorem h245 : Model (fun x => f245 ((43/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(387/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((43/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(32809/1600),(403/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((43/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(66409/1600),(403/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((43/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(15129/1600),(123/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((43/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1004701761/2560000),(7132647/640000),(139907/1280000),(263/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((43/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((43/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(62001/160),(747/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((43/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(51612070773/20000000000000),(-310916089/5000000000000),(112379309/100000000000000),(-1805291/100000000000000)⟩
def e253 : ℝ := (14067/50000000000000)
theorem h253 : Model (fun x => f253 ((43/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (30249/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(101278785926737/100000000000000),(435568278291/100000000000000),(1504729053/50000000000000),(-928043/3125000000000)⟩
def e254 : ℝ := (2200487/10000000000000)
theorem h254 : Model (fun x => f254 ((43/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(201278785926737/100000000000000),(435568278291/100000000000000),(1504729053/50000000000000),(-928043/3125000000000)⟩
def e255 : ℝ := (2200487/10000000000000)
theorem h255 : Model (fun x => f255 ((43/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(12579924120421/12500000000000),(43556827829/20000000000000),(1504729053/100000000000000),(-928043/6250000000000)⟩
def e256 : ℝ := (2750609/25000000000000)
theorem h256 : Model (fun x => f256 ((43/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(79924120421/12500000000000),(43556827829/20000000000000),(1504729053/100000000000000),(-928043/6250000000000)⟩
def e257 : ℝ := (2750609/25000000000000)
theorem h257 : Model (fun x => f257 ((43/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(185703641777643/50000000000000),(803727180177/100000000000000),(5553166743/100000000000000),(-5479873/10000000000000)⟩
def e258 : ℝ := (40604231/100000000000000)
theorem h258 : Model (fun x => f258 ((43/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2727121569269571/100000000000000),(803727180177/100000000000000),(5553166743/100000000000000),(-5479873/10000000000000)⟩
def e259 : ℝ := (5075529/12500000000000)
theorem h259 : Model (fun x => f259 ((43/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2744558592685971/100000000000000),(6748104388283/100000000000000),(6046856773/12500000000000),(-8718061/2000000000000)⟩
def e260 : ℝ := (17062427/5000000000000)
theorem h260 : Model (fun x => f260 ((43/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8026939545066923/100000000000000),(6748104388283/100000000000000),(6046856773/12500000000000),(-8718061/2000000000000)⟩
def e261 : ℝ := (341248541/100000000000000)
theorem h261 : Model (fun x => f261 ((43/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(2019565807922971/25000000000000),(4854530496163/20000000000000),(184164152049/100000000000000),(-711845973/50000000000000)⟩
def e262 : ℝ := (1229322813/100000000000000)
theorem h262 : Model (fun x => f262 ((43/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(13347310850739503/100000000000000),(4854530496163/20000000000000),(184164152049/100000000000000),(-711845973/50000000000000)⟩
def e263 : ℝ := (614661407/50000000000000)
theorem h263 : Model (fun x => f263 ((43/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(419770394284937/3125000000000),(5349617614809/10000000000000),(13720141753/3125000000000),(-264837751/10000000000000)⟩
def e264 : ℝ := (2715081997/100000000000000)
theorem h264 : Model (fun x => f264 ((43/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(15768366902832269/100000000000000),(5349617614809/10000000000000),(13720141753/3125000000000),(-264837751/10000000000000)⟩
def e265 : ℝ := (1357540999/50000000000000)
theorem h265 : Model (fun x => f265 ((43/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(15869188731247027/100000000000000),(8817922905061/10000000000000),(198907285159/25000000000000),(-1622782393/50000000000000)⟩
def e266 : ℝ := (2243222903/50000000000000)
theorem h266 : Model (fun x => f266 ((43/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(16271569683627979/100000000000000),(8817922905061/10000000000000),(198907285159/25000000000000),(-1622782393/50000000000000)⟩
def e267 : ℝ := (4486445807/100000000000000)
theorem h267 : Model (fun x => f267 ((43/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(16375608955214617/100000000000000),(124179938797179/100000000000000),(309399937169/25000000000000),(-2622818761/100000000000000)⟩
def e268 : ℝ := (1583346811/25000000000000)
theorem h268 : Model (fun x => f268 ((43/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(16357989907595569/100000000000000),(124179938797179/100000000000000),(309399937169/25000000000000),(-2622818761/100000000000000)⟩
def e269 : ℝ := (1266677449/20000000000000)
theorem h269 : Model (fun x => f269 ((43/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(8231290872006591/50000000000000),(32119808817889/20000000000000),(176210051171/10000000000000),(-504668189/100000000000000)⟩
def e270 : ℝ := (8207101449/100000000000000)
theorem h270 : Model (fun x => f270 ((43/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(3293183015469303/20000000000000),(32119808817889/20000000000000),(176210051171/10000000000000),(-504668189/100000000000000)⟩
def e271 : ℝ := (164142029/2000000000000)
theorem h271 : Model (fun x => f271 ((43/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(6580118897419/6250000000000),(3688701039069/10000000000000),(121758680067/20000000000000),(29734037/781250000000)⟩
def e272 : ℝ := (380365747/20000000000000)
theorem h272 : Model (fun x => f272 ((43/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(3165089817511/3125000000000),(109588317803/25000000000000),(3502999681/100000000000000),(-23333137/100000000000000)⟩
def e273 : ℝ := (11118157/50000000000000)
theorem h273 : Model (fun x => f273 ((43/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(25079924120421/12500000000000),(43556827829/20000000000000),(1504729053/100000000000000),(-928043/6250000000000)⟩
def e274 : ℝ := (2750609/25000000000000)
theorem h274 : Model (fun x => f274 ((43/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(25160103755443/6250000000000),(436960774751/50000000000000),(6512457787/100000000000000),(-53030513/100000000000000)⟩
def e275 : ℝ := (22120593/50000000000000)
theorem h275 : Model (fun x => f275 ((43/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(80769727110199/10000000000000),(526029267569/20000000000000),(21027280549/100000000000000),(-138841973/100000000000000)⟩
def e276 : ℝ := (133399777/100000000000000)
theorem h276 : Model (fun x => f276 ((43/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1620558901720721/100000000000000),(7036146195067/100000000000000),(15017676277/25000000000000),(-156566741/50000000000000)⟩
def e277 : ℝ := (178742451/50000000000000)
theorem h277 : Model (fun x => f277 ((43/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(82067431656209/5000000000000),(7115092027049/50000000000000),(9278292927/6250000000000),(-9273987/5000000000000)⟩
def e278 : ℝ := (726516457/100000000000000)
theorem h278 : Model (fun x => f278 ((43/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(12579924120421/1562500000000),(43556827829/2500000000000),(1504729053/12500000000000),(-928043/781250000000)⟩
def e279 : ℝ := (2750609/3125000000000)
theorem h279 : Model (fun x => f279 ((43/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(28324938058353/3125000000000),(545156596093/25000000000000),(3108166421/20000000000000),(-142122641/100000000000000)⟩
def e280 : ℝ := (55127901/50000000000000)
theorem h280 : Model (fun x => f280 ((43/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(31449938058353/3125000000000),(545156596093/25000000000000),(3108166421/20000000000000),(-142122641/100000000000000)⟩
def e281 : ℝ := (55127901/50000000000000)
theorem h281 : Model (fun x => f281 ((43/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(16518500110053703/100000000000000),(35800794322549/20000000000000),(2059411281107/100000000000000),(1249295017/100000000000000)⟩
def e282 : ℝ := (572161149/6250000000000)
theorem h282 : Model (fun x => f282 ((43/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(121076368113/20000000000000),(-131205319/2000000000000),(-2191983/50000000000000),(81961/10000000000000)⟩
def e283 : ℝ := (87733/25000000000000)
theorem h283 : Model (fun x => f283 ((43/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (326748526465729/2000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(15933937957/2500000000000),(5410012241/2500000000000),(630511593/50000000000000),(-17652109/100000000000000)⟩
def e284 : ℝ := (76063/625000000000)
theorem h284 : Model (fun x => f284 ((43/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(101278785926737/50000000000000),(435568278291/50000000000000),(1504729053/25000000000000),(-928043/1562500000000)⟩
def e285 : ℝ := (2200487/5000000000000)
theorem h285 : Model (fun x => f285 ((43/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(24841167324111/50000000000000),(-21502563089/20000000000000),(-510176631/100000000000000),(2510457/25000000000000)⟩
def e286 : ℝ := (5485497/100000000000000)
theorem h286 : Model (fun x => f286 ((43/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (100420078244047/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(20127066140711/20000000000000),(215025630887/100000000000000),(51017663/5000000000000),(-10041829/50000000000000)⟩
def e287 : ℝ := (16596783/50000000000000)
theorem h287 : Model (fun x => f287 ((43/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(127066140711/20000000000000),(215025630887/100000000000000),(51017663/5000000000000),(-10041829/50000000000000)⟩
def e288 : ℝ := (16596783/50000000000000)
theorem h288 : Model (fun x => f288 ((43/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(371392291882167/100000000000000),(79354697113/10000000000000),(3765589411/100000000000000),(-37059131/50000000000000)⟩
def e289 : ℝ := (30625017/25000000000000)
theorem h289 : Model (fun x => f289 ((43/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(681776644399113/25000000000000),(79354697113/10000000000000),(3765589411/100000000000000),(-37059131/50000000000000)⟩
def e290 : ℝ := (122500069/100000000000000)
theorem h290 : Model (fun x => f290 ((43/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(274443272300259/10000000000000),(3331283371061/50000000000000),(6664392721/20000000000000),(-18940561/3125000000000)⟩
def e291 : ℝ := (128664191/12500000000000)
theorem h291 : Model (fun x => f291 ((43/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4013406837691771/50000000000000),(3331283371061/50000000000000),(6664392721/20000000000000),(-18940561/3125000000000)⟩
def e292 : ℝ := (1029313529/100000000000000)
theorem h292 : Model (fun x => f292 ((43/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(1615562097436081/20000000000000),(2995575352487/12500000000000),(32440437363/25000000000000),(-1041197003/50000000000000)⟩
def e293 : ℝ := (741400053/20000000000000)
theorem h293 : Model (fun x => f293 ((43/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1668357263278503/12500000000000),(2995575352487/12500000000000),(32440437363/25000000000000),(-1041197003/50000000000000)⟩
def e294 : ℝ := (1853500133/50000000000000)
theorem h294 : Model (fun x => f294 ((43/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1343165479373681/10000000000000),(10563204629221/20000000000000),(63660261177/20000000000000),(-1063154201/25000000000000)⟩
def e295 : ℝ := (8184873751/100000000000000)
theorem h295 : Model (fun x => f295 ((43/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3153473815890219/20000000000000),(10563204629221/20000000000000),(63660261177/20000000000000),(-1063154201/25000000000000)⟩
def e296 : ℝ := (1023109219/12500000000000)
theorem h296 : Model (fun x => f296 ((43/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(3173508803271137/20000000000000),(2176386609873/2500000000000),(74346802901/12500000000000),(-6222960061/100000000000000)⟩
def e297 : ℝ := (13522564853/100000000000000)
theorem h297 : Model (fun x => f297 ((43/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(16269924968736637/100000000000000),(2176386609873/2500000000000),(74346802901/12500000000000),(-6222960061/100000000000000)⟩
def e298 : ℝ := (6761282427/50000000000000)
theorem h298 : Model (fun x => f298 ((43/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(8186646398754191/50000000000000),(12259306329821/10000000000000),(95175547909/10000000000000),(-36814509/500000000000)⟩
def e299 : ℝ := (19092344893/100000000000000)
theorem h299 : Model (fun x => f299 ((43/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(8177836874944667/50000000000000),(12259306329821/10000000000000),(95175547909/10000000000000),(-36814509/500000000000)⟩
def e300 : ℝ := (9546172447/50000000000000)
theorem h300 : Model (fun x => f300 ((43/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(8229793183497833/50000000000000),(158540825336291/100000000000000),(694147215977/50000000000000),(-1479419523/20000000000000)⟩
def e301 : ℝ := (24755955361/100000000000000)
theorem h301 : Model (fun x => f301 ((43/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(16462919700328999/100000000000000),(158540825336291/100000000000000),(694147215977/50000000000000),(-1479419523/20000000000000)⟩
def e302 : ℝ := (12377977681/50000000000000)
theorem h302 : Model (fun x => f302 ((43/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(52296991778897/50000000000000),(36406755489083/100000000000000),(32356475533/6250000000000),(624756409/50000000000000)⟩
def e303 : ℝ := (5762435103/100000000000000)
theorem h303 : Model (fun x => f303 ((43/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(50637348929069/50000000000000),(432783509481/100000000000000),(1258015987/50000000000000),(-3603447/10000000000000)⟩
def e304 : ℝ := (261831/390625000000)
theorem h304 : Model (fun x => f304 ((43/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(40127066140711/20000000000000),(215025630887/100000000000000),(51017663/5000000000000),(-10041829/50000000000000)⟩
def e305 : ℝ := (16596783/50000000000000)
theorem h305 : Model (fun x => f305 ((43/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(12579542477039/3125000000000),(172566954251/20000000000000),(2278369247/50000000000000),(-38100893/50000000000000)⟩
def e306 : ℝ := (33353967/25000000000000)
theorem h306 : Model (fun x => f306 ((43/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(807648212793643/100000000000000),(2596727095099/100000000000000),(15105127953/100000000000000),(-215131421/100000000000000)⟩
def e307 : ℝ := (20108357/5000000000000)
theorem h307 : Model (fun x => f307 ((43/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1620427662659877/100000000000000),(6946602659627/100000000000000),(11032679277/25000000000000),(-534859257/100000000000000)⟩
def e308 : ℝ := (53877399/5000000000000)
theorem h308 : Model (fun x => f308 ((43/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(820541609684239/50000000000000),(7024047281001/50000000000000),(115527479301/100000000000000),(-759820407/100000000000000)⟩
def e309 : ℝ := (1095275319/50000000000000)
theorem h309 : Model (fun x => f309 ((43/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(20127066140711/2500000000000),(215025630887/12500000000000),(51017663/625000000000),(-10041829/6250000000000)⟩
def e310 : ℝ := (16596783/6250000000000)
theorem h310 : Model (fun x => f310 ((43/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(453178671743289/50000000000000),(2152988556577/100000000000000),(5339429027/50000000000000),(-98351867/50000000000000)⟩
def e311 : ℝ := (20786079/6250000000000)
theorem h311 : Model (fun x => f311 ((43/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(503178671743289/50000000000000),(2152988556577/100000000000000),(5339429027/50000000000000),(-98351867/50000000000000)⟩
def e312 : ℝ := (20786079/6250000000000)
theorem h312 : Model (fun x => f312 ((43/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(8257580745420313/50000000000000),(88353182580777/50000000000000),(1640322087571/100000000000000),(-1721777737/25000000000000)⟩
def e313 : ℝ := (1381455853/5000000000000)
theorem h313 : Model (fun x => f313 ((43/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(605504221411/100000000000000),(-6478680219/100000000000000),(917957/10000000000000),(199441/25000000000000)⟩
def e314 : ℝ := (65461/6250000000000)
theorem h314 : Model (fun x => f314 ((43/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (16336780287363493/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(79165123223/12500000000000),(106834065821/50000000000000),(157128243/20000000000000),(-681191/3125000000000)⟩
def e315 : ℝ := (2313079/6250000000000)
theorem h315 : Model (fun x => f315 ((43/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(9927175813/781250000000),(215034310641/50000000000000),(2046664401/100000000000000),(-39450221/100000000000000)⟩
def e316 : ℝ := (3073709/6250000000000)
theorem h316 : Model (fun x => f316 ((43/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(6368889919823/100000000000000),(2139447267489/100000000000000),(4820196083/100000000000000),(-216395871/100000000000000)⟩
def e317 : ℝ := (247630401/100000000000000)
theorem h317 : Model (fun x => f317 ((43/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(2962274381313/50000000000000),(926201650429/50000000000000),(-38595243199/100000000000000),(69626531/10000000000000)⟩
def e318 : ℝ := (256303009/100000000000000)
theorem h318 : Model (fun x => f318 ((43/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-17282701625157/100000000000000),(-5235919478571/100000000000000),(20176157649/12500000000000),(-2099707073/50000000000000)⟩
def e319 : ℝ := (14214293/3125000000000)
theorem h319 : Model (fun x => f319 ((43/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((43/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-20339/1600),(-473/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((43/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((43/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(4171/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((43/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(146501/1600),(1467/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((43/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((43/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(319301/1600),(1467/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((43/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1596505/32),(7335/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((43/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((43/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(82674130670754209/10000000000000),(3522720414834859/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (107649/100000000000000)
theorem h329 : Model (fun x => f329 ((43/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(12095682069/100000000000000),(-25769673/25000000000000),(386943/25000000000000),(-3779/20000000000000)⟩
def e330 : ℝ := (253/100000000000000)
theorem h330 : Model (fun x => f330 ((43/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (409825058130993823/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(301731514087013/50000000000000),(402437774399/100000000000000),(9174962857/100000000000000),(-13990771/25000000000000)⟩
def e331 : ℝ := (12046837/50000000000000)
theorem h331 : Model (fun x => f331 ((43/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((43/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(403/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((43/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((43/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((43/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(465806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((43/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((43/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((43/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2066547375096427/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1007/100000000000000)
theorem h339 : Model (fun x => f339 ((43/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3564193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((43/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((43/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((43/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1004226312451657/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1007/100000000000000)
theorem h343 : Model (fun x => f343 ((43/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(1244739342617/25000000000000),(-174617259/2500000000000),(612401/6250000000000),(-6873/50000000000000)⟩
def e344 : ℝ := (3/12500000000000)
theorem h344 : Model (fun x => f344 ((43/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1002817541633913/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(6430782052911/6250000000000),(960113210447/100000000000000),(-1346887123/100000000000000),(1889461/100000000000000)⟩
def e345 : ℝ := (901/25000000000000)
theorem h345 : Model (fun x => f345 ((43/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(12680782052911/6250000000000),(960113210447/100000000000000),(-1346887123/100000000000000),(1889461/100000000000000)⟩
def e346 : ℝ := (901/25000000000000)
theorem h346 : Model (fun x => f346 ((43/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(12680782052911/12500000000000),(480056605223/100000000000000),(-336721781/50000000000000),(94473/10000000000000)⟩
def e347 : ℝ := (451/25000000000000)
theorem h347 : Model (fun x => f347 ((43/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(180782052911/12500000000000),(480056605223/100000000000000),(-336721781/50000000000000),(94473/10000000000000)⟩
def e348 : ℝ := (451/25000000000000)
theorem h348 : Model (fun x => f348 ((43/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(187192496971543/50000000000000),(221454683957/12500000000000),(-310665929/12500000000000),(3486503/100000000000000)⟩
def e349 : ℝ := (333/5000000000000)
theorem h349 : Model (fun x => f349 ((43/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2730099279657371/100000000000000),(221454683957/12500000000000),(-310665929/12500000000000),(3486503/100000000000000)⟩
def e350 : ℝ := (6661/100000000000000)
theorem h350 : Model (fun x => f350 ((43/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(553916703170311/20000000000000),(14903281813527/100000000000000),(-3100521693/25000000000000),(1366759/25000000000000)⟩
def e351 : ℝ := (53167/50000000000000)
theorem h351 : Model (fun x => f351 ((43/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8051964468232507/100000000000000),(14903281813527/100000000000000),(-3100521693/25000000000000),(1366759/25000000000000)⟩
def e352 : ℝ := (21267/20000000000000)
theorem h352 : Model (fun x => f352 ((43/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(8168416521555187/100000000000000),(10754561752799/20000000000000),(2368649833/50000000000000),(-39143401/50000000000000)⟩
def e353 : ℝ := (126157/25000000000000)
theorem h353 : Model (fun x => f353 ((43/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(6718732070301403/50000000000000),(10754561752799/20000000000000),(2368649833/50000000000000),(-39143401/50000000000000)⟩
def e354 : ℝ := (504629/100000000000000)
theorem h354 : Model (fun x => f354 ((43/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(2726360865772659/20000000000000),(59528967823081/50000000000000),(172451996301/100000000000000),(-145929537/50000000000000)⟩
def e355 : ℝ := (429297/50000000000000)
theorem h355 : Model (fun x => f355 ((43/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(798375930728879/5000000000000),(59528967823081/50000000000000),(172451996301/100000000000000),(-145929537/50000000000000)⟩
def e356 : ℝ := (171719/20000000000000)
theorem h356 : Model (fun x => f356 ((43/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(3239689975636123/20000000000000),(19743294648737/10000000000000),(127791870473/20000000000000),(-11915097/10000000000000)⟩
def e357 : ℝ := (81457/3125000000000)
theorem h357 : Model (fun x => f357 ((43/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(16600830830561567/100000000000000),(19743294648737/10000000000000),(127791870473/20000000000000),(-11915097/10000000000000)⟩
def e358 : ℝ := (20853/800000000000)
theorem h358 : Model (fun x => f358 ((43/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(8420460706383869/50000000000000),(279981718081637/100000000000000),(92762063567/6250000000000),(886862969/50000000000000)⟩
def e359 : ℝ := (1494141/25000000000000)
theorem h359 : Model (fun x => f359 ((43/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(1682330236514869/10000000000000),(279981718081637/100000000000000),(92762063567/6250000000000),(886862969/50000000000000)⟩
def e360 : ℝ := (1195313/20000000000000)
theorem h360 : Model (fun x => f360 ((43/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(8533305228106907/50000000000000),(182396172941979/50000000000000),(2736433538289/100000000000000),(1439552221/20000000000000)⟩
def e361 : ℝ := (1891789/25000000000000)
theorem h361 : Model (fun x => f361 ((43/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(17069943789547147/100000000000000),(182396172941979/50000000000000),(2736433538289/100000000000000),(1439552221/20000000000000)⟩
def e362 : ℝ := (7567157/100000000000000)
theorem h362 : Model (fun x => f362 ((43/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(30859394813497/12500000000000),(1362831646931/1562500000000),(418957290023/25000000000000),(5472561171/50000000000000)⟩
def e363 : ℝ := (2506797/12500000000000)
theorem h363 : Model (fun x => f363 ((43/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(20582685884599/20000000000000),(486999454711/50000000000000),(234544219/25000000000000),(-909807/20000000000000)⟩
def e364 : ℝ := (17299/100000000000000)
theorem h364 : Model (fun x => f364 ((43/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(25180782052911/12500000000000),(480056605223/100000000000000),(-336721781/50000000000000),(94473/10000000000000)⟩
def e365 : ℝ := (451/25000000000000)
theorem h365 : Model (fun x => f365 ((43/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(405805942269571/100000000000000),(483528029967/25000000000000),(-51088781/12500000000000),(-106383/4000000000000)⟩
def e366 : ℝ := (20907/100000000000000)
theorem h366 : Model (fun x => f366 ((43/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(8174808790453/1000000000000),(1168858938151/20000000000000),(5728627497/100000000000000),(-8255519/50000000000000)⟩
def e367 : ℝ := (11569/20000000000000)
theorem h367 : Model (fun x => f367 ((43/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1646784627812943/100000000000000),(7848741912581/50000000000000),(17045377989/50000000000000),(-37395253/100000000000000)⟩
def e368 : ℝ := (38891/20000000000000)
theorem h368 : Model (fun x => f368 ((43/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1694762535693003/100000000000000),(32194483253021/100000000000000),(50856759983/25000000000000),(22869763/6250000000000)⟩
def e369 : ℝ := (1250003/100000000000000)
theorem h369 : Model (fun x => f369 ((43/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(12680782052911/1562500000000),(480056605223/12500000000000),(-336721781/6250000000000),(94473/1250000000000)⟩
def e370 : ℝ := (451/3125000000000)
theorem h370 : Model (fun x => f370 ((43/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(914483480809299/100000000000000),(2407225875603/50000000000000),(-222468581/5000000000000),(601761/20000000000000)⟩
def e371 : ℝ := (31731/100000000000000)
theorem h371 : Model (fun x => f371 ((43/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1014483480809299/100000000000000),(2407225875603/50000000000000),(-222468581/5000000000000),(601761/20000000000000)⟩
def e372 : ℝ := (31731/100000000000000)
theorem h372 : Model (fun x => f372 ((43/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(3438617192710063/20000000000000),(408201238912269/100000000000000),(1769157647543/50000000000000),(12124596069/100000000000000)⟩
def e373 : ℝ := (2854229/12500000000000)
theorem h373 : Model (fun x => f373 ((43/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(290814575731/50000000000000),(-1380914053/10000000000000),(8326419/4000000000000),(-502089/20000000000000)⟩
def e374 : ℝ := (14173/50000000000000)
theorem h374 : Model (fun x => f374 ((43/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (16781334261913059/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(897436181/62500000000),(473212735637/100000000000000),(-891747081/50000000000000),(760487/10000000000000)⟩
def e375 : ℝ := (223427/50000000000000)
theorem h375 : Model (fun x => f375 ((43/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(6430782052911/3125000000000),(960113210447/50000000000000),(-1346887123/50000000000000),(1889461/50000000000000)⟩
def e376 : ℝ := (901/12500000000000)
theorem h376 : Model (fun x => f376 ((43/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(4928718097923/10000000000000),(-233233217431/100000000000000),(715439319/50000000000000),(-1755679/20000000000000)⟩
def e377 : ℝ := (54423/100000000000000)
theorem h377 : Model (fun x => f377 ((43/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (201931050855941/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(50712819020769/50000000000000),(466466434861/100000000000000),(-2861757279/100000000000000),(17556787/100000000000000)⟩
def e378 : ℝ := (83207/25000000000000)
theorem h378 : Model (fun x => f378 ((43/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(712819020769/50000000000000),(466466434861/100000000000000),(-2861757279/100000000000000),(17556787/100000000000000)⟩
def e379 : ℝ := (83207/25000000000000)
theorem h379 : Model (fun x => f379 ((43/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(46788612787019/12500000000000),(172148327151/10000000000000),(-5280623551/50000000000000),(8099113/12500000000000)⟩
def e380 : ℝ := (1228297/100000000000000)
theorem h380 : Model (fun x => f380 ((43/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2730023188010437/100000000000000),(172148327151/10000000000000),(-5280623551/50000000000000),(8099113/12500000000000)⟩
def e381 : ℝ := (614149/50000000000000)
theorem h381 : Model (fun x => f381 ((43/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1384471718560761/50000000000000),(7240333613949/50000000000000),(-80808307917/100000000000000),(223245813/50000000000000)⟩
def e382 : ℝ := (5627027/50000000000000)
theorem h382 : Model (fun x => f382 ((43/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(4025662194751237/50000000000000),(7240333613949/50000000000000),(-80808307917/100000000000000),(223245813/50000000000000)⟩
def e383 : ℝ := (2250811/20000000000000)
theorem h383 : Model (fun x => f383 ((43/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(31898855987683/390625000000),(52243834967373/100000000000000),(-122411125753/50000000000000),(134383209/12500000000000)⟩
def e384 : ℝ := (45277503/100000000000000)
theorem h384 : Model (fun x => f384 ((43/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(13435154751894467/100000000000000),(52243834967373/100000000000000),(-122411125753/50000000000000),(134383209/12500000000000)⟩
def e385 : ℝ := (707461/1562500000000)
theorem h385 : Model (fun x => f385 ((43/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(6813345714488487/50000000000000),(57829565171123/50000000000000),(-97273523827/25000000000000),(812068341/100000000000000)⟩
def e386 : ℝ := (112293481/100000000000000)
theorem h386 : Model (fun x => f386 ((43/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(15962405714691259/100000000000000),(57829565171123/50000000000000),(-97273523827/25000000000000),(812068341/100000000000000)⟩
def e387 : ℝ := (56146741/50000000000000)
theorem h387 : Model (fun x => f387 ((43/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(16189971842904533/100000000000000),(38353455151657/20000000000000),(-155967727147/50000000000000),(-1498745869/100000000000000)⟩
def e388 : ℝ := (40651141/20000000000000)
theorem h388 : Model (fun x => f388 ((43/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(3318470559057097/20000000000000),(38353455151657/20000000000000),(-155967727147/50000000000000),(-1498745869/100000000000000)⟩
def e389 : ℝ := (101627853/50000000000000)
theorem h389 : Model (fun x => f389 ((43/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(4207224922180317/25000000000000),(271898939536443/100000000000000),(103314585787/100000000000000),(-346876043/6250000000000)⟩
def e390 : ℝ := (298586667/100000000000000)
theorem h390 : Model (fun x => f390 ((43/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(840564032055111/5000000000000),(271898939536443/100000000000000),(103314585787/100000000000000),(-346876043/6250000000000)⟩
def e391 : ℝ := (74646667/25000000000000)
theorem h391 : Model (fun x => f391 ((43/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(8525474326595743/50000000000000),(354194215714039/100000000000000),(178401344013/20000000000000),(-2494194733/25000000000000)⟩
def e392 : ℝ := (380171889/100000000000000)
theorem h392 : Model (fun x => f392 ((43/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(17054281986524819/100000000000000),(354194215714039/100000000000000),(178401344013/20000000000000),(-2494194733/25000000000000)⟩
def e393 : ℝ := (38017189/10000000000000)
theorem h393 : Model (fun x => f393 ((43/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(12156616585553/5000000000000),(8460202865383/10000000000000),(147107720191/12500000000000),(-1561657799/50000000000000)⟩
def e394 : ℝ := (9433953/12500000000000)
theorem h394 : Model (fun x => f394 ((43/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(10287160052133/10000000000000),(473116557807/50000000000000),(-3629201811/100000000000000),(2228973/25000000000000)⟩
def e395 : ℝ := (924971/100000000000000)
theorem h395 : Model (fun x => f395 ((43/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(100712819020769/50000000000000),(466466434861/100000000000000),(-2861757279/100000000000000),(17556787/100000000000000)⟩
def e396 : ℝ := (83207/25000000000000)
theorem h396 : Model (fun x => f396 ((43/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(202861438302203/50000000000000),(234895748167/12500000000000),(-9352716369/100000000000000),(22014733/50000000000000)⟩
def e397 : ℝ := (1590627/100000000000000)
theorem h397 : Model (fun x => f397 ((43/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(408614946440453/50000000000000),(2838841556867/50000000000000),(-10841946999/50000000000000),(31257041/50000000000000)⟩
def e398 : ℝ := (5373909/100000000000000)
theorem h398 : Model (fun x => f398 ((43/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(823055263000771/50000000000000),(3049682516751/20000000000000),(-40579571781/100000000000000),(5769103/100000000000000)⟩
def e399 : ℝ := (242237/1562500000000)
theorem h399 : Model (fun x => f399 ((43/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(169338024444787/10000000000000),(31262328995639/100000000000000),(10700000369/25000000000000),(-784672807/100000000000000)⟩
def e400 : ℝ := (17176873/50000000000000)
theorem h400 : Model (fun x => f400 ((43/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(50712819020769/6250000000000),(466466434861/12500000000000),(-2861757279/12500000000000),(17556787/12500000000000)⟩
def e401 : ℝ := (83207/3125000000000)
theorem h401 : Model (fun x => f401 ((43/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(457138352426817/50000000000000),(2338982297251/50000000000000),(-26523260043/100000000000000),(37342547/25000000000000)⟩
def e402 : ℝ := (717519/20000000000000)
theorem h402 : Model (fun x => f402 ((43/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(507138352426817/50000000000000),(2338982297251/50000000000000),(-26523260043/100000000000000),(37342547/25000000000000)⟩
def e403 : ℝ := (717519/20000000000000)
theorem h403 : Model (fun x => f403 ((43/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(4293890336007067/25000000000000),(49537781085379/12500000000000),(1447411480729/100000000000000),(-1464871017/12500000000000)⟩
def e404 : ℝ := (82713663/20000000000000)
theorem h404 : Model (fun x => f404 ((43/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(582222601037/100000000000000),(-2686795749/20000000000000),(260905609/100000000000000),(-112267/2500000000000)⟩
def e405 : ℝ := (44723/50000000000000)
theorem h405 : Model (fun x => f405 ((43/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (2097224943916007/12500000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(28311427713/2000000000000),(229954892997/50000000000000),(-1939558749/50000000000000),(16764567/50000000000000)⟩
def e406 : ℝ := (222843/20000000000000)
theorem h406 : Model (fun x => f406 ((43/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(11405877101/400000000000),(933122521631/100000000000000),(-283130583/5000000000000),(10283501/25000000000000)⟩
def e407 : ℝ := (1561069/100000000000000)
theorem h407 : Model (fun x => f407 ((43/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(137660502687/800000000000),(5642524815097/100000000000000),(-15077454521/50000000000000),(77364473/25000000000000)⟩
def e408 : ℝ := (5611649/50000000000000)
theorem h408 : Model (fun x => f408 ((43/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(8003517598081/50000000000000),(1219150915161/25000000000000),(-35365116409/25000000000000),(3577646077/100000000000000)⟩
def e409 : ℝ := (21091597/20000000000000)
theorem h409 : Model (fun x => f409 ((43/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-255133285799/20000000000000),(-359315817927/100000000000000),(4987198889/25000000000000),(-621768069/100000000000000)⟩
def e410 : ℝ := (560315361/100000000000000)
theorem h410 : Model (fun x => f410 ((43/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(277109846679687/100000000000000),(7279083251953/25000000000000),(123883/10240000),(2537/10240000)⟩
def e411 : ℝ := (250000001/100000000000000)
theorem h411 : Model (fun x => f411 ((43/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(26569/1600),(163/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((43/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(4330747/64000),(79707/64000),(489/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((43/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(1171965465994643/6250000000000),(578840103022971/25000000000000),(120243718728209/100000000000000),(852500270111/25000000000000)⟩
def e414 : ℝ := (2319727407/4000000000000)
theorem h414 : Model (fun x => f414 ((43/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(33330760277/6250000000000),(-65848973447/100000000000000),(4711053559/100000000000000),(-128213791/50000000000000)⟩
def e415 : ℝ := (9271197/50000000000000)
theorem h415 : Model (fun x => f415 ((43/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (509761729088393/3125000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1317861625577/100000000000000),(193004539231/50000000000000),(-4045085207/25000000000000),(486525169/100000000000000)⟩
def e416 : ℝ := (974241/625000000000)
theorem h416 : Model (fun x => f416 ((43/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(21097598291/50000000000000),(5338652107/20000000000000),(471056841/12500000000000),(-1352429/1000000000000)⟩
def e417 : ℝ := (716193921/100000000000000)
theorem h417 : Model (fun x => f417 ((43/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((43/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((42735154237/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (21/20) (11/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (21/20) (11/10) ≤ (44167542079/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(43/40)-(1/40)) (by norm_num : ((43/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel1


noncomputable section
namespace Hf4Quad.Panel2
open Hf4Quad.Dag

def p0 : Cubic := ⟨(9/8),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((9/8)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((9/8)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((9/8)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((9/8)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(197142857142857/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((9/8)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-197142857142857/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((9/8)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-52857142857143/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((9/8)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((9/8)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(81/64),(9/160),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((9/8)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(30642857142857/20000000000000),(6809523809523/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((9/8)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-30642857142857/20000000000000),(-6809523809523/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((9/8)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-258928571428571/100000000000000),(-447619047619/4000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((9/8)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((9/8)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(729/512),(243/2560),(27/12800),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((9/8)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(142047/10240),(47349/51200),(5261/256000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/100000000000000)
theorem h14 : Model (fun x => f14 ((9/8)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-142047/10240),(-47349/51200),(-5261/256000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/100000000000000)
theorem h15 : Model (fun x => f15 ((9/8)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1646106305803571/100000000000000),(-4146759672619/4000000000000),(-2130739500661/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/20000000000000)
theorem h16 : Model (fun x => f16 ((9/8)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((9/8)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(6561/4096),(729/5120),(243/51200),(9/128000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((9/8)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(223744419642857/50000000000000),(7955357142857/20000000000000),(662946428571/50000000000000),(9821428571/50000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((9/8)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1198617466517857/100000000000000),(-6389220610119/10000000000000),(-804846643519/100000000000000),(4420056217/100000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((9/8)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((9/8)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(22525405883789/12500000000000),(5005645751953/25000000000000),(729/81920),(81/409600)⟩
def e22 : ℝ := (110351563/50000000000000)
theorem h22 : Model (fun x => f22 ((9/8)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(586995391845701/50000000000000),(16305427551269/12500000000000),(2898742675781/50000000000000),(32208251953/25000000000000)⟩
def e23 : ℝ := (718919999/50000000000000)
theorem h23 : Model (fun x => f23 ((9/8)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(-4925336565291/20000000000000),(33275607154481/50000000000000),(4992638708043/100000000000000),(133253064029/100000000000000)⟩
def e24 : ℝ := (154696699/10000000000000)
theorem h24 : Model (fun x => f24 ((9/8)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((9/8)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(202728652954101/100000000000000),(13515243530273/50000000000000),(300338745117/20000000000000),(22247314453/50000000000000)⟩
def e26 : ℝ := (374096681/50000000000000)
theorem h26 : Model (fun x => f26 ((9/8)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(455227726527621/100000000000000),(60697030203681/100000000000000),(674411446707/20000000000000),(99912806919/100000000000000)⟩
def e27 : ℝ := (52502193/3125000000000)
theorem h27 : Model (fun x => f27 ((9/8)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(215300521850583/50000000000000),(127248244512643/100000000000000),(4182347970789/50000000000000),(58291467737/25000000000000)⟩
def e28 : ℝ := (1613518583/50000000000000)
theorem h28 : Model (fun x => f28 ((9/8)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((9/8)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(228069734573363/100000000000000),(17738757133483/50000000000000),(591291904449/25000000000000),(43799400329/50000000000000)⟩
def e30 : ℝ := (493197023/25000000000000)
theorem h30 : Model (fun x => f30 ((9/8)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(5412131002971/10000000000000),(1683774089813/20000000000000),(561258029937/100000000000000),(20787334441/100000000000000)⟩
def e31 : ℝ := (468145749/100000000000000)
theorem h31 : Model (fun x => f31 ((9/8)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(121180588432719/25000000000000),(33916778740427/25000000000000),(1785190794303/20000000000000),(253953205389/100000000000000)⟩
def e32 : ℝ := (739036583/20000000000000)
theorem h32 : Model (fun x => f32 ((9/8)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((9/8)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(173745/64),(3861/32),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((9/8)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((9/8)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(19881/4),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((9/8)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(491841/64),(36977/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((9/8)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((9/8)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(637761/64),(36977/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((9/8)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-637761/64),(-36977/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((9/8)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((9/8)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(17/8),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((9/8)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(289/64),(17/160),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((9/8)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((9/8)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(30345/32),(357/16),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((9/8)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(26363486571/25000000000000),(-99250773/4000000000000),(8757421/20000000000000),(-686857/100000000000000)⟩
def e46 : ℝ := (5223/50000000000000)
theorem h46 : Model (fun x => f46 ((9/8)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (74067/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1050850222437971/100000000000000),(354821520061/100000000000000),(-855306659/20000000000000),(51518791/100000000000000)⟩
def e47 : ℝ := (207478371/100000000000000)
theorem h47 : Model (fun x => f47 ((9/8)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((9/8)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(25/8),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((9/8)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((9/8)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((9/8)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(20833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((9/8)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(40833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((9/8)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((9/8)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(25520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((9/8)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((9/8)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(535937499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((9/8)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((9/8)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((9/8)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(5582682291663/12500000000000),(4557291666659/50000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (9/10000000000000)
theorem h60 : Model (fun x => f60 ((9/8)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(104210069444441/100000000000000),(850694444443/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/10000000000000)
theorem h61 : Model (fun x => f61 ((9/8)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((9/8)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(25520833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((9/8)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1125043402777761/100000000000000),(5017361111103/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (1/2000000000000)
theorem h64 : Model (fun x => f64 ((9/8)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1225043402777761/100000000000000),(5017361111103/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (1/2000000000000)
theorem h65 : Model (fun x => f65 ((9/8)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(547122248896479/100000000000000),(2847460711439/2500000000000),(226179334851/25000000000000),(496871383/25000000000000)⟩
def e66 : ℝ := (158523/25000000000000)
theorem h66 : Model (fun x => f66 ((9/8)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(50520833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((9/8)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(81675347222221/20000000000000),(67361111111/4000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (9/50000000000000)
theorem h68 : Model (fun x => f68 ((9/8)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(165052264178237/20000000000000),(255235460069/5000000000000),(1052517361/10000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (7/12500000000000)
theorem h69 : Model (fun x => f69 ((9/8)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(4515188298132639/100000000000000),(30246521092043/3125000000000),(1667256423719/12500000000000),(37306361833/50000000000000)⟩
def e70 : ℝ := (52614527/25000000000000)
theorem h70 : Model (fun x => f70 ((9/8)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((9/8)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2188411458333261/12500000000000),(17864583333303/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1250000000000)
theorem h72 : Model (fun x => f72 ((9/8)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(36473524305531/10000000000000),(3796223958327/5000000000000),(601562499997/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (751/100000000000000)
theorem h73 : Model (fun x => f73 ((9/8)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(120400755383757/4000000000000),(32259701658123/5000000000000),(8878575525123/100000000000000),(12188700293/25000000000000)⟩
def e74 : ℝ := (32755529/25000000000000)
theorem h74 : Model (fun x => f74 ((9/8)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(1881301795681641/25000000000000),(403270677026959/25000000000000),(177733015319/800000000000),(61683762419/50000000000000)⟩
def e75 : ℝ := (10671257/3125000000000)
theorem h75 : Model (fun x => f75 ((9/8)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((9/8)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(729470486111087/12500000000000),(5954861111101/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1250000000000)
theorem h77 : Model (fun x => f77 ((9/8)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(43402777777/100000000000000),(17361111111/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((9/8)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(904224537/100000000000000),(271267361/50000000000000),(1695421/1562500000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/50000000000000)
theorem h79 : Model (fun x => f79 ((9/8)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(13192102251/25000000000000),(32091807913/100000000000000),(263661827/4000000000000),(474366221/100000000000000)⟩
def e80 : ℝ := (1779373/50000000000000)
theorem h80 : Model (fun x => f80 ((9/8)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(53318079931/50000000000000),(8134007941/12500000000000),(3363532771/25000000000000),(197215969/20000000000000)⟩
def e81 : ℝ := (2295747/25000000000000)
theorem h81 : Model (fun x => f81 ((9/8)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(3762656909443213/50000000000000),(403286945042841/25000000000000),(22230081045959/100000000000000),(124353604683/100000000000000)⟩
def e82 : ℝ := (87665803/25000000000000)
theorem h82 : Model (fun x => f82 ((9/8)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(18838011/100000000000000),(1883801/12500000000000),(2260561/50000000000000),(9419/1562500000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((9/8)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(196229/50000000000000),(196229/50000000000000),(156983/100000000000000),(7849/25000000000000)⟩
def e84 : ℝ := (817/25000000000000)
theorem h84 : Model (fun x => f84 ((9/8)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(511/6250000000000),(9811/100000000000000),(981/20000000000000),(327/25000000000000)⟩
def e85 : ℝ := (43/20000000000000)
theorem h85 : Model (fun x => f85 ((9/8)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(17/10000000000000),(119/50000000000000),(143/100000000000000),(47/100000000000000)⟩
def e86 : ℝ := (13/100000000000000)
theorem h86 : Model (fun x => f86 ((9/8)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(51/10000000000000),(357/50000000000000),(429/100000000000000),(141/100000000000000)⟩
def e87 : ℝ := (39/100000000000000)
theorem h87 : Model (fun x => f87 ((9/8)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-51/10000000000000),(-357/50000000000000),(-429/100000000000000),(-141/100000000000000)⟩
def e88 : ℝ := (39/100000000000000)
theorem h88 : Model (fun x => f88 ((9/8)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(1881328454721479/25000000000000),(32262955603413/2000000000000),(2223008104553/10000000000000),(62176802271/50000000000000)⟩
def e89 : ℝ := (350663251/100000000000000)
theorem h89 : Model (fun x => f89 ((9/8)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2188411458333261/10000000000000),(17864583333303/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1000000000000)
theorem h90 : Model (fun x => f90 ((9/8)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(208464448245949/12500000000000),(13754355348163/100000000000000),(21269621671/50000000000000),(29236593/50000000000000)⟩
def e91 : ℝ := (30289/100000000000000)
theorem h91 : Model (fun x => f91 ((9/8)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(364964789757244691/100000000000000),(1497330822691839/25000000000000),(1248785392519/3125000000000),(13893701199/10000000000000)⟩
def e92 : ℝ := (2664821/1000000000000)
theorem h92 : Model (fun x => f92 ((9/8)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(6849975861/25000000000000),(-449651267/100000000000000),(875797/20000000000000),(-1653/5000000000000)⟩
def e93 : ℝ := (33/12500000000000)
theorem h93 : Model (fun x => f93 ((9/8)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (358935366130422637/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(257741090029/12500000000000),(408163265243/100000000000000),(-832986327/100000000000000),(2266557/100000000000000)⟩
def e94 : ℝ := (242817/100000000000000)
theorem h94 : Model (fun x => f94 ((9/8)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(20833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((9/8)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(9795918367347/20000000000000),(-1599333611/800000000000),(101998317/12500000000000),(-1665279/50000000000000)⟩
def e96 : ℝ := (13653/100000000000000)
theorem h96 : Model (fun x => f96 ((9/8)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (203333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(102040816326529/100000000000000),(399833402747/100000000000000),(-1631973073/100000000000000),(6661113/100000000000000)⟩
def e97 : ℝ := (84187/100000000000000)
theorem h97 : Model (fun x => f97 ((9/8)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2142857142857109/100000000000000),(8396501457687/100000000000000),(-34271434533/100000000000000),(139883373/100000000000000)⟩
def e98 : ℝ := (1767927/100000000000000)
theorem h98 : Model (fun x => f98 ((9/8)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(2040816326529/100000000000000),(399833402747/100000000000000),(-1631973073/100000000000000),(6661113/100000000000000)⟩
def e99 : ℝ := (84187/100000000000000)
theorem h99 : Model (fun x => f99 ((9/8)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(2186588921281/5000000000000),(4369607901449/50000000000000),(-1049125553/50000000000000),(-32116097/25000000000000)⟩
def e100 : ℝ := (1768381/50000000000000)
theorem h100 : Model (fun x => f100 ((9/8)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(26030820491461/25000000000000),(407993268109/50000000000000),(-1731889793/100000000000000),(543761/100000000000000)⟩
def e101 : ℝ := (126303/50000000000000)
theorem h101 : Model (fun x => f101 ((9/8)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(102040816326529/10000000000000),(399833402747/10000000000000),(-1631973073/10000000000000),(6661113/10000000000000)⟩
def e102 : ℝ := (84187/10000000000000)
theorem h102 : Model (fun x => f102 ((9/8)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(562265722615567/50000000000000),(601790070461/12500000000000),(-18051620523/100000000000000),(67154891/100000000000000)⟩
def e103 : ℝ := (273619/25000000000000)
theorem h103 : Model (fun x => f103 ((9/8)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(612265722615567/50000000000000),(601790070461/12500000000000),(-18051620523/100000000000000),(67154891/100000000000000)⟩
def e104 : ℝ := (273619/25000000000000)
theorem h104 : Model (fun x => f104 ((9/8)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(535509378380521/100000000000000),(21823966714941/20000000000000),(387145824221/100000000000000),(-3222305407/100000000000000)⟩
def e105 : ℝ := (44138743/100000000000000)
theorem h105 : Model (fun x => f105 ((9/8)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(202040816326529/100000000000000),(399833402747/100000000000000),(-1631973073/100000000000000),(6661113/100000000000000)⟩
def e106 : ℝ := (84187/100000000000000)
theorem h106 : Model (fun x => f106 ((9/8)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(204102457309451/50000000000000),(100978333857/6250000000000),(-4995835939/100000000000000),(13865987/100000000000000)⟩
def e107 : ℝ := (21049/5000000000000)
theorem h107 : Model (fun x => f107 ((9/8)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(10309256772263/1250000000000),(4896418800903/100000000000000),(-1029550027/10000000000000),(1772779/20000000000000)⟩
def e108 : ℝ := (288483/20000000000000)
theorem h108 : Model (fun x => f108 ((9/8)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(1104140737135947/25000000000000),(926176288498213/100000000000000),(8480779245331/100000000000000),(-18806343919/100000000000000)⟩
def e109 : ℝ := (563829991/100000000000000)
theorem h109 : Model (fun x => f109 ((9/8)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(546647230320681/3125000000000),(8567858630289/6250000000000),(-36369685653/12500000000000),(11418981/12500000000000)⟩
def e110 : ℝ := (2652363/6250000000000)
theorem h110 : Model (fun x => f110 ((9/8)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(356994109596897/100000000000000),(36369685614301/50000000000000),(128350162051/50000000000000),(-69796061/3125000000000)⟩
def e111 : ℝ := (3768077/12500000000000)
theorem h111 : Model (fun x => f111 ((9/8)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(368034394201981/12500000000000),(38586938191207/6250000000000),(564198156273/10000000000000),(-665424041/5000000000000)⟩
def e112 : ℝ := (385890439/100000000000000)
theorem h112 : Model (fun x => f112 ((9/8)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(1840209525539909/25000000000000),(61742691982301/4000000000000),(14122760808061/100000000000000),(-32114824739/100000000000000)⟩
def e113 : ℝ := (94972043/10000000000000)
theorem h113 : Model (fun x => f113 ((9/8)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(182215743440227/3125000000000),(2855952876763/6250000000000),(-12123228551/12500000000000),(3806327/12500000000000)⟩
def e114 : ℝ := (884121/6250000000000)
theorem h114 : Model (fun x => f114 ((9/8)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(20824656393/50000000000000),(4079932681/25000000000000),(1532056353/100000000000000),(-2555693/20000000000000)⟩
def e115 : ℝ := (10529/12500000000000)
theorem h115 : Model (fun x => f115 ((9/8)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(33999439/4000000000000),(499583593/100000000000000),(19167697/20000000000000),(350083/6250000000000)⟩
def e116 : ℝ := (77429/100000000000000)
theorem h116 : Model (fun x => f116 ((9/8)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(49561864431/100000000000000),(29518641841/100000000000000),(72696393/1250000000000),(369917411/100000000000000)⟩
def e117 : ℝ := (7022623/100000000000000)
theorem h117 : Model (fun x => f117 ((9/8)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(100135195483/100000000000000),(59837869833/100000000000000),(5933663711/50000000000000),(385079439/50000000000000)⟩
def e118 : ℝ := (3121723/20000000000000)
theorem h118 : Model (fun x => f118 ((9/8)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(7360938237355119/100000000000000),(771813568713679/50000000000000),(14134628135483/100000000000000),(-31344665861/100000000000000)⟩
def e119 : ℝ := (193065809/20000000000000)
theorem h119 : Model (fun x => f119 ((9/8)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(4336663/25000000000000),(13594111/100000000000000),(3939517/100000000000000),(48941/10000000000000)⟩
def e120 : ℝ := (11423/50000000000000)
theorem h120 : Model (fun x => f120 ((9/8)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(354013/100000000000000),(86697/25000000000000),(134469/100000000000000),(12759/50000000000000)⟩
def e121 : ℝ := (2461/100000000000000)
theorem h121 : Model (fun x => f121 ((9/8)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(903/12500000000000),(2123/25000000000000),(33/800000000000),(263/25000000000000)⟩
def e122 : ℝ := (163/100000000000000)
theorem h122 : Model (fun x => f122 ((9/8)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(147/100000000000000),(101/50000000000000),(59/50000000000000),(37/100000000000000)⟩
def e123 : ℝ := (1/10000000000000)
theorem h123 : Model (fun x => f123 ((9/8)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(441/100000000000000),(303/50000000000000),(177/50000000000000),(111/100000000000000)⟩
def e124 : ℝ := (3/10000000000000)
theorem h124 : Model (fun x => f124 ((9/8)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-441/100000000000000),(-303/50000000000000),(-177/50000000000000),(-111/100000000000000)⟩
def e125 : ℝ := (3/10000000000000)
theorem h125 : Model (fun x => f125 ((9/8)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(3680469118677339/50000000000000),(24119174022293/1562500000000),(14134628135129/100000000000000),(-7836166493/25000000000000)⟩
def e126 : ℝ := (38613163/4000000000000)
theorem h126 : Model (fun x => f126 ((9/8)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(546647230320681/2500000000000),(8567858630289/5000000000000),(-36369685653/10000000000000),(11418981/10000000000000)⟩
def e127 : ℝ := (2652363/5000000000000)
theorem h127 : Model (fun x => f127 ((9/8)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1666312523190251/100000000000000),(13190352688147/100000000000000),(-293662769/2000000000000),(-48227501/100000000000000)⟩
def e128 : ℝ := (2074481/50000000000000)
theorem h128 : Model (fun x => f128 ((9/8)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(72870810052049299/20000000000000),(5739533932086249/100000000000000),(13331690369887/100000000000000),(-3271044873/4000000000000)⟩
def e129 : ℝ := (181960597/10000000000000)
theorem h129 : Model (fun x => f129 ((9/8)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(27445831857/100000000000000),(-432343989/100000000000000),(5806313/100000000000000),(-34743/50000000000000)⟩
def e130 : ℝ := (189/20000000000000)
theorem h130 : Model (fun x => f130 ((9/8)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (89650275260515641/25000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2020270731721/100000000000000),(391836734633/100000000000000),(-591753439/25000000000000),(7399991/50000000000000)⟩
def e131 : ℝ := (120377/25000000000000)
theorem h131 : Model (fun x => f131 ((9/8)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(4082199451953/100000000000000),(199999999969/25000000000000),(-3200000083/100000000000000),(17066539/100000000000000)⟩
def e132 : ℝ := (28973/4000000000000)
theorem h132 : Model (fun x => f132 ((9/8)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-4289780202121/10000000000000),(-4196158628027/50000000000000),(36291203531/100000000000000),(-222807219/100000000000000)⟩
def e133 : ℝ := (18362301/100000000000000)
theorem h133 : Model (fun x => f133 ((9/8)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(11111111111111/12500000000000),(-246913580247/12500000000000),(43895747599/100000000000000),(-487730529/50000000000000)⟩
def e134 : ℝ := (5542393/25000000000000)
theorem h134 : Model (fun x => f134 ((9/8)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (11/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-38131379574409/100000000000000),(-1322494714079/20000000000000),(179202704703/100000000000000),(-1045083297/25000000000000)⟩
def e135 : ℝ := (130721093/100000000000000)
theorem h135 : Model (fun x => f135 ((9/8)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(32805/2048),(729/512),(243/5120),(9/12800)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((9/8)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((9/8)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(6561/256),(2187/1280),(243/6400),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((9/8)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(85293/2048),(8019/2560),(2187/25600),(63/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((9/8)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-81/64),(-9/160),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((9/8)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(82701/2048),(1575/512),(2171/25600),(63/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((9/8)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((9/8)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(27/4),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((9/8)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-27/4),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((9/8)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(68877/2048),(7491/2560),(2171/25600),(63/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((9/8)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(75021/2048),(7491/2560),(2171/25600),(63/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((9/8)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((9/8)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(75021/32),(7491/40),(2171/400),(63/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((9/8)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((9/8)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(6200145/4096),(137781/1024),(45927/10240),(1701/25600)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((9/8)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(66062971107/100000000000000),(-5872264099/100000000000000),(163118447/50000000000000),(-7249709/50000000000000)⟩
def e151 : ℝ := (8629/1250000000000)
theorem h151 : Model (fun x => f151 ((9/8)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (351898533/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(7743922117841/5000000000000),(-1395029741283/100000000000000),(23660329817/100000000000000),(-24250323/4000000000000)⟩
def e152 : ℝ := (1571633051/50000000000000)
theorem h152 : Model (fun x => f152 ((9/8)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(33/8),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((9/8)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(825/64),(29/160),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((9/8)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(51/4),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((9/8)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(7843137254901/100000000000000),(-92272202999/100000000000000),(1085555329/100000000000000),(-319281/2500000000000)⟩
def e156 : ℝ := (152041/100000000000000)
theorem h156 : Model (fun x => f156 ((9/8)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (63/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(50551470588229/50000000000000),(116061130333/50000000000000),(2171110653/100000000000000),(-2554249/10000000000000)⟩
def e157 : ℝ := (226991/6250000000000)
theorem h157 : Model (fun x => f157 ((9/8)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(100551470588229/50000000000000),(116061130333/50000000000000),(2171110653/100000000000000),(-2554249/10000000000000)⟩
def e158 : ℝ := (226991/6250000000000)
theorem h158 : Model (fun x => f158 ((9/8)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(100551470588229/100000000000000),(116061130333/100000000000000),(542777663/50000000000000),(-2554249/20000000000000)⟩
def e159 : ℝ := (1815929/100000000000000)
theorem h159 : Model (fun x => f159 ((9/8)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(551470588229/100000000000000),(116061130333/100000000000000),(542777663/50000000000000),(-2554249/20000000000000)⟩
def e160 : ℝ := (1815929/100000000000000)
theorem h160 : Model (fun x => f160 ((9/8)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((9/8)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((9/8)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(185541404061613/50000000000000),(428320838133/100000000000000),(1001554021/25000000000000),(-5891497/12500000000000)⟩
def e163 : ℝ := (1675411/25000000000000)
theorem h163 : Model (fun x => f163 ((9/8)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2726797093837511/100000000000000),(428320838133/100000000000000),(1001554021/25000000000000),(-5891497/12500000000000)⟩
def e164 : ℝ := (1340329/20000000000000)
theorem h164 : Model (fun x => f164 ((9/8)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((9/8)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(2741834577810707/100000000000000),(3595434430573/100000000000000),(17063157137/50000000000000),(-193169257/50000000000000)⟩
def e166 : ℝ := (56337953/100000000000000)
theorem h166 : Model (fun x => f166 ((9/8)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8024215530191659/100000000000000),(3595434430573/100000000000000),(17063157137/50000000000000),(-193169257/50000000000000)⟩
def e167 : ℝ := (28168977/50000000000000)
theorem h167 : Model (fun x => f167 ((9/8)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((9/8)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8068466718776769/100000000000000),(12928257438673/100000000000000),(62797355879/50000000000000),(-667311733/50000000000000)⟩
def e169 : ℝ := (12690021/6250000000000)
theorem h169 : Model (fun x => f169 ((9/8)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3334378584456097/25000000000000),(12928257438673/100000000000000),(62797355879/50000000000000),(-667311733/50000000000000)⟩
def e170 : ℝ := (203040337/100000000000000)
theorem h170 : Model (fun x => f170 ((9/8)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((9/8)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(2682213361319663/20000000000000),(14239611437411/50000000000000),(286078108619/100000000000000),(-1379620063/50000000000000)⟩
def e172 : ℝ := (448702173/100000000000000)
theorem h172 : Model (fun x => f172 ((9/8)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(78733905461563/500000000000),(14239611437411/50000000000000),(286078108619/100000000000000),(-1379620063/50000000000000)⟩
def e173 : ℝ := (224351087/50000000000000)
theorem h173 : Model (fun x => f173 ((9/8)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((9/8)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(15833619958629509/100000000000000),(46912169539533/100000000000000),(491649074047/100000000000000),(-414433331/10000000000000)⟩
def e175 : ℝ := (92746997/12500000000000)
theorem h175 : Model (fun x => f175 ((9/8)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(16236000911010461/100000000000000),(46912169539533/100000000000000),(491649074047/100000000000000),(-414433331/10000000000000)⟩
def e176 : ℝ := (741975977/100000000000000)
theorem h176 : Model (fun x => f176 ((9/8)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((9/8)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(4081384420184819/25000000000000),(33007281267519/50000000000000),(725057940937/100000000000000),(-5160856517/100000000000000)⟩
def e178 : ℝ := (8385637/800000000000)
theorem h178 : Model (fun x => f178 ((9/8)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(4076979658280057/25000000000000),(33007281267519/50000000000000),(725057940937/100000000000000),(-5160856517/100000000000000)⟩
def e179 : ℝ := (524102313/50000000000000)
theorem h179 : Model (fun x => f179 ((9/8)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((9/8)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(8198926003967101/50000000000000),(1332902627043/1562500000000),(982705148973/100000000000000),(-228556253/4000000000000)⟩
def e181 : ℝ := (679632263/50000000000000)
theorem h181 : Model (fun x => f181 ((9/8)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(3280237068253507/20000000000000),(1332902627043/1562500000000),(982705148973/100000000000000),(-228556253/4000000000000)⟩
def e182 : ℝ := (1359264527/100000000000000)
theorem h182 : Model (fun x => f182 ((9/8)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(1413245519969/1562500000000),(19505837316389/100000000000000),(70617527399/25000000000000),(-59566063/100000000000000)⟩
def e183 : ℝ := (157768043/50000000000000)
theorem h183 : Model (fun x => f183 ((9/8)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(50552991187277/50000000000000),(116701173331/50000000000000),(579446387/25000000000000),(-11581767/50000000000000)⟩
def e184 : ℝ := (918571/25000000000000)
theorem h184 : Model (fun x => f184 ((9/8)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(200551470588229/100000000000000),(116061130333/100000000000000),(542777663/50000000000000),(-2554249/20000000000000)⟩
def e185 : ℝ := (1815929/100000000000000)
theorem h185 : Model (fun x => f185 ((9/8)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(100552230887753/25000000000000),(14547643979/3125000000000),(22444481/500000000000),(-6088253/12500000000000)⟩
def e186 : ℝ := (3653071/50000000000000)
theorem h186 : Model (fun x => f186 ((9/8)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(10082948887733/1250000000000),(1400424668919/100000000000000),(6954520427/50000000000000),(-17348043/12500000000000)⟩
def e187 : ℝ := (22041863/100000000000000)
theorem h187 : Model (fun x => f187 ((9/8)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1263843892063/78125000000),(3744763023997/100000000000000),(38276613771/100000000000000),(-350006117/100000000000000)⟩
def e188 : ℝ := (11819393/20000000000000)
theorem h188 : Model (fun x => f188 ((9/8)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(8178059409607/500000000000),(1890494077463/25000000000000),(84935595729/100000000000000),(-552464197/100000000000000)⟩
def e189 : ℝ := (120282767/100000000000000)
theorem h189 : Model (fun x => f189 ((9/8)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((9/8)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(100551470588229/12500000000000),(116061130333/12500000000000),(542777663/6250000000000),(-2554249/2500000000000)⟩
def e191 : ℝ := (1815929/12500000000000)
theorem h191 : Model (fun x => f191 ((9/8)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(452758873540193/50000000000000),(580945694663/50000000000000),(2750557039/25000000000000),(-62666747/50000000000000)⟩
def e192 : ℝ := (4550429/25000000000000)
theorem h192 : Model (fun x => f192 ((9/8)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(502758873540193/50000000000000),(580945694663/50000000000000),(2750557039/25000000000000),(-62666747/50000000000000)⟩
def e193 : ℝ := (4550429/25000000000000)
theorem h193 : Model (fun x => f193 ((9/8)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(4111591936518791/25000000000000),(47520523722207/50000000000000),(560929095623/50000000000000),(-361640613/6250000000000)⟩
def e194 : ℝ := (189587097/12500000000000)
theorem h194 : Model (fun x => f194 ((9/8)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(304018496801/50000000000000),(-878438231/25000000000000),(-2646333/12500000000000),(143987/25000000000000)⟩
def e195 : ℝ := (59919/100000000000000)
theorem h195 : Model (fun x => f195 ((9/8)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (408754938437323/2500000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(549955556597/100000000000000),(923396781/800000000000),(1012987451/100000000000000),(-13896069/100000000000000)⟩
def e196 : ℝ := (1026031/50000000000000)
theorem h196 : Model (fun x => f196 ((9/8)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(50551470588229/25000000000000),(116061130333/25000000000000),(2171110653/50000000000000),(-2554249/5000000000000)⟩
def e197 : ℝ := (226991/3125000000000)
theorem h197 : Model (fun x => f197 ((9/8)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(12431444241317/25000000000000),(-57395777979/100000000000000),(-470591459/100000000000000),(1495719/20000000000000)⟩
def e198 : ℝ := (227781/25000000000000)
theorem h198 : Model (fun x => f198 ((9/8)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (200868618630793/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(100548446069463/100000000000000),(22958311191/20000000000000),(188236583/20000000000000),(-14957191/100000000000000)⟩
def e199 : ℝ := (5506933/100000000000000)
theorem h199 : Model (fun x => f199 ((9/8)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(548446069463/100000000000000),(22958311191/20000000000000),(188236583/20000000000000),(-14957191/100000000000000)⟩
def e200 : ℝ := (5506933/100000000000000)
theorem h200 : Model (fun x => f200 ((9/8)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(92767911552183/25000000000000),(423635504119/100000000000000),(1736706569/50000000000000),(-27599579/50000000000000)⟩
def e201 : ℝ := (2540401/12500000000000)
theorem h201 : Model (fun x => f201 ((9/8)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2726785931923017/100000000000000),(423635504119/100000000000000),(1736706569/50000000000000),(-27599579/50000000000000)⟩
def e202 : ℝ := (20323209/100000000000000)
theorem h202 : Model (fun x => f202 ((9/8)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1370870441094659/50000000000000),(1778039457603/50000000000000),(14821402021/50000000000000),(-227689053/50000000000000)⟩
def e203 : ℝ := (4268477/2500000000000)
theorem h203 : Model (fun x => f203 ((9/8)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(802412183457027/10000000000000),(1778039457603/50000000000000),(14821402021/50000000000000),(-227689053/50000000000000)⟩
def e204 : ℝ := (170739081/100000000000000)
theorem h204 : Model (fun x => f204 ((9/8)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8068129815380893/100000000000000),(12786596395871/100000000000000),(109409120939/100000000000000),(-397640549/25000000000000)⟩
def e205 : ℝ := (153684513/25000000000000)
theorem h205 : Model (fun x => f205 ((9/8)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(416786794825891/3125000000000),(12786596395871/100000000000000),(109409120939/100000000000000),(-397640549/25000000000000)⟩
def e206 : ℝ := (614738053/100000000000000)
theorem h206 : Model (fun x => f206 ((9/8)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13410324659844941/100000000000000),(28166677478681/100000000000000),(10008573571/4000000000000),(-1674107491/50000000000000)⟩
def e207 : ℝ := (1356741007/100000000000000)
theorem h207 : Model (fun x => f207 ((9/8)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(7873019472779613/50000000000000),(28166677478681/100000000000000),(10008573571/4000000000000),(-1674107491/50000000000000)⟩
def e208 : ℝ := (84796313/6250000000000)
theorem h208 : Model (fun x => f208 ((9/8)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(7916198738626129/50000000000000),(23198139810549/50000000000000),(432118625667/100000000000000),(-5169418367/100000000000000)⟩
def e209 : ℝ := (8960849/400000000000)
theorem h209 : Model (fun x => f209 ((9/8)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(1623477842963321/10000000000000),(23198139810549/50000000000000),(432118625667/100000000000000),(-5169418367/100000000000000)⟩
def e210 : ℝ := (2240212251/100000000000000)
theorem h210 : Model (fun x => f210 ((9/8)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(204047717922707/1250000000000),(65286892958279/100000000000000),(320273267717/50000000000000),(-6693327107/100000000000000)⟩
def e211 : ℝ := (3160629861/100000000000000)
theorem h211 : Model (fun x => f211 ((9/8)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(2038274798274689/12500000000000),(65286892958279/100000000000000),(320273267717/50000000000000),(-6693327107/100000000000000)⟩
def e212 : ℝ := (1580314931/50000000000000)
theorem h212 : Model (fun x => f212 ((9/8)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(16395629090325451/100000000000000),(10545386900151/12500000000000),(872474581289/100000000000000),(-7819223217/100000000000000)⟩
def e213 : ℝ := (4094804663/100000000000000)
theorem h213 : Model (fun x => f213 ((9/8)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(512467575739337/3125000000000),(10545386900151/12500000000000),(872474581289/100000000000000),(-7819223217/100000000000000)⟩
def e214 : ℝ := (511850583/12500000000000)
theorem h214 : Model (fun x => f214 ((9/8)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(8993946484527/10000000000000),(9643655103151/50000000000000),(1023883979/400000000000),(-700170169/100000000000000)⟩
def e215 : ℝ := (948559671/100000000000000)
theorem h215 : Model (fun x => f215 ((9/8)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(101099900069837/100000000000000),(230842251463/100000000000000),(506115151/25000000000000),(-558353/2000000000000)⟩
def e216 : ℝ := (11112787/100000000000000)
theorem h216 : Model (fun x => f216 ((9/8)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(200548446069463/100000000000000),(22958311191/20000000000000),(188236583/20000000000000),(-14957191/100000000000000)⟩
def e217 : ℝ := (5506933/100000000000000)
theorem h217 : Model (fun x => f217 ((9/8)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(402196792208763/100000000000000),(460425363373/100000000000000),(1953413217/50000000000000),(-1807251/3125000000000)⟩
def e218 : ℝ := (22126653/100000000000000)
theorem h218 : Model (fun x => f218 ((9/8)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(806599416915901/100000000000000),(1385063867331/100000000000000),(2429803327/20000000000000),(-167320433/100000000000000)⟩
def e219 : ℝ := (2666967/4000000000000)
theorem h219 : Model (fun x => f219 ((9/8)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(404405649157547/25000000000000),(3703632084003/100000000000000),(16773088171/50000000000000),(-85844223/20000000000000)⟩
def e220 : ℝ := (89287677/50000000000000)
theorem h220 : Model (fun x => f220 ((9/8)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(817707414350111/50000000000000),(1869631189529/25000000000000),(75212830637/100000000000000),(-183281753/25000000000000)⟩
def e221 : ℝ := (181248781/50000000000000)
theorem h221 : Model (fun x => f221 ((9/8)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(100548446069463/12500000000000),(22958311191/2500000000000),(188236583/2500000000000),(-14957191/12500000000000)⟩
def e222 : ℝ := (5506933/12500000000000)
theorem h222 : Model (fun x => f222 ((9/8)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(905487468625541/100000000000000),(1149174699103/100000000000000),(2388480981/25000000000000),(-73787589/50000000000000)⟩
def e223 : ℝ := (55168251/100000000000000)
theorem h223 : Model (fun x => f223 ((9/8)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1005487468625541/100000000000000),(1149174699103/100000000000000),(2388480981/25000000000000),(-73787589/50000000000000)⟩
def e224 : ℝ := (55168251/100000000000000)
theorem h224 : Model (fun x => f224 ((9/8)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(16443891162624589/100000000000000),(23497350679429/25000000000000),(199688637963/20000000000000),(-4103073597/50000000000000)⟩
def e225 : ℝ := (1141980947/25000000000000)
theorem h225 : Model (fun x => f225 ((9/8)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(608128568907/100000000000000),(-3475919441/100000000000000),(-17056927/100000000000000),(76503/12500000000000)⟩
def e226 : ℝ := (4379/2500000000000)
theorem h226 : Model (fun x => f226 ((9/8)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (4087222635661519/25000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(273473790223/50000000000000),(57082710097/50000000000000),(870880473/100000000000000),(-3973663/25000000000000)⟩
def e227 : ℝ := (3046893/50000000000000)
theorem h227 : Model (fun x => f227 ((9/8)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(1096903137043/100000000000000),(229590017819/100000000000000),(470966981/25000000000000),(-29790721/100000000000000)⟩
def e228 : ℝ := (1018231/12500000000000)
theorem h228 : Model (fun x => f228 ((9/8)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(339773298563/20000000000000),(340283318409/100000000000000),(-5122567/20000000000000),(-24748231/100000000000000)⟩
def e229 : ℝ := (11007327/20000000000000)
theorem h229 : Model (fun x => f229 ((9/8)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(94381471823/6250000000000),(268916204159/100000000000000),(-5998682613/100000000000000),(11130563/10000000000000)⟩
def e230 : ℝ := (10667593/20000000000000)
theorem h230 : Model (fun x => f230 ((9/8)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-36621276025241/100000000000000),(-1585889341559/25000000000000),(17320402209/10000000000000),(-2034513779/50000000000000)⟩
def e231 : ℝ := (92029529/50000000000000)
theorem h231 : Model (fun x => f231 ((9/8)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((9/8)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-405/64),(-9/32),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((9/8)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(189/8),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((9/8)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1107/64),(39/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((9/8)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((9/8)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2771/64),(39/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((9/8)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((9/8)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(346375/32),(975/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((9/8)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(351/64),(3/32),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((9/8)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(735/64),(3/32),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((9/8)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((9/8)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(138915/64),(567/32),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((9/8)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(11517834647/25000000000000),(-4701157/1250000000000),(5577427/100000000000000),(-32999/50000000000000)⟩
def e244 : ℝ := (427/50000000000000)
theorem h244 : Model (fun x => f244 ((9/8)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (215271/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(124671561745457/25000000000000),(-631717972241/50000000000000),(1459916263/100000000000000),(-80680019/100000000000000)⟩
def e245 : ℝ := (17727271/100000000000000)
theorem h245 : Model (fun x => f245 ((9/8)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(81/4),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((9/8)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(1377/64),(81/160),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((9/8)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(2721/64),(81/160),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((9/8)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(625/64),(5/32),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((9/8)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1700625/4096),(11865/1024),(5723/51200),(53/128000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((9/8)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((9/8)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(13005/32),(153/16),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((9/8)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(61514801999/25000000000000),(-723703553/12500000000000),(102169913/100000000000000),(-801333/50000000000000)⟩
def e253 : ℝ := (2437/10000000000000)
theorem h253 : Model (fun x => f253 ((9/8)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (31743/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(102161728661669/100000000000000),(447261516827/100000000000000),(2840012471/100000000000000),(-3355617/12500000000000)⟩
def e254 : ℝ := (20186189/100000000000000)
theorem h254 : Model (fun x => f254 ((9/8)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(202161728661669/100000000000000),(447261516827/100000000000000),(2840012471/100000000000000),(-3355617/12500000000000)⟩
def e255 : ℝ := (20186189/100000000000000)
theorem h255 : Model (fun x => f255 ((9/8)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(50540432165417/50000000000000),(223630758413/100000000000000),(284001247/20000000000000),(-3355617/25000000000000)⟩
def e256 : ℝ := (1261637/12500000000000)
theorem h256 : Model (fun x => f256 ((9/8)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(540432165417/50000000000000),(223630758413/100000000000000),(284001247/20000000000000),(-3355617/25000000000000)⟩
def e257 : ℝ := (1261637/12500000000000)
theorem h257 : Model (fun x => f257 ((9/8)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(5828695673839/1562500000000),(825303989381/100000000000000),(204707/3906250000),(-49535299/100000000000000)⟩
def e258 : ℝ := (37248333/100000000000000)
theorem h258 : Model (fun x => f258 ((9/8)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2728750808839981/100000000000000),(825303989381/100000000000000),(204707/3906250000),(-49535299/100000000000000)⟩
def e259 : ℝ := (18624167/50000000000000)
theorem h259 : Model (fun x => f259 ((9/8)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(689561225752519/25000000000000),(433534408427/6250000000000),(1147280177/2500000000000),(-392897677/100000000000000)⟩
def e260 : ℝ := (313382599/100000000000000)
theorem h260 : Model (fun x => f260 ((9/8)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(2010156463847757/25000000000000),(433534408427/6250000000000),(1147280177/2500000000000),(-392897677/100000000000000)⟩
def e261 : ℝ := (1566913/500000000000)
theorem h261 : Model (fun x => f261 ((9/8)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(1625506822447553/20000000000000),(4998567563383/20000000000000),(22009609727/12500000000000),(-79704281/6250000000000)⟩
def e262 : ℝ := (35340559/3125000000000)
theorem h262 : Model (fun x => f262 ((9/8)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(1674572716410673/12500000000000),(4998567563383/20000000000000),(22009609727/12500000000000),(-79704281/6250000000000)⟩
def e263 : ℝ := (1130897889/100000000000000)
theorem h263 : Model (fun x => f263 ((9/8)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(13541380604769871/100000000000000),(3451365863327/6250000000000),(424103998603/100000000000000),(-1169271201/50000000000000)⟩
def e264 : ℝ := (2504085189/100000000000000)
theorem h264 : Model (fun x => f264 ((9/8)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(3969273722621039/25000000000000),(3451365863327/6250000000000),(424103998603/100000000000000),(-1169271201/50000000000000)⟩
def e265 : ℝ := (250408519/10000000000000)
theorem h265 : Model (fun x => f265 ((9/8)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(8024352372964033/50000000000000),(18264958970293/20000000000000),(777636775323/100000000000000),(-1381168049/50000000000000)⟩
def e266 : ℝ := (4151604053/100000000000000)
theorem h266 : Model (fun x => f266 ((9/8)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(8225542849154509/50000000000000),(18264958970293/20000000000000),(777636775323/100000000000000),(-1381168049/50000000000000)⟩
def e267 : ℝ := (2075802027/50000000000000)
theorem h267 : Model (fun x => f267 ((9/8)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(16628899615656973/100000000000000),(64550789849261/50000000000000),(1223878747837/100000000000000),(-982241059/50000000000000)⟩
def e268 : ℝ := (5883078553/100000000000000)
theorem h268 : Model (fun x => f268 ((9/8)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(664451222721517/4000000000000),(64550789849261/50000000000000),(1223878747837/100000000000000),(-982241059/50000000000000)⟩
def e269 : ℝ := (2941539277/50000000000000)
theorem h269 : Model (fun x => f269 ((9/8)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(8395412987296303/50000000000000),(167644925340441/100000000000000),(1761699278257/100000000000000),(354860483/100000000000000)⟩
def e270 : ℝ := (7654189601/100000000000000)
theorem h270 : Model (fun x => f270 ((9/8)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(16794159307925939/100000000000000),(167644925340441/100000000000000),(1761699278257/100000000000000),(354860483/100000000000000)⟩
def e271 : ℝ := (3827094801/50000000000000)
theorem h271 : Model (fun x => f271 ((9/8)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(181522077622809/100000000000000),(1968446001493/5000000000000),(632425306383/100000000000000),(16279659/400000000000)⟩
def e272 : ℝ := (1815647253/100000000000000)
theorem h272 : Model (fun x => f272 ((9/8)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(25543352834671/25000000000000),(226047903513/50000000000000),(421352039/12500000000000),(-1298997/6250000000000)⟩
def e273 : ℝ := (10245033/50000000000000)
theorem h273 : Model (fun x => f273 ((9/8)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(100540432165417/50000000000000),(223630758413/100000000000000),(284001247/20000000000000),(-3355617/25000000000000)⟩
def e274 : ℝ := (1261637/12500000000000)
theorem h274 : Model (fun x => f274 ((9/8)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(12635473125011/3125000000000),(224839330963/25000000000000),(3105414391/50000000000000),(-5953611/12500000000000)⟩
def e275 : ℝ := (20338129/50000000000000)
theorem h275 : Model (fun x => f275 ((9/8)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(162608118861199/20000000000000),(2712653220337/100000000000000),(20241611999/100000000000000),(-123384081/100000000000000)⟩
def e276 : ℝ := (61462807/50000000000000)
theorem h276 : Model (fun x => f276 ((9/8)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(408717263597761/25000000000000),(7272835389003/100000000000000),(1822298827/3125000000000),(-10937823/4000000000000)⟩
def e277 : ℝ := (16507523/5000000000000)
theorem h277 : Model (fun x => f277 ((9/8)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(835200741895907/50000000000000),(7411039231629/50000000000000),(147569572653/100000000000000),(-5519599/5000000000000)⟩
def e278 : ℝ := (84515173/12500000000000)
theorem h278 : Model (fun x => f278 ((9/8)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(50540432165417/6250000000000),(223630758413/12500000000000),(284001247/2500000000000),(-3355617/3125000000000)⟩
def e279 : ℝ := (1261637/1562500000000)
theorem h279 : Model (fun x => f279 ((9/8)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(227705081496339/25000000000000),(224114187433/10000000000000),(920679137/6250000000000),(-8010231/6250000000000)⟩
def e280 : ℝ := (50617417/50000000000000)
theorem h280 : Model (fun x => f280 ((9/8)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(252705081496339/25000000000000),(224114187433/10000000000000),(920679137/6250000000000),(-8010231/6250000000000)⟩
def e281 : ℝ := (50617417/50000000000000)
theorem h281 : Model (fun x => f281 ((9/8)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(16884757723728637/100000000000000),(187260648962797/100000000000000),(1034955824939/50000000000000),(111697559/5000000000000)⟩
def e282 : ℝ := (1711256479/20000000000000)
theorem h282 : Model (fun x => f282 ((9/8)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(74031266569/12500000000000),(-3284179317/50000000000000),(242209/100000000000000),(362087/50000000000000)⟩
def e283 : ℝ := (314257/100000000000000)
theorem h283 : Model (fun x => f283 ((9/8)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (16695416372882387/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(268766186333/25000000000000),(110619730001/50000000000000),(7250547/625000000000),(-4006499/25000000000000)⟩
def e284 : ℝ := (5796273/50000000000000)
theorem h284 : Model (fun x => f284 ((9/8)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(102161728661669/50000000000000),(447261516827/50000000000000),(2840012471/50000000000000),(-3355617/6250000000000)⟩
def e285 : ℝ := (20186189/50000000000000)
theorem h285 : Model (fun x => f285 ((9/8)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(24732673355637/50000000000000),(-54718432977/50000000000000),(-9055651/2000000000000),(22769/250000000000)⟩
def e286 : ℝ := (997959/20000000000000)
theorem h286 : Model (fun x => f286 ((9/8)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (100855790050623/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(101069306577451/100000000000000),(43774746381/20000000000000),(905565097/100000000000000),(-4553801/25000000000000)⟩
def e287 : ℝ := (1214809/4000000000000)
theorem h287 : Model (fun x => f287 ((9/8)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(1069306577451/100000000000000),(43774746381/20000000000000),(905565097/100000000000000),(-4553801/25000000000000)⟩
def e288 : ℝ := (1214809/4000000000000)
theorem h288 : Model (fun x => f288 ((9/8)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(372993869512021/100000000000000),(201937074079/25000000000000),(3341966429/100000000000000),(-67222777/100000000000000)⟩
def e289 : ℝ := (56040297/50000000000000)
theorem h289 : Model (fun x => f289 ((9/8)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(1364354077613153/50000000000000),(201937074079/25000000000000),(3341966429/100000000000000),(-67222777/100000000000000)⟩
def e290 : ℝ := (22416119/20000000000000)
theorem h290 : Model (fun x => f290 ((9/8)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1378943205504791/50000000000000),(6788810974117/100000000000000),(29855879789/100000000000000),(-550351979/100000000000000)⟩
def e291 : ℝ := (58921991/6250000000000)
theorem h291 : Model (fun x => f291 ((9/8)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4020133681695267/50000000000000),(6788810974117/100000000000000),(29855879789/100000000000000),(-550351979/100000000000000)⟩
def e292 : ℝ := (942751857/100000000000000)
theorem h292 : Model (fun x => f292 ((9/8)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(1625248494230383/20000000000000),(12229718704893/50000000000000),(58921954777/50000000000000),(-1893964251/100000000000000)⟩
def e293 : ℝ := (3401004829/100000000000000)
theorem h293 : Model (fun x => f293 ((9/8)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(6697645045099767/50000000000000),(12229718704893/50000000000000),(58921954777/50000000000000),(-1893964251/100000000000000)⟩
def e294 : ℝ := (340100483/10000000000000)
theorem h294 : Model (fun x => f294 ((9/8)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(13538526808202679/100000000000000),(3377484693921/6250000000000),(29394237739/10000000000000),(-3874770461/100000000000000)⟩
def e295 : ℝ := (7528065383/100000000000000)
theorem h295 : Model (fun x => f295 ((9/8)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3968560273479241/25000000000000),(3377484693921/6250000000000),(29394237739/10000000000000),(-3874770461/100000000000000)⟩
def e296 : ℝ := (941008173/12500000000000)
theorem h296 : Model (fun x => f296 ((9/8)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(16043985398054647/100000000000000),(89362149652341/100000000000000),(559115938031/100000000000000),(-709375153/12500000000000)⟩
def e297 : ℝ := (2495681851/20000000000000)
theorem h297 : Model (fun x => f297 ((9/8)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(16446366350435599/100000000000000),(89362149652341/100000000000000),(559115938031/100000000000000),(-709375153/12500000000000)⟩
def e298 : ℝ := (1559801157/12500000000000)
theorem h298 : Model (fun x => f298 ((9/8)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(8311114213786247/50000000000000),(126314480790291/100000000000000),(45480871339/5000000000000),(-6698433211/100000000000000)⟩
def e299 : ℝ := (17685171907/100000000000000)
theorem h299 : Model (fun x => f299 ((9/8)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(8302304689976723/50000000000000),(126314480790291/100000000000000),(45480871339/5000000000000),(-6698433211/100000000000000)⟩
def e300 : ℝ := (4421292977/25000000000000)
theorem h300 : Model (fun x => f300 ((9/8)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(16782163560213333/100000000000000),(82004149029903/50000000000000),(673089395417/50000000000000),(-1664962503/25000000000000)⟩
def e301 : ℝ := (4604863001/20000000000000)
theorem h301 : Model (fun x => f301 ((9/8)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(8392748446773333/50000000000000),(82004149029903/50000000000000),(673089395417/50000000000000),(-1664962503/25000000000000)⟩
def e302 : ℝ := (11512157503/50000000000000)
theorem h302 : Model (fun x => f302 ((9/8)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(179488422340527/100000000000000),(19246397494211/50000000000000),(525369462177/100000000000000),(260581389/20000000000000)⟩
def e303 : ℝ := (273869771/5000000000000)
theorem h303 : Model (fun x => f303 ((9/8)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(102150047320467/100000000000000),(442428326233/100000000000000),(2309553833/100000000000000),(-32855873/100000000000000)⟩
def e304 : ℝ := (61595339/100000000000000)
theorem h304 : Model (fun x => f304 ((9/8)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(201069306577451/100000000000000),(43774746381/20000000000000),(905565097/100000000000000),(-4553801/25000000000000)⟩
def e305 : ℝ := (1214809/4000000000000)
theorem h305 : Model (fun x => f305 ((9/8)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(404288660475369/100000000000000),(880175790043/100000000000000),(4120684027/100000000000000),(-69286281/100000000000000)⟩
def e306 : ℝ := (122335789/100000000000000)
theorem h306 : Model (fun x => f306 ((9/8)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(812900406189089/100000000000000),(2654645036553/100000000000000),(6936500699/50000000000000),(-19596579/10000000000000)⟩
def e307 : ℝ := (46197083/12500000000000)
theorem h307 : Model (fun x => f307 ((9/8)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1634493209889683/100000000000000),(3558450911393/50000000000000),(10266502681/25000000000000),(-121923657/25000000000000)⟩
def e308 : ℝ := (992399023/100000000000000)
theorem h308 : Model (fun x => f308 ((9/8)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1669635587352131/100000000000000),(7250689765317/50000000000000),(5559281979/5000000000000),(-172287741/25000000000000)⟩
def e309 : ℝ := (2032903987/100000000000000)
theorem h309 : Model (fun x => f309 ((9/8)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(101069306577451/12500000000000),(43774746381/2500000000000),(905565097/12500000000000),(-4553801/3125000000000)⟩
def e310 : ℝ := (1214809/500000000000)
theorem h310 : Model (fun x => f310 ((9/8)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(36428179997603/4000000000000),(2193418181473/100000000000000),(9554074609/100000000000000),(-35715501/20000000000000)⟩
def e311 : ℝ := (304557139/100000000000000)
theorem h311 : Model (fun x => f311 ((9/8)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(40428179997603/4000000000000),(2193418181473/100000000000000),(9554074609/100000000000000),(-35715501/20000000000000)⟩
def e312 : ℝ := (304557139/100000000000000)
theorem h312 : Model (fun x => f312 ((9/8)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(16875082013968889/100000000000000),(183188186006831/100000000000000),(64054095497/4000000000000),(-3061317363/50000000000000)⟩
def e313 : ℝ := (1609475083/6250000000000)
theorem h313 : Model (fun x => f313 ((9/8)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(118517942511/20000000000000),(-6432883373/100000000000000),(13598943/100000000000000),(27113/4000000000000)⟩
def e314 : ℝ := (233857/25000000000000)
theorem h314 : Model (fun x => f314 ((9/8)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (16690260601338579/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1063629926017/100000000000000),(216558062299/100000000000000),(132299461/20000000000000),(-9812141/50000000000000)⟩
def e315 : ℝ := (17553973/50000000000000)
theorem h315 : Model (fun x => f315 ((9/8)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(2138694671349/100000000000000),(437797522301/100000000000000),(72863393/4000000000000),(-17825139/50000000000000)⟩
def e316 : ℝ := (11675123/25000000000000)
theorem h316 : Model (fun x => f316 ((9/8)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(213307523819/2000000000000),(2156214996121/100000000000000),(3583924889/100000000000000),(-196131613/100000000000000)⟩
def e317 : ℝ := (234062579/100000000000000)
theorem h317 : Model (fun x => f317 ((9/8)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(1896066878391/20000000000000),(426490363627/25000000000000),(-34724543533/100000000000000),(597317311/100000000000000)⟩
def e318 : ℝ := (28917013/12500000000000)
theorem h318 : Model (fun x => f318 ((9/8)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-13570470816643/50000000000000),(-289849744483/6250000000000),(138479478557/100000000000000),(-3471710247/100000000000000)⟩
def e319 : ℝ := (207697581/50000000000000)
theorem h319 : Model (fun x => f319 ((9/8)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((9/8)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-891/64),(-99/160),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((9/8)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((9/8)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(873/8),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((9/8)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(6093/64),(289/160),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((9/8)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((9/8)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(13005/64),(289/160),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((9/8)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1625625/32),(7225/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((9/8)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((9/8)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(420324594951886611/50000000000000),(3431221183280707/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (109421/100000000000000)
theorem h329 : Model (fun x => f329 ((9/8)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(1486946059/12500000000000),(-48553341/50000000000000),(288017/20000000000000),(-17041/100000000000000)⟩
def e330 : ℝ := (223/100000000000000)
theorem h330 : Model (fun x => f330 ((9/8)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (83374099792132531/10000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(151076042947617/25000000000000),(219248663971/50000000000000),(1107774833/12500000000000),(-48505621/100000000000000)⟩
def e331 : ℝ := (2162917/10000000000000)
theorem h331 : Model (fun x => f331 ((9/8)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((9/8)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(81/8),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((9/8)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((9/8)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((9/8)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(475806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((9/8)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((9/8)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((9/8)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(263864036478433/12500000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (101/10000000000000)
theorem h339 : Model (fun x => f339 ((9/8)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3574193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((9/8)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((9/8)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((9/8)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2014087708172277/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1009/100000000000000)
theorem h343 : Model (fun x => f343 ((9/8)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2482513536879/50000000000000),(-3472830513/50000000000000),(9716403/100000000000000),(-13593/100000000000000)⟩
def e344 : ℝ := (3/12500000000000)
theorem h344 : Model (fun x => f344 ((9/8)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2011270166536787/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(104807366792519/100000000000000),(477374125563/50000000000000),(-1335613621/100000000000000),(4671/250000000000)⟩
def e345 : ℝ := (179/5000000000000)
theorem h345 : Model (fun x => f345 ((9/8)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(204807366792519/100000000000000),(477374125563/50000000000000),(-1335613621/100000000000000),(4671/250000000000)⟩
def e346 : ℝ := (179/5000000000000)
theorem h346 : Model (fun x => f346 ((9/8)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(102403683396259/100000000000000),(477374125563/100000000000000),(-667806811/100000000000000),(4671/500000000000)⟩
def e347 : ℝ := (1791/100000000000000)
theorem h347 : Model (fun x => f347 ((9/8)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(2403683396259/100000000000000),(477374125563/100000000000000),(-667806811/100000000000000),(4671/500000000000)⟩
def e348 : ℝ := (1791/100000000000000)
theorem h348 : Model (fun x => f348 ((9/8)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(75583671078191/20000000000000),(1761737844339/100000000000000),(-154032821/6250000000000),(1723821/50000000000000)⟩
def e349 : ℝ := (6613/100000000000000)
theorem h349 : Model (fun x => f349 ((9/8)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(68340816027631/2500000000000),(1761737844339/100000000000000),(-154032821/6250000000000),(1723821/50000000000000)⟩
def e350 : ℝ := (3307/50000000000000)
theorem h350 : Model (fun x => f350 ((9/8)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(2799340515014203/100000000000000),(14853739360969/100000000000000),(-6184534427/50000000000000),(5538097/100000000000000)⟩
def e351 : ℝ := (105219/100000000000000)
theorem h351 : Model (fun x => f351 ((9/8)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(1616344293479031/20000000000000),(14853739360969/100000000000000),(-6184534427/50000000000000),(5538097/100000000000000)⟩
def e352 : ℝ := (5261/5000000000000)
theorem h352 : Model (fun x => f352 ((9/8)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(8275980464438831/100000000000000),(53790823413127/100000000000000),(2135619937/50000000000000),(-77070361/100000000000000)⟩
def e353 : ℝ := (501219/100000000000000)
theorem h353 : Model (fun x => f353 ((9/8)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(270900561669729/2000000000000),(53790823413127/100000000000000),(2135619937/50000000000000),(-77070361/100000000000000)⟩
def e354 : ℝ := (25061/5000000000000)
theorem h354 : Model (fun x => f354 ((9/8)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(1733825959318479/12500000000000),(4789769755001/4000000000000),(34140551953/20000000000000),(-11648569/4000000000000)⟩
def e355 : ℝ := (865853/100000000000000)
theorem h355 : Model (fun x => f355 ((9/8)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(16206321960262117/100000000000000),(4789769755001/4000000000000),(34140551953/20000000000000),(-11648569/4000000000000)⟩
def e356 : ℝ := (432927/50000000000000)
theorem h356 : Model (fun x => f356 ((9/8)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(16595870630365213/100000000000000),(799949216507/400000000000),(127641405781/20000000000000),(-131584043/100000000000000)⟩
def e357 : ℝ := (324781/12500000000000)
theorem h357 : Model (fun x => f357 ((9/8)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(3399650316549233/20000000000000),(799949216507/400000000000),(127641405781/20000000000000),(-131584043/100000000000000)⟩
def e358 : ℝ := (2598249/100000000000000)
theorem h358 : Model (fun x => f358 ((9/8)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(17406835733694967/100000000000000),(285939620604803/100000000000000),(186839958473/12500000000000),(216894643/12500000000000)⟩
def e359 : ℝ := (6009857/100000000000000)
theorem h359 : Model (fun x => f359 ((9/8)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(17389216686075919/100000000000000),(285939620604803/100000000000000),(186839958473/12500000000000),(216894643/12500000000000)⟩
def e360 : ℝ := (3004929/50000000000000)
theorem h360 : Model (fun x => f360 ((9/8)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(142457587202389/800000000000),(734031884543/195312500000),(55590467727/2000000000000),(1791298893/25000000000000)⟩
def e361 : ℝ := (7474629/100000000000000)
theorem h361 : Model (fun x => f361 ((9/8)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(8905265866815979/50000000000000),(734031884543/195312500000),(55590467727/2000000000000),(1791298893/25000000000000)⟩
def e362 : ℝ := (747463/10000000000000)
theorem h362 : Model (fun x => f362 ((9/8)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(428108794066751/100000000000000),(94056497017933/100000000000000),(1741959082717/100000000000000),(88780477/800000000000)⟩
def e363 : ℝ := (19717013/100000000000000)
theorem h363 : Model (fun x => f363 ((9/8)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(26216285932803/25000000000000),(488848688157/50000000000000),(227785753/25000000000000),(-1115641/25000000000000)⟩
def e364 : ℝ := (17079/100000000000000)
theorem h364 : Model (fun x => f364 ((9/8)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(202403683396259/100000000000000),(477374125563/100000000000000),(-667806811/100000000000000),(4671/500000000000)⟩
def e365 : ℝ := (1791/100000000000000)
theorem h365 : Model (fun x => f365 ((9/8)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(40967251052373/10000000000000),(24155570343/1250000000000),(-42447061/10000000000000),(-648541/25000000000000)⟩
def e366 : ℝ := (20661/100000000000000)
theorem h366 : Model (fun x => f366 ((9/8)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(207298062790489/25000000000000),(5867011694353/100000000000000),(2815015169/50000000000000),(-408871/2500000000000)⟩
def e367 : ℝ := (3613/6250000000000)
theorem h367 : Model (fun x => f367 ((9/8)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(839157829394079/50000000000000),(197917462911/1250000000000),(33865582223/100000000000000),(-37660481/100000000000000)⟩
def e368 : ℝ := (12079/6250000000000)
theorem h368 : Model (fun x => f368 ((9/8)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(1759968127851639/100000000000000),(33012562718301/100000000000000),(205607754689/100000000000000),(360979171/100000000000000)⟩
def e369 : ℝ := (39437/3125000000000)
theorem h369 : Model (fun x => f369 ((9/8)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(102403683396259/12500000000000),(477374125563/12500000000000),(-667806811/12500000000000),(4671/62500000000)⟩
def e370 : ℝ := (1791/12500000000000)
theorem h370 : Model (fun x => f370 ((9/8)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(231023652725321/25000000000000),(2398345190409/50000000000000),(-1107827869/25000000000000),(752759/25000000000000)⟩
def e371 : ℝ := (31407/100000000000000)
theorem h371 : Model (fun x => f371 ((9/8)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(256023652725321/25000000000000),(2398345190409/50000000000000),(-1107827869/25000000000000),(752759/25000000000000)⟩
def e372 : ℝ := (31407/100000000000000)
theorem h372 : Model (fun x => f372 ((9/8)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(9011869375454427/50000000000000),(422500097612649/100000000000000),(112848083941/3125000000000),(12149239421/100000000000000)⟩
def e373 : ℝ := (22755457/100000000000000)
theorem h373 : Model (fun x => f373 ((9/8)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(110964768611/20000000000000),(-6502899623/50000000000000),(193711507/100000000000000),(-230907/10000000000000)⟩
def e374 : ℝ := (5149/20000000000000)
theorem h374 : Model (fun x => f374 ((9/8)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (3519523068523043/20000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(2375249663697/100000000000000),(466168901087/100000000000000),(-1738698857/100000000000000),(7329131/100000000000000)⟩
def e375 : ℝ := (506647/100000000000000)
theorem h375 : Model (fun x => f375 ((9/8)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(104807366792519/50000000000000),(477374125563/25000000000000),(-1335613621/50000000000000),(4671/125000000000)⟩
def e376 : ℝ := (179/2500000000000)
theorem h376 : Model (fun x => f376 ((9/8)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(4882636868297/10000000000000),(-56903336583/25000000000000),(1379474829/100000000000000),(-8360451/100000000000000)⟩
def e377 : ℝ := (25607/50000000000000)
theorem h377 : Model (fun x => f377 ((9/8)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (12740705065987/6250000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(20469452526811/20000000000000),(22761334633/5000000000000),(-2758949661/100000000000000),(16720899/100000000000000)⟩
def e378 : ℝ := (317119/100000000000000)
theorem h378 : Model (fun x => f378 ((9/8)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(469452526811/20000000000000),(22761334633/5000000000000),(-2758949661/100000000000000),(16720899/100000000000000)⟩
def e379 : ℝ := (317119/100000000000000)
theorem h379 : Model (fun x => f379 ((9/8)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(377710135911393/100000000000000),(168000327053/10000000000000),(-2036367607/20000000000000),(61708079/100000000000000)⟩
def e380 : ℝ := (1170323/100000000000000)
theorem h380 : Model (fun x => f380 ((9/8)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1366712210812839/50000000000000),(168000327053/10000000000000),(-2036367607/20000000000000),(61708079/100000000000000)⟩
def e381 : ℝ := (292581/25000000000000)
theorem h381 : Model (fun x => f381 ((9/8)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(2797585071704631/100000000000000),(14162714950477/100000000000000),(-19546703251/25000000000000),(427508777/100000000000000)⟩
def e382 : ℝ := (85783/800000000000)
theorem h382 : Model (fun x => f382 ((9/8)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8079966024085583/100000000000000),(14162714950477/100000000000000),(-19546703251/25000000000000),(427508777/100000000000000)⟩
def e383 : ℝ := (2680719/25000000000000)
theorem h383 : Model (fun x => f383 ((9/8)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(8269624047413283/100000000000000),(51277313165973/100000000000000),(-238471799221/100000000000000),(1041917069/100000000000000)⟩
def e384 : ℝ := (8637659/20000000000000)
theorem h384 : Model (fun x => f384 ((9/8)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(6769335833230451/50000000000000),(51277313165973/100000000000000),(-238471799221/100000000000000),(1041917069/100000000000000)⟩
def e385 : ℝ := (5398537/12500000000000)
theorem h385 : Model (fun x => f385 ((9/8)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1385645984763513/10000000000000),(114112573634991/100000000000000),(-384166477893/100000000000000),(51866167/6250000000000)⟩
def e386 : ℝ := (53731069/50000000000000)
theorem h386 : Model (fun x => f386 ((9/8)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3238434826669883/20000000000000),(114112573634991/100000000000000),(-384166477893/100000000000000),(51866167/6250000000000)⟩
def e387 : ℝ := (107462139/100000000000000)
theorem h387 : Model (fun x => f387 ((9/8)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4143061746605661/25000000000000),(95251097106839/50000000000000),(-160223456287/50000000000000),(-670161049/50000000000000)⟩
def e388 : ℝ := (195732909/100000000000000)
theorem h388 : Model (fun x => f388 ((9/8)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(4243656984700899/25000000000000),(95251097106839/50000000000000),(-160223456287/50000000000000),(-670161049/50000000000000)⟩
def e389 : ℝ := (19573291/10000000000000)
theorem h389 : Model (fun x => f389 ((9/8)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(17373067037680993/100000000000000),(136123409196333/50000000000000),(2837070199/4000000000000),(-1312023027/25000000000000)⟩
def e390 : ℝ := (14513431/5000000000000)
theorem h390 : Model (fun x => f390 ((9/8)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(3471089598012389/20000000000000),(136123409196333/50000000000000),(2837070199/4000000000000),(-1312023027/25000000000000)⟩
def e391 : ℝ := (290268621/100000000000000)
theorem h391 : Model (fun x => f391 ((9/8)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(8881412967852759/50000000000000),(178821899057343/50000000000000),(416551852973/50000000000000),(-2414391709/25000000000000)⟩
def e392 : ℝ := (187072267/50000000000000)
theorem h392 : Model (fun x => f392 ((9/8)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(17766159269038851/100000000000000),(178821899057343/50000000000000),(416551852973/50000000000000),(-2414391709/25000000000000)⟩
def e393 : ℝ := (74828907/20000000000000)
theorem h393 : Model (fun x => f393 ((9/8)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(417018418028847/100000000000000),(44635569244657/50000000000000),(1157485774727/100000000000000),(-3330728819/100000000000000)⟩
def e394 : ℝ := (37763643/50000000000000)
theorem h394 : Model (fun x => f394 ((9/8)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(52374810843421/50000000000000),(465912058717/50000000000000),(-1787552747/50000000000000),(4553907/50000000000000)⟩
def e395 : ℝ := (881311/100000000000000)
theorem h395 : Model (fun x => f395 ((9/8)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(40469452526811/20000000000000),(22761334633/5000000000000),(-2758949661/100000000000000),(16720899/100000000000000)⟩
def e396 : ℝ := (317119/100000000000000)
theorem h396 : Model (fun x => f396 ((9/8)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(51180518369369/12500000000000),(921138751377/50000000000000),(-568312801/6250000000000),(10637403/25000000000000)⟩
def e397 : ℝ := (1515549/100000000000000)
theorem h397 : Model (fun x => f397 ((9/8)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(414249511689351/50000000000000),(2795848572709/50000000000000),(-1331829081/6250000000000),(62339423/100000000000000)⟩
def e398 : ℝ := (1283307/25000000000000)
theorem h398 : Model (fun x => f398 ((9/8)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(838222547378341/50000000000000),(15086194811387/100000000000000),(-40521688033/100000000000000),(13397027/100000000000000)⟩
def e399 : ℝ := (14867561/100000000000000)
theorem h399 : Model (fun x => f399 ((9/8)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(439017473636311/25000000000000),(31424251700349/100000000000000),(38195806053/100000000000000),(-375108703/50000000000000)⟩
def e400 : ℝ := (33572521/100000000000000)
theorem h400 : Model (fun x => f400 ((9/8)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(20469452526811/2500000000000),(22761334633/625000000000),(-2758949661/12500000000000),(16720899/12500000000000)⟩
def e401 : ℝ := (317119/12500000000000)
theorem h401 : Model (fun x => f401 ((9/8)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(461763861379641/50000000000000),(2286818829357/50000000000000),(-12823351391/50000000000000),(71437503/50000000000000)⟩
def e402 : ℝ := (3418263/100000000000000)
theorem h402 : Model (fun x => f402 ((9/8)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(511763861379641/50000000000000),(2286818829357/50000000000000),(-12823351391/50000000000000),(71437503/50000000000000)⟩
def e403 : ℝ := (3418263/100000000000000)
theorem h403 : Model (fun x => f403 ((9/8)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(898693110085013/5000000000000),(401952201832987/100000000000000),(1377802047121/100000000000000),(-1148204483/10000000000000)⟩
def e404 : ℝ := (407308051/100000000000000)
theorem h404 : Model (fun x => f404 ((9/8)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(55636345087/10000000000000),(-12442040091/100000000000000),(235594701/100000000000000),(-395947/10000000000000)⟩
def e405 : ℝ := (15527/20000000000000)
theorem h405 : Model (fun x => f405 ((9/8)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (17570520308467271/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(580034515327/25000000000000),(111196596993/25000000000000),(-1842424873/50000000000000),(625211/2000000000000)⟩
def e406 : ℝ := (1270833/100000000000000)
theorem h406 : Model (fun x => f406 ((9/8)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(939077545001/20000000000000),(910955289059/100000000000000),(-5423548603/100000000000000),(38589681/100000000000000)⟩
def e407 : ℝ := (44437/2500000000000)
theorem h407 : Model (fun x => f407 ((9/8)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(14187211951971/50000000000000),(34534562279/625000000000),(-14182050639/50000000000000),(71967519/25000000000000)⟩
def e408 : ℝ := (12722493/100000000000000)
theorem h408 : Model (fun x => f408 ((9/8)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(25221710136837/100000000000000),(870219948661/20000000000000),(-121903639877/100000000000000),(1482427143/50000000000000)⟩
def e409 : ℝ := (45764967/50000000000000)
theorem h409 : Model (fun x => f409 ((9/8)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1919231496449/100000000000000),(-286496168423/100000000000000),(414395967/2500000000000),(-506855961/100000000000000)⟩
def e410 : ℝ := (63365637/12500000000000)
theorem h410 : Model (fun x => f410 ((9/8)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(85095977783203/25000000000000),(8565216064453/25000000000000),(5589/409600),(549/2048000)⟩
def e411 : ℝ := (129882813/50000000000000)
theorem h411 : Model (fun x => f411 ((9/8)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(1089/64),(33/160),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((9/8)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(35937/512),(3267/2560),(99/12800),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((9/8)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(23891360574960673/100000000000000),(2839139699935877/100000000000000),(71064527034759/50000000000000),(3893187332153/100000000000000)⟩
def e414 : ℝ := (16023543609/25000000000000)
theorem h414 : Model (fun x => f414 ((9/8)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(104640336081/25000000000000),(-248699551/500000000000),(1710426359/50000000000000),(-178823223/100000000000000)⟩
def e415 : ℝ := (123499/1000000000000)
theorem h415 : Model (fun x => f415 ((9/8)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (20906134539448689/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1014430200007/50000000000000),(81687409181/25000000000000),(-3384617601/25000000000000),(198682257/50000000000000)⟩
def e416 : ℝ := (33298871/20000000000000)
theorem h416 : Model (fun x => f416 ((9/8)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(21925780713/20000000000000),(40253468301/100000000000000),(759342069/25000000000000),(-109491447/100000000000000)⟩
def e417 : ℝ := (673419451/100000000000000)
theorem h417 : Model (fun x => f417 ((9/8)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((9/8)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((54983970103/1000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (11/10) (23/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (11/10) (23/20) ≤ (27828694777/500000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(9/8)-(1/40)) (by norm_num : ((9/8):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel2


noncomputable section
namespace Hf4Quad.Panel3
open Hf4Quad.Dag

def p0 : Cubic := ⟨(47/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((47/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((47/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((47/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((47/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(205904761904761/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((47/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-205904761904761/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((47/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-11447619047619/10000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((47/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((47/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(2209/1600),(47/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((47/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(83567989417989/50000000000000),(7112169312169/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((47/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-83567989417989/50000000000000),(-7112169312169/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((47/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-35201521164021/12500000000000),(-11493121693121/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((47/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((47/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(103823/64000),(6627/64000),(141/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((47/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1580476860532407/100000000000000),(100881501736111/100000000000000),(429282986111/20000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((47/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1580476860532407/100000000000000),(-100881501736111/100000000000000),(-429282986111/20000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((47/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-74483561193783/4000000000000),(-7023413964327/6250000000000),(-277759538277/12500000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((47/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((47/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(4879681/2560000),(103823/640000),(6627/1280000),(47/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((47/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(266252435515873/50000000000000),(45319563492063/100000000000000),(1446369047619/100000000000000),(4103174603/20000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((47/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1329584158812829/100000000000000),(-67055059937169/100000000000000),(-775707258597/100000000000000),(529307209/10000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((47/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((47/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(223969733398437/100000000000000),(5956641845703/25000000000000),(103823/10240000),(2209/10240000)⟩
def e22 : ℝ := (230468751/100000000000000)
theorem h22 : Model (fun x => f22 ((47/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(1459121337214261/100000000000000),(155225674171727/100000000000000),(3302673918547/50000000000000),(70269657841/50000000000000)⟩
def e23 : ℝ := (375365309/25000000000000)
theorem h23 : Model (fun x => f23 ((47/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(16192147300179/12500000000000),(44085307117279/50000000000000),(5829640578497/100000000000000),(36458096943/25000000000000)⟩
def e24 : ℝ := (1610588229/100000000000000)
theorem h24 : Model (fun x => f24 ((47/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((47/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(263164436743163/100000000000000),(6719092001953/20000000000000),(178699255371/10000000000000),(25347412109/50000000000000)⟩
def e26 : ℝ := (101983643/12500000000000)
theorem h26 : Model (fun x => f26 ((47/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(295468219454493/50000000000000),(15087738865761/20000000000000),(4012696506849/100000000000000),(56917680947/50000000000000)⟩
def e27 : ℝ := (458009081/25000000000000)
theorem h27 : Model (fun x => f27 ((47/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(360236808655209/50000000000000),(163609308563363/100000000000000),(4921168542673/50000000000000),(129833874833/50000000000000)⟩
def e28 : ℝ := (3442624553/100000000000000)
theorem h28 : Model (fun x => f28 ((47/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((47/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(9663069161663/3125000000000),(11513444107513/25000000000000),(2939602750853/100000000000000),(52120616149/50000000000000)⟩
def e30 : ℝ := (2246413581/100000000000000)
theorem h30 : Model (fun x => f30 ((47/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(18344493202141/25000000000000),(10928634248083/100000000000000),(697572398813/100000000000000),(12368304943/50000000000000)⟩
def e31 : ℝ := (66634689/12500000000000)
theorem h31 : Model (fun x => f31 ((47/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(396925795059491/50000000000000),(87268971405723/50000000000000),(10539909484159/100000000000000),(2221909059/781250000000)⟩
def e32 : ℝ := (795140413/20000000000000)
theorem h32 : Model (fun x => f32 ((47/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((47/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(947661/320),(20163/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((47/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((47/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(103823/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((47/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(2608829/320),(7567/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((47/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((47/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(3338429/320),(7567/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((47/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-3338429/320),(-7567/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((47/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((47/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(87/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((47/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(7569/1600),(87/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((47/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((47/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(158949/160),(1827/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((47/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(50330609189/50000000000000),(-1157025499/50000000000000),(3989743/10000000000000),(-122291/20000000000000)⟩
def e46 : ℝ := (9079/100000000000000)
theorem h46 : Model (fun x => f46 ((47/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (77637/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1050157283151401/100000000000000),(42289283023/12500000000000),(-796350627/20000000000000),(46838919/100000000000000)⟩
def e47 : ℝ := (188798803/100000000000000)
theorem h47 : Model (fun x => f47 ((47/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((47/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(127/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((47/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((47/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((47/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(26458333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/25000000000000)
theorem h52 : Model (fun x => f52 ((47/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(51458333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/25000000000000)
theorem h53 : Model (fun x => f53 ((47/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((47/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(51458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((47/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((47/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1080624999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((47/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((47/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(1458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((47/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(31518229166659/50000000000000),(9260416666651/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (69/100000000000000)
theorem h60 : Model (fun x => f60 ((47/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(6619900173611/6250000000000),(857638888887/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((47/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((47/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(51458333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((47/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(283771267361109/25000000000000),(5024305555547/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((47/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(308771267361109/25000000000000),(5024305555547/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((47/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(778553885181373/100000000000000),(117541167896211/100000000000000),(91665744357/10000000000000),(1992549189/100000000000000)⟩
def e66 : ℝ := (633843/100000000000000)
theorem h66 : Model (fun x => f66 ((47/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(101458333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((47/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(102937934027777/25000000000000),(1690972222219/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((47/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(835512897858787/100000000000000),(5146896701379/100000000000000),(2642144097/25000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (43/100000000000000)
theorem h69 : Model (fun x => f69 ((47/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(3252459063735531/50000000000000),(63883936393847/6250000000000),(13790795725499/100000000000000),(9538270539/12500000000000)⟩
def e70 : ℝ := (1668287/781250000000)
theorem h70 : Model (fun x => f70 ((47/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((47/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(139017903645831/781250000000),(18010416666627/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((47/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(519000173610983/100000000000000),(78345312499869/100000000000000),(608854166663/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (587/100000000000000)
theorem h73 : Model (fun x => f73 ((47/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(4336313390429259/100000000000000),(85162199202489/12500000000000),(4587129163081/50000000000000),(49808425203/100000000000000)⟩
def e74 : ℝ := (66370707/50000000000000)
theorem h74 : Model (fun x => f74 ((47/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(10841231517900321/100000000000000),(212930071990183/12500000000000),(22965054051661/100000000000000),(25222917903/20000000000000)⟩
def e75 : ℝ := (6925643/2000000000000)
theorem h75 : Model (fun x => f75 ((47/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((47/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(46339301215277/781250000000),(6003472222209/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((47/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(21267361111/25000000000000),(4861111111/20000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((47/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(2481192129/100000000000000),(212673611/20000000000000),(75954861/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/50000000000000)
theorem h79 : Model (fun x => f79 ((47/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(147170188081/100000000000000),(32132299587/50000000000000),(595221499/6250000000000),(12576507/2500000000000)⟩
def e80 : ℝ := (145163/4000000000000)
theorem h80 : Model (fun x => f80 ((47/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(298632839981/100000000000000),(131016791607/100000000000000),(4898156791/25000000000000),(132559323/12500000000000)⟩
def e81 : ℝ := (4737603/50000000000000)
theorem h81 : Model (fun x => f81 ((47/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(5420765075370151/50000000000000),(1703571592713071/100000000000000),(919385867153/4000000000000),(127175064099/100000000000000)⟩
def e82 : ℝ := (88939339/25000000000000)
theorem h82 : Model (fun x => f82 ((47/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(72368103/100000000000000),(20676601/50000000000000),(44307/500000000000),(421971/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((47/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(131921/6250000000000),(376917/25000000000000),(215381/50000000000000),(61537/100000000000000)⟩
def e84 : ℝ := (1131/25000000000000)
theorem h84 : Model (fun x => f84 ((47/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(61563/100000000000000),(1649/3125000000000),(3769/20000000000000),(3589/100000000000000)⟩
def e85 : ℝ := (41/10000000000000)
theorem h85 : Model (fun x => f85 ((47/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(359/20000000000000),(359/20000000000000),(769/100000000000000),(183/100000000000000)⟩
def e86 : ℝ := (31/100000000000000)
theorem h86 : Model (fun x => f86 ((47/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(1077/20000000000000),(1077/20000000000000),(2307/100000000000000),(549/100000000000000)⟩
def e87 : ℝ := (93/100000000000000)
theorem h87 : Model (fun x => f87 ((47/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-1077/20000000000000),(-1077/20000000000000),(-2307/100000000000000),(-549/100000000000000)⟩
def e88 : ℝ := (93/100000000000000)
theorem h88 : Model (fun x => f88 ((47/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(10841530150734917/100000000000000),(851785796353843/50000000000000),(11492323338259/50000000000000),(2543501271/2000000000000)⟩
def e89 : ℝ := (355757449/100000000000000)
theorem h89 : Model (fun x => f89 ((47/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(139017903645831/625000000000),(18010416666627/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((47/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(423848730476279/25000000000000),(13925214964287/100000000000000),(42890805843/100000000000000),(7339289/12500000000000)⟩
def e91 : ℝ := (1891/6250000000000)
theorem h91 : Model (fun x => f91 ((47/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(188552198316029271/50000000000000),(3075421801621921/50000000000000),(10200290887331/25000000000000),(35269221559/25000000000000)⟩
def e92 : ℝ := (269146839/100000000000000)
theorem h92 : Model (fun x => f92 ((47/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(26517855769/100000000000000),(-432525277/100000000000000),(4185673/100000000000000),(-6279/20000000000000)⟩
def e93 : ℝ := (249/100000000000000)
theorem h93 : Model (fun x => f93 ((47/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (370912610519232301/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(718735332131/25000000000000),(10121457489/2500000000000),(-12805489/1562500000000),(2211931/100000000000000)⟩
def e94 : ℝ := (251961/100000000000000)
theorem h94 : Model (fun x => f94 ((47/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(26458333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/12500000000000)
theorem h95 : Model (fun x => f95 ((47/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(48582995951417/100000000000000),(-98346145651/50000000000000),(159265013/20000000000000),(-3223989/100000000000000)⟩
def e96 : ℝ := (1311/10000000000000)
theorem h96 : Model (fun x => f96 ((47/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (40999999999999/20000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(25708502024291/25000000000000),(1966922913/500000000000),(-318530027/20000000000000),(3223987/50000000000000)⟩
def e97 : ℝ := (20427/25000000000000)
theorem h97 : Model (fun x => f97 ((47/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(539878542510111/25000000000000),(41305381173/500000000000),(-6689130567/20000000000000),(67703727/50000000000000)⟩
def e98 : ℝ := (428967/25000000000000)
theorem h98 : Model (fun x => f98 ((47/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(708502024291/25000000000000),(1966922913/500000000000),(-318530027/20000000000000),(3223987/50000000000000)⟩
def e99 : ℝ := (20427/25000000000000)
theorem h99 : Model (fun x => f99 ((47/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(1224016128767/2000000000000),(4364657686701/50000000000000),(-2843557591/100000000000000),(-60028857/50000000000000)⟩
def e100 : ℝ := (171451/5000000000000)
theorem h100 : Model (fun x => f100 ((47/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(4229933288531/4000000000000),(809066267047/100000000000000),(-43201441/2500000000000),(36547/5000000000000)⟩
def e101 : ℝ := (244997/100000000000000)
theorem h101 : Model (fun x => f101 ((47/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(25708502024291/2500000000000),(1966922913/50000000000),(-318530027/2000000000000),(3223987/5000000000000)⟩
def e102 : ℝ := (20427/2500000000000)
theorem h102 : Model (fun x => f102 ((47/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(226817682636983/20000000000000),(4742912093047/100000000000000),(-1765455899/10000000000000),(1630267/2500000000000)⟩
def e103 : ℝ := (1062077/100000000000000)
theorem h103 : Model (fun x => f103 ((47/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(246817682636983/20000000000000),(4742912093047/100000000000000),(-1765455899/10000000000000),(1630267/2500000000000)⟩
def e104 : ℝ := (1062077/100000000000000)
theorem h104 : Model (fun x => f104 ((47/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(188818015257851/25000000000000),(11063017002313/10000000000000),(368127007257/100000000000000),(-623539689/20000000000000)⟩
def e105 : ℝ := (43742779/100000000000000)
theorem h105 : Model (fun x => f105 ((47/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(50708502024291/25000000000000),(1966922913/500000000000),(-318530027/20000000000000),(3223987/50000000000000)⟩
def e106 : ℝ := (20427/25000000000000)
theorem h106 : Model (fun x => f106 ((47/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(411416348407603/100000000000000),(1595835432247/100000000000000),(-491335791/10000000000000),(1703361/12500000000000)⟩
def e107 : ℝ := (408413/100000000000000)
theorem h107 : Model (fun x => f107 ((47/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(834492269442133/100000000000000),(606918181849/12500000000000),(-1280076657/12500000000000),(4711757/50000000000000)⟩
def e108 : ℝ := (701389/50000000000000)
theorem h108 : Model (fun x => f108 ((47/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(1260537392512667/20000000000000),(959871284200309/100000000000000),(4183061929167/50000000000000),(-9700574641/50000000000000)⟩
def e109 : ℝ := (139578213/25000000000000)
theorem h109 : Model (fun x => f109 ((47/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(88828599059151/500000000000),(16990391607987/12500000000000),(-907230261/312500000000),(767487/625000000000)⟩
def e110 : ℝ := (5144937/12500000000000)
theorem h110 : Model (fun x => f110 ((47/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(31467621124171/6250000000000),(14747935063787/20000000000000),(7610230469/3125000000000),(-1078910067/50000000000000)⟩
def e111 : ℝ := (3731009/12500000000000)
theorem h111 : Model (fun x => f111 ((47/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(840303570107349/20000000000000),(319898838719989/50000000000000),(556097345431/10000000000000),(-3421674037/25000000000000)⟩
def e112 : ℝ := (381636303/100000000000000)
theorem h112 : Model (fun x => f112 ((47/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(131302560163751/1250000000000),(1599668961640287/100000000000000),(3481774328161/25000000000000),(-3308784543/10000000000000)⟩
def e113 : ℝ := (187989831/20000000000000)
theorem h113 : Model (fun x => f113 ((47/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(29609533019717/500000000000),(5663463869329/12500000000000),(-302410087/312500000000),(255829/625000000000)⟩
def e114 : ℝ := (1714979/12500000000000)
theorem h114 : Model (fun x => f114 ((47/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(80316018947/100000000000000),(22297101847/100000000000000),(145724263/10000000000000),(-760313/6250000000000)⟩
def e115 : ℝ := (81581/100000000000000)
theorem h115 : Model (fun x => f115 ((47/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(28452031/1250000000000),(947852507/100000000000000),(127732581/100000000000000),(2518937/50000000000000)⟩
def e116 : ℝ := (72637/100000000000000)
theorem h116 : Model (fun x => f116 ((47/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(134792216219/100000000000000),(14290554331/25000000000000),(7991451753/100000000000000),(44411823/12500000000000)⟩
def e117 : ℝ := (649909/10000000000000)
theorem h117 : Model (fun x => f117 ((47/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(273404454759/100000000000000),(14559333539/12500000000000),(16432102477/100000000000000),(751193681/100000000000000)⟩
def e118 : ℝ := (3621863/25000000000000)
theorem h118 : Model (fun x => f118 ((47/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(10504478217554839/100000000000000),(1599785436308599/100000000000000),(13943529415121/100000000000000),(-32336651749/100000000000000)⟩
def e119 : ℝ := (954436607/100000000000000)
theorem h119 : Model (fun x => f119 ((47/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(16126657/25000000000000),(35816289/100000000000000),(3656203/50000000000000),(19697/3125000000000)⟩
def e120 : ℝ := (5067/25000000000000)
theorem h120 : Model (fun x => f120 ((47/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(1828123/100000000000000),(253759/20000000000000),(173551/50000000000000),(23031/50000000000000)⟩
def e121 : ℝ := (379/12500000000000)
theorem h121 : Model (fun x => f121 ((47/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(51809/100000000000000),(43149/100000000000000),(14799/100000000000000),(53/2000000000000)⟩
def e122 : ℝ := (69/25000000000000)
theorem h122 : Model (fun x => f122 ((47/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(367/25000000000000),(713/50000000000000),(147/25000000000000),(33/25000000000000)⟩
def e123 : ℝ := (11/50000000000000)
theorem h123 : Model (fun x => f123 ((47/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(1101/25000000000000),(2139/50000000000000),(441/25000000000000),(99/25000000000000)⟩
def e124 : ℝ := (33/50000000000000)
theorem h124 : Model (fun x => f124 ((47/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-1101/25000000000000),(-2139/50000000000000),(-441/25000000000000),(-99/25000000000000)⟩
def e125 : ℝ := (33/50000000000000)
theorem h125 : Model (fun x => f125 ((47/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(2100895643510087/20000000000000),(1599785436304321/100000000000000),(13943529413357/100000000000000),(-6467330429/20000000000000)⟩
def e126 : ℝ := (954436673/100000000000000)
theorem h126 : Model (fun x => f126 ((47/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(88828599059151/400000000000),(16990391607987/10000000000000),(-907230261/250000000000),(767487/500000000000)⟩
def e127 : ℝ := (5144937/10000000000000)
theorem h127 : Model (fun x => f127 ((47/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1692634117370463/100000000000000),(3282763930973/25000000000000),(-7480904063/50000000000000),(-11172931/25000000000000)⟩
def e128 : ℝ := (2025363/50000000000000)
theorem h128 : Model (fun x => f128 ((47/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(187942896707175991/50000000000000),(579188486061879/10000000000000),(12845151191143/100000000000000),(-80398871089/100000000000000)⟩
def e129 : ℝ := (1785682223/100000000000000)
theorem h129 : Model (fun x => f129 ((47/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(26603825351/100000000000000),(-102482121/25000000000000),(5407303/100000000000000),(-63621/100000000000000)⟩
def e130 : ℝ := (171/20000000000000)
theorem h130 : Model (fun x => f130 ((47/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (370080981217988737/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(279459303903/10000000000000),(76508655031/20000000000000),(-71264219/3125000000000),(7030453/50000000000000)⟩
def e131 : ℝ := (503409/100000000000000)
theorem h131 : Model (fun x => f131 ((47/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(2834767183777/50000000000000),(157480314943/20000000000000),(-96875197/3125000000000),(16272837/100000000000000)⟩
def e132 : ℝ := (75537/10000000000000)
theorem h132 : Model (fun x => f132 ((47/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-59539028081641/100000000000000),(-8249774141041/100000000000000),(437413587/1250000000000),(-42014997/20000000000000)⟩
def e133 : ℝ := (20681071/100000000000000)
theorem h133 : Model (fun x => f133 ((47/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(85106382978723/100000000000000),(-1810774105931/100000000000000),(9631777159/25000000000000),(-204931429/25000000000000)⟩
def e134 : ℝ := (17820127/100000000000000)
theorem h134 : Model (fun x => f134 ((47/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (23/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-50671513260971/100000000000000),(-5942967071929/100000000000000),(78113729259/50000000000000),(-3502775701/100000000000000)⟩
def e135 : ℝ := (115350699/100000000000000)
theorem h135 : Model (fun x => f135 ((47/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(4879681/256000),(103823/64000),(6627/128000),(47/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((47/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((47/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(934407/32000),(59643/32000),(1269/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((47/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(12354937/256000),(223109/64000),(11703/128000),(13/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((47/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-2209/1600),(-47/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((47/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(12001497/256000),(219349/64000),(11623/128000),(13/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((47/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((47/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(141/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((47/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-141/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((47/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(10196697/256000),(209749/64000),(11623/128000),(13/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((47/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(10964697/256000),(209749/64000),(11623/128000),(13/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((47/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((47/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(10964697/4000),(209749/1000),(11623/2000),(13/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((47/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((47/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(922259709/512000),(19622547/128000),(1252503/256000),(8883/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((47/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(3469738479/6250000000000),(-472475027/10000000000000),(251316503/100000000000000),(-133679/1250000000000)⟩
def e151 : ℝ := (4843/1000000000000)
theorem h151 : Model (fun x => f151 ((47/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (420614397/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(152178524365903/100000000000000),(-1306976958097/100000000000000),(5130211243/25000000000000),(-225483797/50000000000000)⟩
def e152 : ℝ := (1291659661/50000000000000)
theorem h152 : Model (fun x => f152 ((47/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(167/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((47/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(21209/1600),(147/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((47/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(261/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((47/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3831417624521/50000000000000),(-88078566081/100000000000000),(1012397311/100000000000000),(-11636751/100000000000000)⟩
def e156 : ℝ := (8457/6250000000000)
theorem h156 : Model (fun x => f156 ((47/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (129/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(50787835249041/50000000000000),(30063691813/12500000000000),(1012397309/50000000000000),(-11636753/50000000000000)⟩
def e157 : ℝ := (3331373/100000000000000)
theorem h157 : Model (fun x => f157 ((47/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(100787835249041/50000000000000),(30063691813/12500000000000),(1012397309/50000000000000),(-11636753/50000000000000)⟩
def e158 : ℝ := (3331373/100000000000000)
theorem h158 : Model (fun x => f158 ((47/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(100787835249041/100000000000000),(30063691813/25000000000000),(1012397309/100000000000000),(-11636753/100000000000000)⟩
def e159 : ℝ := (1665687/100000000000000)
theorem h159 : Model (fun x => f159 ((47/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(787835249041/100000000000000),(30063691813/25000000000000),(1012397309/100000000000000),(-11636753/100000000000000)⟩
def e160 : ℝ := (1665687/100000000000000)
theorem h160 : Model (fun x => f160 ((47/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((47/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((47/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(185977553138111/50000000000000),(221898677667/50000000000000),(934057041/25000000000000),(-1073629/2500000000000)⟩
def e163 : ℝ := (307359/5000000000000)
theorem h163 : Model (fun x => f163 ((47/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2727669391990507/100000000000000),(221898677667/50000000000000),(934057041/25000000000000),(-1073629/2500000000000)⟩
def e164 : ℝ := (6147181/100000000000000)
theorem h164 : Model (fun x => f164 ((47/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((47/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(274915893293791/10000000000000),(149097849043/4000000000000),(15957101243/50000000000000),(-175854831/50000000000000)⟩
def e166 : ℝ := (25855647/50000000000000)
theorem h166 : Model (fun x => f166 ((47/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4015769942659431/50000000000000),(149097849043/4000000000000),(15957101243/50000000000000),(-175854831/50000000000000)⟩
def e167 : ℝ := (10342259/20000000000000)
theorem h167 : Model (fun x => f167 ((47/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((47/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(8094815187576191/100000000000000),(6707560978587/50000000000000),(29489789819/25000000000000),(-1212976099/100000000000000)⟩
def e169 : ℝ := (23320659/12500000000000)
theorem h169 : Model (fun x => f169 ((47/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(1336386280662381/10000000000000),(6707560978587/50000000000000),(29489789819/25000000000000),(-1212976099/100000000000000)⟩
def e170 : ℝ := (186565273/100000000000000)
theorem h170 : Model (fun x => f170 ((47/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((47/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(105227718972249/781250000000),(7397873282659/25000000000000),(270316194231/100000000000000),(-2499986213/100000000000000)⟩
def e172 : ℝ := (412938613/100000000000000)
theorem h172 : Model (fun x => f172 ((47/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(15804862314162157/100000000000000),(7397873282659/25000000000000),(270316194231/100000000000000),(-2499986213/100000000000000)⟩
def e173 : ℝ := (206469307/50000000000000)
theorem h173 : Model (fun x => f173 ((47/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((47/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(15929378590535523/100000000000000),(48830725734631/100000000000000),(468039022443/100000000000000),(-746840637/20000000000000)⟩
def e175 : ℝ := (684219913/100000000000000)
theorem h175 : Model (fun x => f175 ((47/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(653270381716659/4000000000000),(48830725734631/100000000000000),(468039022443/100000000000000),(-746840637/20000000000000)⟩
def e176 : ℝ := (342109957/50000000000000)
theorem h176 : Model (fun x => f176 ((47/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((47/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(4115106725346047/25000000000000),(68855150830821/100000000000000),(139157993709/20000000000000),(-4606908883/100000000000000)⟩
def e178 : ℝ := (484412323/50000000000000)
theorem h178 : Model (fun x => f178 ((47/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(822140392688257/5000000000000),(68855150830821/100000000000000),(139157993709/20000000000000),(-4606908883/100000000000000)⟩
def e179 : ℝ := (968824647/100000000000000)
theorem h179 : Model (fun x => f179 ((47/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((47/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(16572350089969183/100000000000000),(17834175258817/20000000000000),(59408737049/6250000000000),(-502280437/10000000000000)⟩
def e181 : ℝ := (1259313193/100000000000000)
theorem h181 : Model (fun x => f181 ((47/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(4143920855825629/25000000000000),(17834175258817/20000000000000),(59408737049/6250000000000),(-502280437/10000000000000)⟩
def e182 : ℝ := (629656597/50000000000000)
theorem h182 : Model (fun x => f182 ((47/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(130589076778223/100000000000000),(5158892279111/25000000000000),(282532690213/100000000000000),(38695103/50000000000000)⟩
def e183 : ℝ := (37000551/12500000000000)
theorem h183 : Model (fun x => f183 ((47/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(50790938670939/50000000000000),(121202176697/50000000000000),(1092679377/50000000000000),(-21021951/100000000000000)⟩
def e184 : ℝ := (844909/25000000000000)
theorem h184 : Model (fun x => f184 ((47/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(200787835249041/100000000000000),(30063691813/25000000000000),(1012397309/100000000000000),(-11636753/100000000000000)⟩
def e185 : ℝ := (1665687/100000000000000)
theorem h185 : Model (fun x => f185 ((47/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(10078938695999/2500000000000),(241456943949/50000000000000),(1052538343/25000000000000),(-44295457/100000000000000)⟩
def e186 : ℝ := (671101/10000000000000)
theorem h186 : Model (fun x => f186 ((47/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(202372828237743/25000000000000),(1454448512441/100000000000000),(13115758953/100000000000000),(-6295121/5000000000000)⟩
def e187 : ℝ := (20274273/100000000000000)
theorem h187 : Model (fun x => f187 ((47/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(50792502618853/3125000000000),(486725947157/12500000000000),(1813958021/5000000000000),(-158249063/50000000000000)⟩
def e188 : ℝ := (5443159/10000000000000)
theorem h188 : Model (fun x => f188 ((47/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1651071286692909/100000000000000),(1973836609631/25000000000000),(81811760193/100000000000000),(-49015121/10000000000000)⟩
def e189 : ℝ := (111297409/100000000000000)
theorem h189 : Model (fun x => f189 ((47/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((47/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(100787835249041/12500000000000),(30063691813/3125000000000),(1012397309/12500000000000),(-11636753/12500000000000)⟩
def e191 : ℝ := (1665687/12500000000000)
theorem h191 : Model (fun x => f191 ((47/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(453942279667103/50000000000000),(120444249141/10000000000000),(5142268613/50000000000000),(-4564639/4000000000000)⟩
def e192 : ℝ := (4176283/25000000000000)
theorem h192 : Model (fun x => f192 ((47/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(503942279667103/50000000000000),(120444249141/10000000000000),(5142268613/50000000000000),(-4564639/4000000000000)⟩
def e193 : ℝ := (4176283/25000000000000)
theorem h193 : Model (fun x => f193 ((47/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(1664089256217843/10000000000000),(3978487272009/4000000000000),(544734023581/50000000000000),(-2513459507/50000000000000)⟩
def e194 : ℝ := (87930727/6250000000000)
theorem h194 : Model (fun x => f194 ((47/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(600929304881/100000000000000),(-1795869409/50000000000000),(-17874709/100000000000000),(104703/20000000000000)⟩
def e195 : ℝ := (54527/100000000000000)
theorem h195 : Model (fun x => f195 ((47/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (16540334478520397/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(784748031333/100000000000000),(59657381743/50000000000000),(933303567/100000000000000),(-12687671/100000000000000)⟩
def e196 : ℝ := (964147/50000000000000)
theorem h196 : Model (fun x => f196 ((47/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(50787835249041/25000000000000),(30063691813/6250000000000),(1012397309/25000000000000),(-11636753/25000000000000)⟩
def e197 : ℝ := (3331373/50000000000000)
theorem h197 : Model (fun x => f197 ((47/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(12402290384661/25000000000000),(-59191053759/100000000000000),(-427692243/100000000000000),(3416317/50000000000000)⟩
def e198 : ℝ := (416337/50000000000000)
theorem h198 : Model (fun x => f198 ((47/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (201333109564081/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(25195419230677/25000000000000),(59191053757/50000000000000),(855384483/100000000000000),(-13665271/100000000000000)⟩
def e199 : ℝ := (78883/1562500000000)
theorem h199 : Model (fun x => f199 ((47/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(195419230677/25000000000000),(59191053757/50000000000000),(855384483/100000000000000),(-13665271/100000000000000)⟩
def e200 : ℝ := (78883/1562500000000)
theorem h200 : Model (fun x => f200 ((47/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(371932379119517/100000000000000),(218443174579/50000000000000),(789194017/25000000000000),(-25215679/50000000000000)⟩
def e201 : ℝ := (2328927/12500000000000)
theorem h201 : Model (fun x => f201 ((47/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1363823332416901/50000000000000),(218443174579/50000000000000),(789194017/25000000000000),(-25215679/50000000000000)⟩
def e202 : ℝ := (18631417/100000000000000)
theorem h202 : Model (fun x => f202 ((47/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1374484024672911/50000000000000),(3669346996293/100000000000000),(27030513447/100000000000000),(-416091761/100000000000000)⟩
def e203 : ℝ := (156620333/100000000000000)
theorem h203 : Model (fun x => f203 ((47/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(4015674500863387/50000000000000),(3669346996293/100000000000000),(27030513447/100000000000000),(-416091761/100000000000000)⟩
def e204 : ℝ := (78310167/50000000000000)
theorem h204 : Model (fun x => f204 ((47/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8094128203455411/100000000000000),(528228385801/4000000000000),(4011382727/4000000000000),(-181682943/12500000000000)⟩
def e205 : ℝ := (564451731/100000000000000)
theorem h205 : Model (fun x => f205 ((47/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(1336317582250303/10000000000000),(528228385801/4000000000000),(4011382727/4000000000000),(-181682943/12500000000000)⟩
def e206 : ℝ := (141112933/25000000000000)
theorem h206 : Model (fun x => f206 ((47/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(13467632684048431/100000000000000),(364106809991/1250000000000),(231008199313/100000000000000),(-3059260547/100000000000000)⟩
def e207 : ℝ := (1247544183/100000000000000)
theorem h207 : Model (fun x => f207 ((47/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(3950836742440679/25000000000000),(364106809991/1250000000000),(231008199313/100000000000000),(-3059260547/100000000000000)⟩
def e208 : ℝ := (155943023/12500000000000)
theorem h208 : Model (fun x => f208 ((47/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(637075123441633/4000000000000),(48064571112451/100000000000000),(100619075023/25000000000000),(-1180027711/25000000000000)⟩
def e209 : ℝ := (82551369/4000000000000)
theorem h209 : Model (fun x => f209 ((47/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16329259038421777/100000000000000),(48064571112451/100000000000000),(100619075023/25000000000000),(-1180027711/25000000000000)⟩
def e210 : ℝ := (1031892113/50000000000000)
theorem h210 : Model (fun x => f210 ((47/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(1645690108797433/10000000000000),(67771201763939/100000000000000),(602200164703/100000000000000),(-95325743/1562500000000)⟩
def e211 : ℝ := (2918018469/100000000000000)
theorem h211 : Model (fun x => f211 ((47/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(8219641020177641/50000000000000),(67771201763939/100000000000000),(602200164703/100000000000000),(-95325743/1562500000000)⟩
def e212 : ℝ := (291801847/10000000000000)
theorem h212 : Model (fun x => f212 ((47/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(828389205716181/5000000000000),(10970265268489/12500000000000),(206938867261/25000000000000),(-7102407321/100000000000000)⟩
def e213 : ℝ := (3789166757/100000000000000)
theorem h213 : Model (fun x => f213 ((47/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(16571117447656953/100000000000000),(10970265268489/12500000000000),(206938867261/25000000000000),(-7102407321/100000000000000)⟩
def e214 : ℝ := (1894583379/50000000000000)
theorem h214 : Model (fun x => f214 ((47/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(129532600923173/100000000000000),(4060650865773/20000000000000),(126055895291/50000000000000),(-294694021/50000000000000)⟩
def e215 : ℝ := (888700801/100000000000000)
theorem h215 : Model (fun x => f215 ((47/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(10156946403353/10000000000000),(119307473129/50000000000000),(932142443/50000000000000),(-5103787/20000000000000)⟩
def e216 : ℝ := (10213267/100000000000000)
theorem h216 : Model (fun x => f216 ((47/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(50195419230677/25000000000000),(59191053757/50000000000000),(855384483/100000000000000),(-13665271/100000000000000)⟩
def e217 : ℝ := (78883/1562500000000)
theorem h217 : Model (fun x => f217 ((47/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(201566408939473/50000000000000),(237689580643/50000000000000),(893763463/25000000000000),(-52849477/100000000000000)⟩
def e218 : ℝ := (20310291/100000000000000)
theorem h218 : Model (fun x => f218 ((47/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(404708415981557/50000000000000),(178963922207/12500000000000),(5594576257/50000000000000),(-30580543/20000000000000)⟩
def e219 : ℝ := (15319463/25000000000000)
theorem h219 : Model (fun x => f219 ((47/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1625160688510197/100000000000000),(3832818817001/100000000000000),(3885535517/12500000000000),(-49014631/12500000000000)⟩
def e220 : ℝ := (164327943/100000000000000)
theorem h220 : Model (fun x => f220 ((47/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1650667001003433/100000000000000),(3885424916649/50000000000000),(14203088889/20000000000000),(-333684237/50000000000000)⟩
def e221 : ℝ := (41878563/12500000000000)
theorem h221 : Model (fun x => f221 ((47/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(25195419230677/3125000000000),(59191053757/6250000000000),(855384483/12500000000000),(-13665271/12500000000000)⟩
def e222 : ℝ := (78883/195312500000)
theorem h222 : Model (fun x => f222 ((47/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(453911439707597/50000000000000),(118567180637/10000000000000),(34829443/400000000000),(-134841103/100000000000000)⟩
def e223 : ℝ := (50601363/100000000000000)
theorem h223 : Model (fun x => f223 ((47/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(503911439707597/50000000000000),(118567180637/10000000000000),(34829443/400000000000),(-134841103/100000000000000)⟩
def e224 : ℝ := (50601363/100000000000000)
theorem h224 : Model (fun x => f224 ((47/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(16635799699069227/100000000000000),(3915515831717/4000000000000),(475788101591/50000000000000),(-7433023731/100000000000000)⟩
def e225 : ℝ := (529010847/12500000000000)
theorem h225 : Model (fun x => f225 ((47/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(300556636317/50000000000000),(-3537053491/100000000000000),(-13571357/100000000000000),(13769/2500000000000)⟩
def e226 : ℝ := (79427/50000000000000)
theorem h226 : Model (fun x => f226 ((47/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (16536948561962613/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(778637656537/100000000000000),(29365979791/25000000000000),(779761137/100000000000000),(-14502233/100000000000000)⟩
def e227 : ℝ := (5712009/100000000000000)
theorem h227 : Model (fun x => f227 ((47/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(156338568787/10000000000000),(4735573653/2000000000000),(6691659/390625000000),(-1699369/6250000000000)⟩
def e228 : ℝ := (7640303/100000000000000)
theorem h228 : Model (fun x => f228 ((47/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(594784317487/25000000000000),(339893214563/100000000000000),(-166906283/100000000000000),(-22227933/100000000000000)⟩
def e229 : ℝ := (58651831/100000000000000)
theorem h229 : Model (fun x => f229 ((47/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(2024797676551/100000000000000),(9847600771/4000000000000),(-5380133417/100000000000000),(95553533/100000000000000)⟩
def e230 : ℝ := (2697077/5000000000000)
theorem h230 : Model (fun x => f230 ((47/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-2432335779221/5000000000000),(-2848388526327/50000000000000),(150847325101/100000000000000),(-425902771/12500000000000)⟩
def e231 : ℝ := (169292239/100000000000000)
theorem h231 : Model (fun x => f231 ((47/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((47/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2209/320),(-47/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((47/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(987/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((47/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5687/320),(37/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((47/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((47/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14007/320),(37/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((47/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((47/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(350175/32),(925/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((47/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(9071/1600),(73/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((47/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(18671/1600),(73/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((47/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((47/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3528819/1600),(13797/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((47/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(9068189669/20000000000000),(-354548683/100000000000000),(5200849/100000000000000),(-29829/50000000000000)⟩
def e244 : ℝ := (189/25000000000000)
theorem h244 : Model (fun x => f244 ((47/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (875259/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(496164580834699/100000000000000),(-314635395557/25000000000000),(19855329/2000000000000),(-75170389/100000000000000)⟩
def e245 : ℝ := (15875933/100000000000000)
theorem h245 : Model (fun x => f245 ((47/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(423/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((47/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(36049/1600),(407/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((47/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(69649/1600),(407/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((47/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(16129/1600),(127/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((47/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1123368721/2560000),(7704963/640000),(146267/1280000),(267/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((47/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((47/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(68121/160),(783/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((47/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(46975235243/20000000000000),(-5399452327/100000000000000),(18618801/20000000000000),(-1426729/100000000000000)⟩
def e253 : ℝ := (1059/5000000000000)
theorem h253 : Model (fun x => f253 ((47/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (33273/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(25766850553517/25000000000000),(458309818199/100000000000000),(671663971/25000000000000),(-3040767/12500000000000)⟩
def e254 : ℝ := (18561251/100000000000000)
theorem h254 : Model (fun x => f254 ((47/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(50766850553517/25000000000000),(458309818199/100000000000000),(671663971/25000000000000),(-3040767/12500000000000)⟩
def e255 : ℝ := (18561251/100000000000000)
theorem h255 : Model (fun x => f255 ((47/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(50766850553517/50000000000000),(229154909099/100000000000000),(671663971/50000000000000),(-3040767/25000000000000)⟩
def e256 : ℝ := (4640313/50000000000000)
theorem h256 : Model (fun x => f256 ((47/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(766850553517/50000000000000),(229154909099/100000000000000),(671663971/50000000000000),(-3040767/25000000000000)⟩
def e257 : ℝ := (4640313/50000000000000)
theorem h257 : Model (fun x => f257 ((47/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(74941541293287/20000000000000),(21142268399/2500000000000),(991503957/20000000000000),(-44887513/100000000000000)⟩
def e258 : ℝ := (34249931/100000000000000)
theorem h258 : Model (fun x => f258 ((47/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(34130274902259/1250000000000),(21142268399/2500000000000),(991503957/20000000000000),(-44887513/100000000000000)⟩
def e259 : ℝ := (8562483/25000000000000)
theorem h259 : Model (fun x => f259 ((47/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(554459700900299/20000000000000),(355777856917/5000000000000),(43650016713/100000000000000),(-354958237/100000000000000)⟩
def e260 : ℝ := (288473721/100000000000000)
theorem h260 : Model (fun x => f260 ((47/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8054679456882447/100000000000000),(355777856917/5000000000000),(43650016713/100000000000000),(-354958237/100000000000000)⟩
def e261 : ℝ := (144236861/50000000000000)
theorem h261 : Model (fun x => f261 ((47/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8178214164880693/100000000000000),(25682381904577/100000000000000),(168825885777/100000000000000),(-143060869/12500000000000)⟩
def e262 : ℝ := (1042854797/100000000000000)
theorem h262 : Model (fun x => f262 ((47/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(1680907722991039/12500000000000),(25682381904577/100000000000000),(168825885777/100000000000000),(-143060869/12500000000000)⟩
def e263 : ℝ := (521427399/50000000000000)
theorem h263 : Model (fun x => f263 ((47/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(682675129338709/5000000000000),(2275653335897/4000000000000),(410908434141/100000000000000),(-2065768139/100000000000000)⟩
def e264 : ℝ := (2315156971/100000000000000)
theorem h264 : Model (fun x => f264 ((47/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(3197843374497693/20000000000000),(2275653335897/4000000000000),(410908434141/100000000000000),(-2065768139/100000000000000)⟩
def e265 : ℝ := (578789243/25000000000000)
theorem h265 : Model (fun x => f265 ((47/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(16234443668667887/100000000000000),(4720197589867/5000000000000),(762367442631/100000000000000),(-1168188071/50000000000000)⟩
def e266 : ℝ := (770286149/20000000000000)
theorem h266 : Model (fun x => f266 ((47/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(16636824621048839/100000000000000),(4720197589867/5000000000000),(762367442631/100000000000000),(-1168188071/50000000000000)⟩
def e267 : ℝ := (1925715373/50000000000000)
theorem h267 : Model (fun x => f267 ((47/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(1689198378443717/10000000000000),(8373495411779/6250000000000),(1213878284261/100000000000000),(-690300189/50000000000000)⟩
def e268 : ℝ := (5478931847/100000000000000)
theorem h268 : Model (fun x => f268 ((47/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(8437182368409061/50000000000000),(8373495411779/6250000000000),(1213878284261/100000000000000),(-690300189/50000000000000)⟩
def e269 : ℝ := (684866481/12500000000000)
theorem h269 : Model (fun x => f269 ((47/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(2141645881948957/12500000000000),(174699152031399/100000000000000),(1766186018277/100000000000000),(1127182617/100000000000000)⟩
def e270 : ℝ := (223672027/3125000000000)
theorem h270 : Model (fun x => f270 ((47/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(17136500388924989/100000000000000),(174699152031399/100000000000000),(1766186018277/100000000000000),(1127182617/100000000000000)⟩
def e271 : ℝ := (1431500973/20000000000000)
theorem h271 : Model (fun x => f271 ((47/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(65705674042957/25000000000000),(1677939788707/4000000000000),(328809547777/50000000000000),(865409581/20000000000000)⟩
def e272 : ℝ := (2172857/125000000000)
theorem h272 : Model (fun x => f272 ((47/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(4123636984197/4000000000000),(465338920953/100000000000000),(1626490439/50000000000000),(-18542623/100000000000000)⟩
def e273 : ℝ := (9463371/50000000000000)
theorem h273 : Model (fun x => f273 ((47/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(100766850553517/50000000000000),(229154909099/100000000000000),(671663971/50000000000000),(-3040767/25000000000000)⟩
def e274 : ℝ := (4640313/50000000000000)
theorem h274 : Model (fun x => f274 ((47/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(406158326818993/100000000000000),(923648739151/100000000000000),(2969818381/50000000000000),(-42868759/100000000000000)⟩
def e275 : ℝ := (18743997/50000000000000)
theorem h275 : Model (fun x => f275 ((47/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(818545908392719/100000000000000),(2792195233859/100000000000000),(488574863/2500000000000),(-10977771/10000000000000)⟩
def e276 : ℝ := (113549767/100000000000000)
theorem h276 : Model (fun x => f276 ((47/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(824822932222019/50000000000000),(7502952529241/100000000000000),(28389964259/50000000000000),(-59626827/25000000000000)⟩
def e277 : ℝ := (305662463/100000000000000)
theorem h277 : Model (fun x => f277 ((47/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(850317587181133/50000000000000),(3852826850053/25000000000000),(147111776163/100000000000000),(-8695657/20000000000000)⟩
def e278 : ℝ := (630870161/100000000000000)
theorem h278 : Model (fun x => f278 ((47/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(50766850553517/6250000000000),(229154909099/12500000000000),(671663971/6250000000000),(-3040767/3125000000000)⟩
def e279 : ℝ := (4640313/6250000000000)
theorem h279 : Model (fun x => f279 ((47/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(915360533461197/100000000000000),(459715638749/20000000000000),(6999802207/50000000000000),(-115847167/100000000000000)⟩
def e280 : ℝ := (372687/400000000000)
theorem h280 : Model (fun x => f280 ((47/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1015360533461197/100000000000000),(459715638749/20000000000000),(6999802207/50000000000000),(-115847167/100000000000000)⟩
def e281 : ℝ := (372687/400000000000)
theorem h281 : Model (fun x => f281 ((47/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(17267578378633461/100000000000000),(39114152461037/20000000000000),(2086038063441/100000000000000),(3127402261/100000000000000)⟩
def e282 : ℝ := (1604224729/20000000000000)
theorem h282 : Model (fun x => f282 ((47/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(289560000271/50000000000000),(-3279525869/50000000000000),(865117/20000000000000),(638499/100000000000000)⟩
def e283 : ℝ := (56387/20000000000000)
theorem h283 : Model (fun x => f283 ((47/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (17069910429738929/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(761029399747/50000000000000),(45138689243/20000000000000),(1068348857/100000000000000),(-14582139/100000000000000)⟩
def e284 : ℝ := (11058877/100000000000000)
theorem h284 : Model (fun x => f284 ((47/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(25766850553517/12500000000000),(458309818199/50000000000000),(671663971/12500000000000),(-3040767/6250000000000)⟩
def e285 : ℝ := (18561251/50000000000000)
theorem h285 : Model (fun x => f285 ((47/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(12311183246263/25000000000000),(-22228426991/20000000000000),(-200342643/50000000000000),(1654793/20000000000000)⟩
def e286 : ℝ := (1137139/25000000000000)
theorem h286 : Model (fun x => f286 ((47/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (101303181426299/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(50755267014947/50000000000000),(111142134953/50000000000000),(100171321/12500000000000),(-8273967/50000000000000)⟩
def e287 : ℝ := (3481177/12500000000000)
theorem h287 : Model (fun x => f287 ((47/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(755267014947/50000000000000),(111142134953/50000000000000),(100171321/12500000000000),(-8273967/50000000000000)⟩
def e288 : ℝ := (3481177/12500000000000)
theorem h288 : Model (fun x => f288 ((47/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(187311104459923/50000000000000),(164066961121/20000000000000),(2957439/100000000000),(-61069757/100000000000000)⟩
def e289 : ℝ := (10277761/10000000000000)
theorem h289 : Model (fun x => f289 ((47/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2730336494634131/100000000000000),(164066961121/20000000000000),(2957439/100000000000),(-61069757/100000000000000)⟩
def e290 : ℝ := (102777611/100000000000000)
theorem h290 : Model (fun x => f290 ((47/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1385789578258097/50000000000000),(6901834785077/100000000000000),(26705700431/100000000000000),(-20026347/4000000000000)⟩
def e291 : ℝ := (173084057/20000000000000)
theorem h291 : Model (fun x => f291 ((47/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4026980054448573/50000000000000),(6901834785077/100000000000000),(26705700431/100000000000000),(-20026347/4000000000000)⟩
def e292 : ℝ := (432710143/50000000000000)
theorem h292 : Model (fun x => f292 ((47/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(65404943336769/800000000000),(996351030991/4000000000000),(106992858057/100000000000000),(-345262691/20000000000000)⟩
def e293 : ℝ := (156369191/5000000000000)
theorem h293 : Model (fun x => f293 ((47/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(105036449501123/781250000000),(996351030991/4000000000000),(106992858057/100000000000000),(-345262691/20000000000000)⟩
def e294 : ℝ := (3127383821/100000000000000)
theorem h294 : Model (fun x => f294 ((47/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(109182014274181/800000000000),(55170407937603/100000000000000),(271718904533/100000000000000),(-221235281/6250000000000)⟩
def e295 : ℝ := (3469981921/50000000000000)
theorem h295 : Model (fun x => f295 ((47/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(1598346606998691/10000000000000),(55170407937603/100000000000000),(271718904533/100000000000000),(-221235281/6250000000000)⟩
def e296 : ℝ := (6939963843/100000000000000)
theorem h296 : Model (fun x => f296 ((47/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(16224901764130623/100000000000000),(3661300263331/4000000000000),(526545242371/100000000000000),(-1038411893/20000000000000)⟩
def e297 : ℝ := (11541917099/100000000000000)
theorem h297 : Model (fun x => f297 ((47/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(665091308660463/4000000000000),(3661300263331/4000000000000),(526545242371/100000000000000),(-1038411893/20000000000000)⟩
def e298 : ℝ := (115419171/1000000000000)
theorem h298 : Model (fun x => f298 ((47/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(3375688696038233/20000000000000),(64937485117617/50000000000000),(871207401373/100000000000000),(-1223603449/20000000000000)⟩
def e299 : ℝ := (16420853551/100000000000000)
theorem h299 : Model (fun x => f299 ((47/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(16860824432572117/100000000000000),(64937485117617/50000000000000),(871207401373/100000000000000),(-1223603449/20000000000000)⟩
def e300 : ℝ := (1026303347/6250000000000)
theorem h300 : Model (fun x => f300 ((47/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(42788782308367/250000000000),(169315736347027/100000000000000),(163522074943/12500000000000),(-6023213279/100000000000000)⟩
def e301 : ℝ := (10732947251/50000000000000)
theorem h301 : Model (fun x => f301 ((47/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(17118846256680133/100000000000000),(169315736347027/100000000000000),(163522074943/12500000000000),(-6023213279/100000000000000)⟩
def e302 : ℝ := (21465894503/100000000000000)
theorem h302 : Model (fun x => f302 ((47/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(64646499558097/25000000000000),(40610074233479/100000000000000),(133327024141/25000000000000),(268183843/20000000000000)⟩
def e303 : ℝ := (2609176981/50000000000000)
theorem h303 : Model (fun x => f303 ((47/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(51521942595171/50000000000000),(112820974723/25000000000000),(530263513/25000000000000),(-30033151/100000000000000)⟩
def e304 : ℝ := (5673187/10000000000000)
theorem h304 : Model (fun x => f304 ((47/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(100755267014947/50000000000000),(111142134953/50000000000000),(100171321/12500000000000),(-8273967/50000000000000)⟩
def e305 : ℝ := (3481177/12500000000000)
theorem h305 : Model (fun x => f305 ((47/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(40606495325013/10000000000000),(55990777419/6250000000000),(930948797/25000000000000),(-63129019/100000000000000)⟩
def e306 : ℝ := (56215351/50000000000000)
theorem h306 : Model (fun x => f306 ((47/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(51141478487661/6250000000000),(676963887507/25000000000000),(3187315911/25000000000000),(-44737619/25000000000000)⟩
def e307 : ℝ := (170203851/50000000000000)
theorem h307 : Model (fun x => f307 ((47/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(103055466411269/6250000000000),(3637742786413/50000000000000),(38267570299/100000000000000),(-17838809/4000000000000)⟩
def e308 : ℝ := (458051791/50000000000000)
theorem h308 : Model (fun x => f308 ((47/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(1699077703859191/100000000000000),(466815832193/3125000000000),(53619640249/50000000000000),(-78468193/12500000000000)⟩
def e309 : ℝ := (1891144413/100000000000000)
theorem h309 : Model (fun x => f309 ((47/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(50755267014947/6250000000000),(111142134953/6250000000000),(100171321/1562500000000),(-8273967/6250000000000)⟩
def e310 : ℝ := (3481177/1562500000000)
theorem h310 : Model (fun x => f310 ((47/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(457564078714747/50000000000000),(111477902907/5000000000000),(2133004649/25000000000000),(-162416623/100000000000000)⟩
def e311 : ℝ := (139763599/50000000000000)
theorem h311 : Model (fun x => f311 ((47/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(507564078714747/50000000000000),(111477902907/5000000000000),(2133004649/25000000000000),(-162416623/100000000000000)⟩
def e312 : ℝ := (139763599/50000000000000)
theorem h312 : Model (fun x => f312 ((47/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(431195404712029/2500000000000),(189522850450211/100000000000000),(9791471987/625000000000),(-1366630587/25000000000000)⟩
def e313 : ℝ := (24060652193/100000000000000)
theorem h313 : Model (fun x => f313 ((47/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(57978354423/10000000000000),(-6370790873/100000000000000),(17341381/100000000000000),(57187/10000000000000)⟩
def e314 : ℝ := (836909/100000000000000)
theorem h314 : Model (fun x => f314 ((47/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (2132087146917311/12500000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(749619532717/50000000000000),(218976554531/100000000000000),(17177877/3125000000000),(-2210049/12500000000000)⟩
def e315 : ℝ := (8334911/25000000000000)
theorem h315 : Model (fun x => f315 ((47/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(94415558279/3125000000000),(222335000373/50000000000000),(1618040921/100000000000000),(-32262531/100000000000000)⟩
def e316 : ℝ := (44398521/100000000000000)
theorem h316 : Model (fun x => f316 ((47/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(14990609887287/100000000000000),(433654151069/20000000000000),(2461783521/100000000000000),(-178295557/100000000000000)⟩
def e317 : ℝ := (221488913/100000000000000)
theorem h317 : Model (fun x => f317 ((47/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(159474573269/1250000000000),(1573890730899/100000000000000),(-31391901917/100000000000000),(516171907/100000000000000)⟩
def e318 : ℝ := (41868897/20000000000000)
theorem h318 : Model (fun x => f318 ((47/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-358887497229/1000000000000),(-824577264351/20000000000000),(7465963949/6250000000000),(-2891050261/100000000000000)⟩
def e319 : ℝ := (94659181/25000000000000)
theorem h319 : Model (fun x => f319 ((47/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((47/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-24299/1600),(-517/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((47/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((47/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(4559/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((47/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(158061/1600),(1423/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((47/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((47/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(330861/1600),(1423/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((47/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1654305/32),(7115/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((47/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((47/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(427095538086893873/50000000000000),(6679443903453109/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (55573/50000000000000)
theorem h329 : Model (fun x => f329 ((47/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(5853491261/50000000000000),(-91544077/100000000000000),(1342853/100000000000000),(-3851/25000000000000)⟩
def e330 : ℝ := (99/50000000000000)
theorem h330 : Model (fun x => f330 ((47/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (423732941327223207/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(605216241283037/100000000000000),(47339178083/10000000000000),(4295815277/50000000000000),(-2615609/6250000000000)⟩
def e331 : ℝ := (9754437/50000000000000)
theorem h331 : Model (fun x => f331 ((47/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((47/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(407/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((47/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((47/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((47/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(485806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((47/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((47/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((47/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1077638604279251/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (253/25000000000000)
theorem h339 : Model (fun x => f339 ((47/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3584193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((47/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((47/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((47/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2019722791441239/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (253/25000000000000)
theorem h343 : Model (fun x => f343 ((47/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2475587254443/50000000000000),(-3453478957/50000000000000),(9635303/100000000000000),(-6721/50000000000000)⟩
def e344 : ℝ := (23/100000000000000)
theorem h344 : Model (fun x => f344 ((47/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1008452624902873/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(53355767872989/50000000000000),(118678516789/12500000000000),(-52978623/4000000000000),(923817/50000000000000)⟩
def e345 : ℝ := (221/6250000000000)
theorem h345 : Model (fun x => f345 ((47/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(103355767872989/50000000000000),(118678516789/12500000000000),(-52978623/4000000000000),(923817/50000000000000)⟩
def e346 : ℝ := (221/6250000000000)
theorem h346 : Model (fun x => f346 ((47/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(103355767872989/100000000000000),(118678516789/25000000000000),(-165558197/25000000000000),(923817/100000000000000)⟩
def e347 : ℝ := (1769/100000000000000)
theorem h347 : Model (fun x => f347 ((47/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(3355767872989/100000000000000),(118678516789/25000000000000),(-165558197/25000000000000),(923817/100000000000000)⟩
def e348 : ℝ := (1769/100000000000000)
theorem h348 : Model (fun x => f348 ((47/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(381432000483649/100000000000000),(1751920962123/100000000000000),(-2443954337/100000000000000),(852331/25000000000000)⟩
def e349 : ℝ := (6531/100000000000000)
theorem h349 : Model (fun x => f349 ((47/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(1368573143098967/50000000000000),(1751920962123/100000000000000),(-2443954337/100000000000000),(852331/25000000000000)⟩
def e350 : ℝ := (1633/25000000000000)
theorem h350 : Model (fun x => f350 ((47/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(4526397699051/160000000000),(14804329822149/100000000000000),(-6167816341/50000000000000),(1121273/20000000000000)⟩
def e351 : ℝ := (20767/20000000000000)
theorem h351 : Model (fun x => f351 ((47/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8111379514287827/100000000000000),(14804329822149/100000000000000),(-6167816341/50000000000000),(1121273/20000000000000)⟩
def e352 : ℝ := (25959/25000000000000)
theorem h352 : Model (fun x => f352 ((47/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(8383578582084509/100000000000000),(26903494180433/50000000000000),(381243363/10000000000000),(-37934653/50000000000000)⟩
def e353 : ℝ := (49679/10000000000000)
theorem h353 : Model (fun x => f353 ((47/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(426644568785379/3125000000000),(26903494180433/50000000000000),(381243363/10000000000000),(-37934653/50000000000000)⟩
def e354 : ℝ := (496791/100000000000000)
theorem h354 : Model (fun x => f354 ((47/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(7055388322504499/50000000000000),(60211781551351/50000000000000),(168957545787/100000000000000),(-290519383/100000000000000)⟩
def e355 : ℝ := (870501/100000000000000)
theorem h355 : Model (fun x => f355 ((47/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(16446490930723283/100000000000000),(60211781551351/50000000000000),(168957545787/100000000000000),(-290519383/100000000000000)⟩
def e356 : ℝ := (435251/50000000000000)
theorem h356 : Model (fun x => f356 ((47/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(1062399811850659/6250000000000),(20253850434649/10000000000000),(637380907627/100000000000000),(-71876071/50000000000000)⟩
def e357 : ℝ := (2585949/100000000000000)
theorem h357 : Model (fun x => f357 ((47/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(2175097242748937/12500000000000),(20253850434649/10000000000000),(637380907627/100000000000000),(-71876071/50000000000000)⟩
def e358 : ℝ := (51719/2000000000000)
theorem h358 : Model (fun x => f358 ((47/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(17984707657819003/100000000000000),(291939167090993/100000000000000),(752507522997/50000000000000),(84831783/5000000000000)⟩
def e359 : ℝ := (188611/3125000000000)
theorem h359 : Model (fun x => f359 ((47/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(3593417722039991/20000000000000),(291939167090993/100000000000000),(752507522997/50000000000000),(84831783/5000000000000)⟩
def e360 : ℝ := (6035553/100000000000000)
theorem h360 : Model (fun x => f360 ((47/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(1857002239749251/10000000000000),(193514132479953/50000000000000),(705603049821/25000000000000),(1782688771/25000000000000)⟩
def e361 : ℝ := (1844237/25000000000000)
theorem h361 : Model (fun x => f361 ((47/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(18573355730825843/100000000000000),(193514132479953/50000000000000),(705603049821/25000000000000),(1782688771/25000000000000)⟩
def e362 : ℝ := (7376949/100000000000000)
theorem h362 : Model (fun x => f362 ((47/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(311639352275507/50000000000000),(50579051286033/50000000000000),(1808992367979/100000000000000),(11246235079/100000000000000)⟩
def e363 : ℝ := (1937449/10000000000000)
theorem h363 : Model (fun x => f363 ((47/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(106824147526151/100000000000000),(49064436931/5000000000000),(884622889/100000000000000),(-4377789/100000000000000)⟩
def e364 : ℝ := (3369/20000000000000)
theorem h364 : Model (fun x => f364 ((47/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(203355767872989/100000000000000),(118678516789/25000000000000),(-165558197/25000000000000),(923817/100000000000000)⟩
def e365 : ℝ := (1769/100000000000000)
theorem h365 : Model (fun x => f365 ((47/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(413535683272129/100000000000000),(482679218233/25000000000000),(-439842687/100000000000000),(-506031/20000000000000)⟩
def e366 : ℝ := (20383/100000000000000)
theorem h366 : Model (fun x => f366 ((47/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(840948664146849/100000000000000),(2944668091803/50000000000000),(2766185117/50000000000000),(-16198739/100000000000000)⟩
def e367 : ℝ := (1153/2000000000000)
theorem h367 : Model (fun x => f367 ((47/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(427529403348367/25000000000000),(15968406425059/100000000000000),(4204857939/12500000000000),(-37910419/100000000000000)⟩
def e368 : ℝ := (95889/50000000000000)
theorem h368 : Model (fun x => f368 ((47/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(182681856220213/10000000000000),(33839305594467/100000000000000),(207758695007/100000000000000),(71198347/20000000000000)⟩
def e369 : ℝ := (636411/50000000000000)
theorem h369 : Model (fun x => f369 ((47/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(103355767872989/12500000000000),(118678516789/3125000000000),(-165558197/3125000000000),(923817/12500000000000)⟩
def e370 : ℝ := (1769/12500000000000)
theorem h370 : Model (fun x => f370 ((47/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(933670290510063/100000000000000),(1194750318967/25000000000000),(-882647883/20000000000000),(3012747/100000000000000)⟩
def e371 : ℝ := (30997/100000000000000)
theorem h371 : Model (fun x => f371 ((47/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1033670290510063/100000000000000),(1194750318967/25000000000000),(-882647883/20000000000000),(3012747/100000000000000)⟩
def e372 : ℝ := (30997/100000000000000)
theorem h372 : Model (fun x => f372 ((47/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(18883280739006513/100000000000000),(109272632710087/25000000000000),(736819775103/20000000000000),(2434039867/20000000000000)⟩
def e373 : ℝ := (11333699/50000000000000)
theorem h373 : Model (fun x => f373 ((47/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(529568994827/100000000000000),(-6128955987/50000000000000),(180415297/100000000000000),(-2125871/100000000000000)⟩
def e374 : ℝ := (1463/6250000000000)
theorem h374 : Model (fun x => f374 ((47/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (18442493916423917/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(3300690770661/100000000000000),(22965049601/5000000000000),(-1695518343/100000000000000),(7066471/100000000000000)⟩
def e375 : ℝ := (34923/6250000000000)
theorem h375 : Model (fun x => f375 ((47/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(53355767872989/25000000000000),(118678516789/6250000000000),(-52978623/2000000000000),(923817/25000000000000)⟩
def e376 : ℝ := (221/3125000000000)
theorem h376 : Model (fun x => f376 ((47/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(48376593806979/100000000000000),(-6943567977/3125000000000),(332626011/25000000000000),(-7967087/100000000000000)⟩
def e377 : ℝ := (24111/50000000000000)
theorem h377 : Model (fun x => f377 ((47/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (205760781294921/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(103246812386041/100000000000000),(17775534021/4000000000000),(-665252023/25000000000000),(15934173/100000000000000)⟩
def e378 : ℝ := (302273/100000000000000)
theorem h378 : Model (fun x => f378 ((47/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(3246812386041/100000000000000),(17775534021/4000000000000),(-665252023/25000000000000),(15934173/100000000000000)⟩
def e379 : ℝ := (302273/100000000000000)
theorem h379 : Model (fun x => f379 ((47/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(190514951426623/50000000000000),(1640004626937/100000000000000),(-9820387007/100000000000000),(29402343/50000000000000)⟩
def e380 : ℝ := (557767/50000000000000)
theorem h380 : Model (fun x => f380 ((47/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2736744188567531/100000000000000),(1640004626937/100000000000000),(-9820387007/100000000000000),(29402343/50000000000000)⟩
def e381 : ℝ := (223107/20000000000000)
theorem h381 : Model (fun x => f381 ((47/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(1412800568928099/50000000000000),(346375621449/2500000000000),(-37838115677/50000000000000),(81902041/20000000000000)⟩
def e382 : ℝ := (10221273/100000000000000)
theorem h382 : Model (fun x => f382 ((47/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(162159641804743/2000000000000),(346375621449/2500000000000),(-37838115677/50000000000000),(81902041/20000000000000)⟩
def e383 : ℝ := (5110637/50000000000000)
theorem h383 : Model (fun x => f383 ((47/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(1674246611400191/20000000000000),(12583949848201/25000000000000),(-46463447939/20000000000000),(1009766437/100000000000000)⟩
def e384 : ℝ := (41213459/100000000000000)
theorem h384 : Model (fun x => f384 ((47/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(6820140338024287/50000000000000),(12583949848201/25000000000000),(-46463447939/20000000000000),(1009766437/100000000000000)⟩
def e385 : ℝ := (2060673/5000000000000)
theorem h385 : Model (fun x => f385 ((47/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(3520788749632319/25000000000000),(56292963332687/50000000000000),(-15165707541/4000000000000),(422093567/50000000000000)⟩
def e386 : ℝ := (6429593/6250000000000)
theorem h386 : Model (fun x => f386 ((47/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(16418869284243561/100000000000000),(56292963332687/50000000000000),(-15165707541/4000000000000),(422093567/50000000000000)⟩
def e387 : ℝ := (102873489/100000000000000)
theorem h387 : Model (fun x => f387 ((47/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(8475979582906131/50000000000000),(18920492286439/10000000000000),(-164020719067/50000000000000),(-74561201/6250000000000)⟩
def e388 : ℝ := (2356349/1250000000000)
theorem h388 : Model (fun x => f388 ((47/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(8677170059096607/50000000000000),(18920492286439/10000000000000),(-164020719067/50000000000000),(-74561201/6250000000000)⟩
def e389 : ℝ := (188507921/100000000000000)
theorem h389 : Model (fun x => f389 ((47/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(17917802982666393/100000000000000),(272468717530687/100000000000000),(5038989099/12500000000000),(-123974467/2500000000000)⟩
def e390 : ℝ := (11283931/4000000000000)
theorem h390 : Model (fun x => f390 ((47/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(3580036787009469/20000000000000),(272468717530687/100000000000000),(5038989099/12500000000000),(-123974467/2500000000000)⟩
def e391 : ℝ := (70524569/25000000000000)
theorem h391 : Model (fun x => f391 ((47/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(18481369324174583/100000000000000),(180430798864729/50000000000000),(388057330753/50000000000000),(-2334753579/25000000000000)⟩
def e392 : ℝ := (73578957/20000000000000)
theorem h392 : Model (fun x => f392 ((47/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(4621175664376979/25000000000000),(180430798864729/50000000000000),(388057330753/50000000000000),(-2334753579/25000000000000)⟩
def e393 : ℝ := (183947393/50000000000000)
theorem h393 : Model (fun x => f393 ((47/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(18755112981463/3125000000000),(18772072858139/20000000000000),(1136946455289/100000000000000),(-877857237/25000000000000)⟩
def e394 : ℝ := (4724021/6250000000000)
theorem h394 : Model (fun x => f394 ((47/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(106599042678783/100000000000000),(917633613063/100000000000000),(-880000501/25000000000000),(9252631/100000000000000)⟩
def e395 : ℝ := (840159/100000000000000)
theorem h395 : Model (fun x => f395 ((47/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(203246812386041/100000000000000),(17775534021/4000000000000),(-665252023/25000000000000),(15934173/100000000000000)⟩
def e396 : ℝ := (302273/100000000000000)
theorem h396 : Model (fun x => f396 ((47/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(82618533490173/20000000000000),(1806410314113/100000000000000),(-2210504547/25000000000000),(41120977/100000000000000)⟩
def e397 : ℝ := (288941/20000000000000)
theorem h397 : Model (fun x => f397 ((47/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(839597678794351/100000000000000),(5507207073071/100000000000000),(-5234018107/25000000000000),(62038351/100000000000000)⟩
def e398 : ℝ := (613163/12500000000000)
theorem h398 : Model (fun x => f398 ((47/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1706455519016709/100000000000000),(2984859420671/20000000000000),(-808405507/2000000000000),(2536153/12500000000000)⟩
def e399 : ℝ := (14261721/100000000000000)
theorem h399 : Model (fun x => f399 ((47/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1819065247011069/100000000000000),(31568167273179/100000000000000),(6759094339/20000000000000),(-2239767/312500000000)⟩
def e400 : ℝ := (4098903/12500000000000)
theorem h400 : Model (fun x => f400 ((47/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(103246812386041/12500000000000),(17775534021/500000000000),(-665252023/3125000000000),(15934173/12500000000000)⟩
def e401 : ℝ := (302273/12500000000000)
theorem h401 : Model (fun x => f401 ((47/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(932573541767111/100000000000000),(4472740417263/100000000000000),(-1240403337/5000000000000),(27345203/20000000000000)⟩
def e402 : ℝ := (3258343/100000000000000)
theorem h402 : Model (fun x => f402 ((47/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1032573541767111/100000000000000),(4472740417263/100000000000000),(-1240403337/5000000000000),(27345203/20000000000000)⟩
def e403 : ℝ := (3258343/100000000000000)
theorem h403 : Model (fun x => f403 ((47/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(18783186448116841/100000000000000),(407326609403079/100000000000000),(1309650355131/100000000000000),(-11233450123/100000000000000)⟩
def e404 : ℝ := (403315081/100000000000000)
theorem h404 : Model (fun x => f404 ((47/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(21295641243/4000000000000),(-1154527397/10000000000000),(213246629/100000000000000),(-3501013/100000000000000)⟩
def e405 : ℝ := (33841/50000000000000)
theorem h405 : Model (fun x => f405 ((47/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (18374538551593427/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(3195217260201/100000000000000),(430413627551/100000000000000),(-3503606573/100000000000000),(1459207/5000000000000)⟩
def e406 : ℝ := (1385373/100000000000000)
theorem h406 : Model (fun x => f406 ((47/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(3247954015431/50000000000000),(889714619571/100000000000000),(-1299781229/25000000000000),(36250611/100000000000000)⟩
def e407 : ℝ := (1944141/100000000000000)
theorem h407 : Model (fun x => f407 ((47/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(7862858084317/20000000000000),(5415448473421/100000000000000),(-834250253/3125000000000),(268504827/100000000000000)⟩
def e408 : ℝ := (3467559/25000000000000)
theorem h408 : Model (fun x => f408 ((47/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(33458970571561/100000000000000),(97424983173/2500000000000),(-105634886187/100000000000000),(619016379/25000000000000)⟩
def e409 : ℝ := (799003/1000000000000)
theorem h409 : Model (fun x => f409 ((47/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-2429779151339/100000000000000),(-45177398967/20000000000000),(13820536997/100000000000000),(-82996949/20000000000000)⟩
def e410 : ℝ := (7164641/1562500000000)
theorem h410 : Model (fun x => f410 ((47/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(414582272460937/100000000000000),(10012227783203/25000000000000),(156839/10240000),(2961/10240000)⟩
def e411 : ℝ := (269531251/100000000000000)
theorem h411 : Model (fun x => f411 ((47/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(27889/1600),(167/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((47/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(4657463/64000),(83667/64000),(501/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((47/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(30170337413167703/100000000000000),(3456455887208581/100000000000000),(167062375366393/100000000000000),(2213291552673/50000000000000)⟩
def e414 : ℝ := (70637151977/100000000000000)
theorem h414 : Model (fun x => f414 ((47/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(82862845243/25000000000000),(-37972630581/100000000000000),(2514975767/100000000000000),(-63245929/50000000000000)⟩
def e415 : ℝ := (418173/5000000000000)
theorem h415 : Model (fun x => f415 ((47/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (13271160965167703/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(2631232058317/100000000000000),(277062090091/100000000000000),(-1422099699/12500000000000),(521297/160000000000)⟩
def e416 : ℝ := (166923817/100000000000000)
theorem h416 : Model (fun x => f416 ((47/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(100726453489/50000000000000),(6396886907/12500000000000),(488747881/20000000000000),(-2229353/2500000000000)⟩
def e417 : ℝ := (625460841/100000000000000)
theorem h417 : Model (fun x => f417 ((47/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((47/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((75615759727/750000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (23/20) (6/5) ∧
    SigmaActualBlockSeparable.endpointCellMass (23/20) (6/5) ≤ (304339421431/3000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(47/40)-(1/40)) (by norm_num : ((47/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel3

