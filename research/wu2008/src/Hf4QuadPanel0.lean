import Hf4QuadDag

noncomputable section
namespace Hf4Quad.Panel0
open Hf4Quad.Dag

def p0 : Cubic := ⟨(41/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((41/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((41/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((41/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((41/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(179619047619047/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((41/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-179619047619047/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((41/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-22047619047619/25000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((41/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((41/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(1681/1600),(41/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((41/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(31796693121693/25000000000000),(775529100529/12500000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((41/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-31796693121693/25000000000000),(-775529100529/12500000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((41/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-1682634755291/781250000000),(-330787037037/3125000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((41/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((41/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(68921/64000),(5043/64000),(123/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((41/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(52458533130787/5000000000000),(19192146267361/25000000000000),(58512641059/3125000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((41/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-52458533130787/5000000000000),(-19192146267361/25000000000000),(-58512641059/3125000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((41/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-316136977823247/25000000000000),(-21838442563657/25000000000000),(-1948065889549/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (7/100000000000000)
theorem h16 : Model (fun x => f16 ((41/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((41/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(2825761/2560000),(68921/640000),(5043/1280000),(41/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((41/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(6167335515873/2000000000000),(30084563492063/100000000000000),(68790922619/6250000000000),(4474206349/25000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((41/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-478090567749669/50000000000000),(-11453841352513/20000000000000),(-169482225529/20000000000000),(2674024471/100000000000000)⟩
def e20 : ℝ := (54563497/50000000000000)
theorem h20 : Model (fun x => f20 ((41/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((41/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(56570410644531/50000000000000),(3449415283203/25000000000000),(68921/10240000),(1681/10240000)⟩
def e22 : ℝ := (50292969/25000000000000)
theorem h22 : Model (fun x => f22 ((41/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(92136437336787/12500000000000),(44944603578919/50000000000000),(4384839373553/100000000000000),(106947301793/100000000000000)⟩
def e23 : ℝ := (16382469/1250000000000)
theorem h23 : Model (fun x => f23 ((41/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(-109544818402521/50000000000000),(32620000395273/100000000000000),(884357061477/25000000000000),(13702665783/12500000000000)⟩
def e24 : ℝ := (709862257/50000000000000)
theorem h24 : Model (fun x => f24 ((41/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((41/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(14496167727661/12500000000000),(8485561596679/50000000000000),(808456707/78125000000),(33652832031/100000000000000)⟩
def e26 : ℝ := (621630863/100000000000000)
theorem h26 : Model (fun x => f26 ((41/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(130204731928451/50000000000000),(9527175506959/25000000000000),(1161850671579/50000000000000),(37783761677/50000000000000)⟩
def e27 : ℝ := (1116699/80000000000)
theorem h27 : Model (fun x => f27 ((41/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(2065991352593/5000000000000),(70728702423109/100000000000000),(2930564794533/50000000000000),(92594424809/50000000000000)⟩
def e28 : ℝ := (351949783/12500000000000)
theorem h28 : Model (fun x => f28 ((41/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((41/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(5943428768341/5000000000000),(5073658704681/25000000000000),(1484973279417/100000000000000),(12072953491/20000000000000)⟩
def e30 : ℝ := (1494033209/100000000000000)
theorem h30 : Model (fun x => f30 ((41/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(3525962701853/12500000000000),(4815949056189/100000000000000),(176193258153/50000000000000),(7162327567/50000000000000)⟩
def e31 : ℝ := (177268227/50000000000000)
theorem h31 : Model (fun x => f31 ((41/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(17381882166671/25000000000000),(37772325739649/50000000000000),(1553379026343/25000000000000),(12469594047/6250000000000)⟩
def e32 : ℝ := (1585067359/50000000000000)
theorem h32 : Model (fun x => f32 ((41/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((41/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(721149/320),(17589/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((41/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((41/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(90569/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((41/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(2170253/320),(35261/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((41/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((41/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(2899853/320),(35261/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((41/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-2899853/320),(-35261/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((41/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((41/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(81/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((41/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(6561/1600),(81/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((41/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((41/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(137781/160),(1701/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((41/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(290315791/250000000000),(-573463291/20000000000000),(13274613/25000000000000),(-874049/100000000000000)⟩
def e46 : ℝ := (3493/25000000000000)
theorem h46 : Model (fun x => f46 ((41/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (67179/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-263085349212101/25000000000000),(391675433813/100000000000000),(-2479693787/50000000000000),(62760443/100000000000000)⟩
def e47 : ℝ := (252323403/100000000000000)
theorem h47 : Model (fun x => f47 ((41/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((41/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(121/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((41/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((41/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((41/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(25208333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/25000000000000)
theorem h52 : Model (fun x => f52 ((41/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(50208333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/25000000000000)
theorem h53 : Model (fun x => f53 ((41/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((41/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(50208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((41/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((41/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1054374999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((41/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((41/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((41/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(8786458333319/100000000000000),(2205729166663/25000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (13/20000000000000)
theorem h60 : Model (fun x => f60 ((41/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(100835069444443/100000000000000),(418402777777/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (7/100000000000000)
theorem h61 : Model (fun x => f61 ((41/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((41/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(50208333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((41/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1105001736111103/100000000000000),(2501736111107/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (37/100000000000000)
theorem h64 : Model (fun x => f64 ((41/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1205001736111103/100000000000000),(2501736111107/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (37/100000000000000)
theorem h65 : Model (fun x => f65 ((41/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(26469243864793/25000000000000),(208507669943/195312500000),(110116034613/12500000000000),(1977358217/100000000000000)⟩
def e66 : ℝ := (633753/100000000000000)
theorem h66 : Model (fun x => f66 ((41/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(100208333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((41/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(16066736111111/4000000000000),(835069444443/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (13/100000000000000)
theorem h68 : Model (fun x => f68 ((41/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(402505211950227/50000000000000),(5020855034713/100000000000000),(2087673611/20000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (41/100000000000000)
theorem h69 : Model (fun x => f69 ((41/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(42616034447843/5000000000000),(216178067505393/25000000000000),(3115669155181/25000000000000),(35649653507/50000000000000)⟩
def e70 : ℝ := (204361357/100000000000000)
theorem h70 : Model (fun x => f70 ((41/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((41/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2117536458333303/12500000000000),(8786458333317/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (147/12500000000000)
theorem h72 : Model (fun x => f72 ((41/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(70584548610997/100000000000000),(17792578124971/25000000000000),(73372395833/12500000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (131/25000000000000)
theorem h73 : Model (fun x => f73 ((41/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(71026621747701/12500000000000),(288236191104629/50000000000000),(4152984785557/50000000000000),(46688610933/100000000000000)⟩
def e74 : ℝ := (63805203/50000000000000)
theorem h74 : Model (fun x => f74 ((41/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(355133415734617/25000000000000),(144118465223083/10000000000000),(10384323095919/50000000000000),(117987917947/100000000000000)⟩
def e75 : ℝ := (331971763/100000000000000)
theorem h75 : Model (fun x => f75 ((41/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((41/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(705845486111101/12500000000000),(2928819444439/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (49/12500000000000)
theorem h77 : Model (fun x => f77 ((41/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(1736111111/100000000000000),(1736111111/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/100000000000000)
theorem h78 : Model (fun x => f78 ((41/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1808449/25000000000000),(5425347/25000000000000),(5425347/25000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((41/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(20423769/5000000000000),(614407989/50000000000000),(247120537/20000000000000),(41866599/10000000000000)⟩
def e80 : ℝ := (3418141/100000000000000)
theorem h80 : Model (fun x => f80 ((41/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(40932637/5000000000000),(2464454003/100000000000000),(2481473781/100000000000000),(422112383/50000000000000)⟩
def e81 : ℝ := (860921/10000000000000)
theorem h81 : Model (fun x => f81 ((41/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(177566810198901/12500000000000),(1441187116684833/100000000000000),(20771127665619/100000000000000),(118832142713/100000000000000)⟩
def e82 : ℝ := (340580973/100000000000000)
theorem h82 : Model (fun x => f82 ((41/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(1507/5000000000000),(120563/100000000000000),(45211/25000000000000),(120563/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((41/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(1/800000000000),(627/100000000000000),(251/20000000000000),(251/20000000000000)⟩
def e84 : ℝ := (757/100000000000000)
theorem h84 : Model (fun x => f84 ((41/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨0,(3/100000000000000),(7/100000000000000),(1/10000000000000)⟩
def e85 : ℝ := (7/50000000000000)
theorem h85 : Model (fun x => f85 ((41/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨0,0,0,0⟩
def e86 : ℝ := (1/100000000000000)
theorem h86 : Model (fun x => f86 ((41/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨0,0,0,0⟩
def e87 : ℝ := (3/100000000000000)
theorem h87 : Model (fun x => f87 ((41/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨0,0,0,0⟩
def e88 : ℝ := (3/100000000000000)
theorem h88 : Model (fun x => f88 ((41/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(177566810198901/12500000000000),(1441187116684833/100000000000000),(20771127665619/100000000000000),(118832142713/100000000000000)⟩
def e89 : ℝ := (21286311/6250000000000)
theorem h89 : Model (fun x => f89 ((41/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2117536458333303/10000000000000),(8786458333317/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (147/10000000000000)
theorem h90 : Model (fun x => f90 ((41/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1613375057900487/100000000000000),(13416840398317/100000000000000),(41840458621/100000000000000),(57990933/100000000000000)⟩
def e91 : ℝ := (30249/100000000000000)
theorem h91 : Model (fun x => f91 ((41/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(34163805060698849/10000000000000),(2838117707179321/50000000000000),(4789908505767/12500000000000),(134721244701/100000000000000)⟩
def e92 : ℝ := (130572133/50000000000000)
theorem h92 : Model (fun x => f92 ((41/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(14635372117/50000000000000),(-486326493/100000000000000),(2398547/50000000000000),(-18349/50000000000000)⟩
def e93 : ℝ := (37/12500000000000)
theorem h93 : Model (fun x => f93 ((41/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (67184672188438949/20000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(207900507431/50000000000000),(414937759331/100000000000000),(-172173347/20000000000000),(595337/25000000000000)⟩
def e94 : ℝ := (111127/50000000000000)
theorem h94 : Model (fun x => f94 ((41/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(25208333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/12500000000000)
theorem h95 : Model (fun x => f95 ((41/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(12448132780083/25000000000000),(-51652003237/25000000000000),(857294659/100000000000000),(-88931/2500000000000)⟩
def e96 : ℝ := (7413/50000000000000)
theorem h96 : Model (fun x => f96 ((41/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (39999999999999/20000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(50207468879667/50000000000000),(413216025893/100000000000000),(-1714589321/100000000000000),(1778619/25000000000000)⟩
def e97 : ℝ := (89441/100000000000000)
theorem h97 : Model (fun x => f97 ((41/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1054356846473007/50000000000000),(8677536543753/100000000000000),(-36006375741/100000000000000),(37350999/25000000000000)⟩
def e98 : ℝ := (1878261/100000000000000)
theorem h98 : Model (fun x => f98 ((41/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(207468879667/50000000000000),(413216025893/100000000000000),(-1714589321/100000000000000),(1778619/25000000000000)⟩
def e99 : ℝ := (89441/100000000000000)
theorem h99 : Model (fun x => f99 ((41/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(8749849348279/100000000000000),(8749549295153/100000000000000),(-448212187/100000000000000),(-146924367/100000000000000)⟩
def e100 : ℝ := (753331/20000000000000)
theorem h100 : Model (fun x => f100 ((41/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(100831597252109/100000000000000),(103732653803/12500000000000),(-1735932759/100000000000000),(118077/100000000000000)⟩
def e101 : ℝ := (268807/100000000000000)
theorem h101 : Model (fun x => f101 ((41/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(50207468879667/5000000000000),(413216025893/10000000000000),(-1714589321/10000000000000),(1778619/2500000000000)⟩
def e102 : ℝ := (89441/10000000000000)
theorem h102 : Model (fun x => f102 ((41/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1104980974845449/100000000000000),(2481010744677/50000000000000),(-18881825969/100000000000000),(71262837/100000000000000)⟩
def e103 : ℝ := (1163217/100000000000000)
theorem h103 : Model (fun x => f103 ((41/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1204980974845449/100000000000000),(2481010744677/50000000000000),(-18881825969/100000000000000),(71262837/100000000000000)⟩
def e104 : ℝ := (1163217/100000000000000)
theorem h104 : Model (fun x => f104 ((41/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(16474065621/15625000000),(21172914759253/20000000000000),(21355075667/5000000000000),(-687698067/20000000000000)⟩
def e105 : ℝ := (9355359/20000000000000)
theorem h105 : Model (fun x => f105 ((41/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(100207468879667/50000000000000),(413216025893/100000000000000),(-1714589321/100000000000000),(1778619/25000000000000)⟩
def e106 : ℝ := (89441/100000000000000)
theorem h106 : Model (fun x => f106 ((41/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(401661472770777/100000000000000),(165629328221/10000000000000),(-5165111401/100000000000000),(14347029/100000000000000)⟩
def e107 : ℝ := (447689/100000000000000)
theorem h107 : Model (fun x => f107 ((41/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(804989590656777/100000000000000),(4979188725979/100000000000000),(-10394430241/100000000000000),(3794001/50000000000000)⟩
def e108 : ℝ := (95383/6250000000000)
theorem h108 : Model (fun x => f108 ((41/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(848732885804907/100000000000000),(857448558089007/100000000000000),(8698360381537/100000000000000),(-1740931781/10000000000000)⟩
def e109 : ℝ := (73759291/12500000000000)
theorem h109 : Model (fun x => f109 ((41/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2117463542294289/12500000000000),(2178385729863/1562500000000),(-36454587939/12500000000000),(2479617/12500000000000)⟩
def e110 : ℝ := (5644947/12500000000000)
theorem h110 : Model (fun x => f110 ((41/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(35144623108441/50000000000000),(7057608206959/10000000000000),(142217775639/50000000000000),(-74695607/3125000000000)⟩
def e111 : ℝ := (3067297/10000000000000)
theorem h111 : Model (fun x => f111 ((41/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(141455278849253/25000000000000),(57162994837679/10000000000000),(362280420931/6250000000000),(-155117559/1250000000000)⟩
def e112 : ℝ := (98523681/25000000000000)
theorem h112 : Model (fun x => f112 ((41/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(1414554001201919/100000000000000),(1429078506465797/100000000000000),(14494847116433/100000000000000),(-2981872253/10000000000000)⟩
def e113 : ℝ := (246042263/25000000000000)
theorem h113 : Model (fun x => f113 ((41/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(705821180764763/12500000000000),(726128576621/1562500000000),(-12151529313/12500000000000),(826539/12500000000000)⟩
def e114 : ℝ := (1881649/12500000000000)
theorem h114 : Model (fun x => f114 ((41/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(1721733441/100000000000000),(1714589319/50000000000000),(1693245883/100000000000000),(-112887/800000000000)⟩
def e115 : ℝ := (3597/4000000000000)
theorem h115 : Model (fun x => f115 ((41/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(3572061/50000000000000),(4268687/20000000000000),(21166311/100000000000000),(3439769/50000000000000)⟩
def e116 : ℝ := (44107/50000000000000)
theorem h116 : Model (fun x => f116 ((41/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(40339781/10000000000000),(151061489/12500000000000),(602541137/50000000000000),(398273599/100000000000000)⟩
def e117 : ℝ := (8205343/100000000000000)
theorem h117 : Model (fun x => f117 ((41/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(808469469/100000000000000),(2423665217/100000000000000),(484030331/20000000000000),(401579343/50000000000000)⟩
def e118 : ℝ := (18110711/100000000000000)
theorem h118 : Model (fun x => f118 ((41/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(353638702417847/25000000000000),(714540465065507/50000000000000),(1812158408511/12500000000000),(-7253890961/25000000000000)⟩
def e119 : ℝ := (1002279763/100000000000000)
theorem h119 : Model (fun x => f119 ((41/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(29643/100000000000000),(59041/50000000000000),(175899/100000000000000),(57821/50000000000000)⟩
def e120 : ℝ := (14459/50000000000000)
theorem h120 : Model (fun x => f120 ((41/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(61/50000000000000),(153/25000000000000),(1217/100000000000000),(301/25000000000000)⟩
def e121 : ℝ := (9/1250000000000)
theorem h121 : Model (fun x => f121 ((41/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨0,(3/100000000000000),(7/100000000000000),(1/10000000000000)⟩
def e122 : ℝ := (13/100000000000000)
theorem h122 : Model (fun x => f122 ((41/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨0,0,0,0⟩
def e123 : ℝ := (1/100000000000000)
theorem h123 : Model (fun x => f123 ((41/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨0,0,0,0⟩
def e124 : ℝ := (3/100000000000000)
theorem h124 : Model (fun x => f124 ((41/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨0,0,0,0⟩
def e125 : ℝ := (3/100000000000000)
theorem h125 : Model (fun x => f125 ((41/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(353638702417847/25000000000000),(714540465065507/50000000000000),(1812158408511/12500000000000),(-7253890961/25000000000000)⟩
def e126 : ℝ := (501139883/50000000000000)
theorem h126 : Model (fun x => f126 ((41/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2117463542294289/10000000000000),(2178385729863/1250000000000),(-36454587939/10000000000000),(2479617/10000000000000)⟩
def e127 : ℝ := (5644947/10000000000000)
theorem h127 : Model (fun x => f127 ((41/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(1613319387083897/100000000000000),(6652691990727/50000000000000),(-351486267/2500000000000),(-5584581/10000000000000)⟩
def e128 : ℝ := (1088517/25000000000000)
theorem h128 : Model (fun x => f128 ((41/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(170807249211335987/50000000000000),(5628912094123433/100000000000000),(1791135013183/12500000000000),(-3377234387/4000000000000)⟩
def e129 : ℝ := (472690379/25000000000000)
theorem h129 : Model (fun x => f129 ((41/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(29272762269/100000000000000),(-120584611/25000000000000),(3359911/50000000000000),(-83259/100000000000000)⟩
def e130 : ℝ := (581/50000000000000)
theorem h130 : Model (fun x => f130 ((41/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (167985585463410943/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(414079266599/100000000000000),(8230170433/2000000000000),(-1277100287/50000000000000),(20543/125000000000)⟩
def e131 : ℝ := (337/80000000000)
theorem h131 : Model (fun x => f131 ((41/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(829880281461/100000000000000),(826446280981/100000000000000),(-3415067309/100000000000000),(4703937/25000000000000)⟩
def e132 : ℝ := (40219/6250000000000)
theorem h132 : Model (fun x => f132 ((41/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-8733173746097/100000000000000),(-1738757180057/20000000000000),(39133997099/100000000000000),(-251847723/100000000000000)⟩
def e133 : ℝ := (11727213/100000000000000)
theorem h133 : Model (fun x => f133 ((41/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(24390243902439/25000000000000),(-1189767995241/50000000000000),(29018731591/50000000000000),(-1415547883/100000000000000)⟩
def e134 : ℝ := (35388699/100000000000000)
theorem h134 : Model (fun x => f134 ((41/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := 1)
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-2130042377097/25000000000000),(-4136966664671/50000000000000),(2399827613/1000000000000),(-6098943177/100000000000000)⟩
def e135 : ℝ := (42595477/25000000000000)
theorem h135 : Model (fun x => f135 ((41/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(2825761/256000),(68921/64000),(5043/128000),(41/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((41/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((41/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(620289/32000),(45387/32000),(1107/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((41/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(7788073/256000),(31939/12800),(9471/128000),(59/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((41/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-1681/1600),(-41/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((41/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(7519113/256000),(31283/12800),(9391/128000),(59/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((41/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((41/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(123/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((41/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-123/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((41/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(5944713/256000),(29363/12800),(9391/128000),(59/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((41/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(6712713/256000),(29363/12800),(9391/128000),(59/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((41/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((41/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(6712713/4000),(29363/200),(9391/2000),(59/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((41/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((41/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(534068829/512000),(13026069/128000),(953127/256000),(7749/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((41/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(958677931/1000000000000),(-374118217/4000000000000),(7128777/1250000000000),(-13909809/50000000000000)⟩
def e151 : ℝ := (737981/50000000000000)
theorem h151 : Model (fun x => f151 ((41/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (240013557/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(2011040565699/1250000000000),(-1621096323479/100000000000000),(34061752619/100000000000000),(-304492159/25000000000000)⟩
def e152 : ℝ := (4784021579/100000000000000)
theorem h152 : Model (fun x => f152 ((41/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(161/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((41/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(19481/1600),(141/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((41/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(243/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((41/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(8230452674897/100000000000000),(-101610526851/100000000000000),(313612737/25000000000000),(-15487049/100000000000000)⟩
def e156 : ℝ := (19359/10000000000000)
theorem h156 : Model (fun x => f156 ((41/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := 12)
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(3131590792181/3125000000000),(1334035081/625000000000),(4900199/195312500000),(-30974101/100000000000000)⟩
def e157 : ℝ := (2173281/50000000000000)
theorem h157 : Model (fun x => f157 ((41/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(6256590792181/3125000000000),(1334035081/625000000000),(4900199/195312500000),(-30974101/100000000000000)⟩
def e158 : ℝ := (2173281/50000000000000)
theorem h158 : Model (fun x => f158 ((41/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(6256590792181/6250000000000),(1334035081/1250000000000),(4900199/390625000000),(-15487051/100000000000000)⟩
def e159 : ℝ := (1086641/50000000000000)
theorem h159 : Model (fun x => f159 ((41/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(6590792181/6250000000000),(1334035081/1250000000000),(4900199/390625000000),(-15487051/100000000000000)⟩
def e160 : ℝ := (1086641/50000000000000)
theorem h160 : Model (fun x => f160 ((41/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((41/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((41/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(46179598704193/12500000000000),(78771595259/20000000000000),(231476067/5000000000000),(-57154593/100000000000000)⟩
def e163 : ℝ := (250639/3125000000000)
theorem h163 : Model (fun x => f163 ((41/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2725151075347829/100000000000000),(78771595259/20000000000000),(231476067/5000000000000),(-57154593/100000000000000)⟩
def e164 : ℝ := (8020449/100000000000000)
theorem h164 : Model (fun x => f164 ((41/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((41/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(136401241002587/5000000000000),(3302631018497/100000000000000),(3924042297/10000000000000),(-469378891/100000000000000)⟩
def e166 : ℝ := (67336811/100000000000000)
theorem h166 : Model (fun x => f166 ((41/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(2002601443108173/25000000000000),(3302631018497/100000000000000),(3924042297/10000000000000),(-469378891/100000000000000)⟩
def e167 : ℝ := (16834203/25000000000000)
theorem h167 : Model (fun x => f167 ((41/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((41/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1603770591917949/20000000000000),(1481880447753/12500000000000),(71646537193/50000000000000),(-13017129/800000000000)⟩
def e169 : ℝ := (24217409/10000000000000)
theorem h169 : Model (fun x => f169 ((41/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3321975144659341/25000000000000),(1481880447753/12500000000000),(71646537193/50000000000000),(-13017129/800000000000)⟩
def e170 : ℝ := (242174091/100000000000000)
theorem h170 : Model (fun x => f170 ((41/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((41/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(6650956512617529/50000000000000),(5209753092477/20000000000000),(40348301279/12500000000000),(-211569927/6250000000000)⟩
def e172 : ℝ := (266776597/50000000000000)
theorem h172 : Model (fun x => f172 ((41/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(15637627310949343/100000000000000),(5209753092477/20000000000000),(40348301279/12500000000000),(-211569927/6250000000000)⟩
def e173 : ℝ := (106710639/20000000000000)
theorem h173 : Model (fun x => f173 ((41/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((41/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(7827058803619503/50000000000000),(4276514931547/10000000000000),(17096660441/3125000000000),(-1284810037/25000000000000)⟩
def e175 : ℝ := (878805657/100000000000000)
theorem h175 : Model (fun x => f175 ((41/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(8028249279809979/50000000000000),(4276514931547/10000000000000),(17096660441/3125000000000),(-1284810037/25000000000000)⟩
def e176 : ℝ := (439402829/50000000000000)
theorem h176 : Model (fun x => f176 ((41/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((41/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(8036715283422857/50000000000000),(59946192194593/100000000000000),(158946224751/20000000000000),(-6510996769/100000000000000)⟩
def e178 : ℝ := (1235970633/100000000000000)
theorem h178 : Model (fun x => f178 ((41/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(8027905759613333/50000000000000),(59946192194593/100000000000000),(158946224751/20000000000000),(-6510996769/100000000000000)⟩
def e179 : ℝ := (617985317/50000000000000)
theorem h179 : Model (fun x => f179 ((41/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((41/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(321454856038999/2000000000000),(38572309857109/50000000000000),(26523943171/2500000000000),(-296171183/4000000000000)⟩
def e181 : ℝ := (1595335931/100000000000000)
theorem h181 : Model (fun x => f181 ((41/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(16076076135283283/100000000000000),(38572309857109/50000000000000),(26523943171/2500000000000),(-296171183/4000000000000)⟩
def e182 : ℝ := (398833983/25000000000000)
theorem h182 : Model (fun x => f182 ((41/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(16952652302973/100000000000000),(8619095344231/50000000000000),(285116200347/100000000000000),(-397492849/100000000000000)⟩
def e183 : ℝ := (180641047/50000000000000)
theorem h183 : Model (fun x => f183 ((41/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(50105508276229/50000000000000),(53417674267/25000000000000),(1312722583/50000000000000),(-5665839/20000000000000)⟩
def e184 : ℝ := (874711/20000000000000)
theorem h184 : Model (fun x => f184 ((41/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(12506590792181/6250000000000),(1334035081/1250000000000),(4900199/390625000000),(-15487051/100000000000000)⟩
def e185 : ℝ := (1086641/50000000000000)
theorem h185 : Model (fun x => f185 ((41/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(1601687687609/400000000000),(106779077507/25000000000000),(2567173527/50000000000000),(-59303297/100000000000000)⟩
def e186 : ℝ := (8720119/100000000000000)
theorem h186 : Model (fun x => f186 ((41/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(160253219886403/20000000000000),(256404907689/20000000000000),(7876517753/50000000000000),(-33969039/20000000000000)⟩
def e187 : ℝ := (209897/800000000000)
theorem h187 : Model (fun x => f187 ((41/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(320675431079783/20000000000000),(684106934949/20000000000000),(10735596431/25000000000000),(-26941721/6250000000000)⟩
def e188 : ℝ := (7015903/10000000000000)
theorem h188 : Model (fun x => f188 ((41/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(25105633540549/1562500000000),(6853699713661/100000000000000),(722167731/781250000000),(-176160361/25000000000000)⟩
def e189 : ℝ := (70760591/50000000000000)
theorem h189 : Model (fun x => f189 ((41/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((41/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(6256590792181/781250000000),(1334035081/156250000000),(4900199/48828125000),(-15487051/12500000000000)⟩
def e191 : ℝ := (1086641/6250000000000)
theorem h191 : Model (fun x => f191 ((41/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(450527318975813/50000000000000),(266863287227/25000000000000),(6330526359/50000000000000),(-152225603/100000000000000)⟩
def e192 : ℝ := (21759811/100000000000000)
theorem h192 : Model (fun x => f192 ((41/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(500527318975813/50000000000000),(266863287227/25000000000000),(6330526359/50000000000000),(-152225603/100000000000000)⟩
def e193 : ℝ := (21759811/100000000000000)
theorem h193 : Model (fun x => f193 ((41/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(3216910194493501/20000000000000),(85760694904921/100000000000000),(600971204791/50000000000000),(-3822634787/50000000000000)⟩
def e194 : ℝ := (1775855121/100000000000000)
theorem h194 : Model (fun x => f194 ((41/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(31085729459/5000000000000),(-132595993/4000000000000),(-28783957/100000000000000),(139339/20000000000000)⟩
def e195 : ℝ := (72611/100000000000000)
theorem h195 : Model (fun x => f195 ((41/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (15997578914028307/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(5269855631/5000000000000),(106610382979/100000000000000),(149537577/12500000000000),(-16766313/100000000000000)⟩
def e196 : ℝ := (584143/25000000000000)
theorem h196 : Model (fun x => f196 ((41/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(3131590792181/1562500000000),(1334035081/312500000000),(4900199/97656250000),(-30974101/50000000000000)⟩
def e197 : ℝ := (2173281/25000000000000)
theorem h197 : Model (fun x => f197 ((41/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(49947329205313/100000000000000),(-26624519477/50000000000000),(-284567853/50000000000000),(1125157/12500000000000)⟩
def e198 : ℝ := (1097613/100000000000000)
theorem h198 : Model (fun x => f198 ((41/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (199994915514281/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(10010534158937/10000000000000),(106498077907/100000000000000),(71141963/6250000000000),(-3600503/20000000000000)⟩
def e199 : ℝ := (3297463/50000000000000)
theorem h199 : Model (fun x => f199 ((41/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(10534158937/10000000000000),(106498077907/100000000000000),(71141963/6250000000000),(-3600503/20000000000000)⟩
def e200 : ℝ := (3297463/50000000000000)
theorem h200 : Model (fun x => f200 ((41/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(73887275935011/20000000000000),(393028620847/100000000000000),(4200763529/100000000000000),(-66437853/100000000000000)⟩
def e201 : ℝ := (1216921/5000000000000)
theorem h201 : Model (fun x => f201 ((41/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(136257533269467/5000000000000),(393028620847/100000000000000),(4200763529/100000000000000),(-66437853/100000000000000)⟩
def e202 : ℝ := (24338421/100000000000000)
theorem h202 : Model (fun x => f202 ((41/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(682005345603247/25000000000000),(411959465269/12500000000000),(7128673491/20000000000000),(-548156033/100000000000000)⟩
def e203 : ℝ := (40846671/20000000000000)
theorem h203 : Model (fun x => f203 ((41/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(400520116739697/5000000000000),(411959465269/12500000000000),(7128673491/20000000000000),(-548156033/100000000000000)⟩
def e204 : ℝ := (51058339/25000000000000)
theorem h204 : Model (fun x => f204 ((41/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8018840619928343/100000000000000),(11830071958511/100000000000000),(26074173097/20000000000000),(-478833529/25000000000000)⟩
def e205 : ℝ := (366976169/50000000000000)
theorem h205 : Model (fun x => f205 ((41/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(6643944119487981/50000000000000),(11830071958511/100000000000000),(26074173097/20000000000000),(-478833529/25000000000000)⟩
def e206 : ℝ := (733952339/100000000000000)
theorem h206 : Model (fun x => f206 ((41/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(415683934738769/3125000000000),(1039755180531/4000000000000),(73589808007/25000000000000),(-4036005041/100000000000000)⟩
def e207 : ℝ := (1615362131/100000000000000)
theorem h207 : Model (fun x => f207 ((41/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(15637600197354893/100000000000000),(1039755180531/4000000000000),(73589808007/25000000000000),(-4036005041/100000000000000)⟩
def e208 : ℝ := (403840533/25000000000000)
theorem h208 : Model (fun x => f208 ((41/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(489189784185691/3125000000000),(42675005520057/100000000000000),(6254382859/1250000000000),(-1561512533/25000000000000)⟩
def e209 : ℝ := (2657551887/100000000000000)
theorem h209 : Model (fun x => f209 ((41/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(2007056755790383/12500000000000),(42675005520057/100000000000000),(6254382859/1250000000000),(-1561512533/25000000000000)⟩
def e210 : ℝ := (166096993/6250000000000)
theorem h210 : Model (fun x => f210 ((41/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(4018342042552981/25000000000000),(5981977498849/10000000000000),(364545896099/50000000000000),(-8124574181/100000000000000)⟩
def e211 : ℝ := (3733773047/100000000000000)
theorem h211 : Model (fun x => f211 ((41/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(4013937280648219/25000000000000),(5981977498849/10000000000000),(364545896099/50000000000000),(-8124574181/100000000000000)⟩
def e212 : ℝ := (466721631/12500000000000)
theorem h212 : Model (fun x => f212 ((41/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(128581300031231/800000000000),(76981854299351/100000000000000),(976324741253/100000000000000),(-9566191241/100000000000000)⟩
def e213 : ℝ := (4815932277/100000000000000)
theorem h213 : Model (fun x => f213 ((41/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(2009499479654651/12500000000000),(76981854299351/100000000000000),(976324741253/100000000000000),(-9566191241/100000000000000)⟩
def e214 : ℝ := (2407966139/50000000000000)
theorem h214 : Model (fun x => f214 ((41/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(8467354761/50000000000),(2150215059989/12500000000000),(66500283833/25000000000000),(-49406561/5000000000000)⟩
def e215 : ℝ := (1088819633/100000000000000)
theorem h215 : Model (fun x => f215 ((41/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(25052698536811/25000000000000),(213220529349/100000000000000),(299044921/12500000000000),(-8404621/25000000000000)⟩
def e216 : ℝ := (2119/16000000000)
theorem h216 : Model (fun x => f216 ((41/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(20010534158937/10000000000000),(106498077907/100000000000000),(71141963/6250000000000),(-3600503/20000000000000)⟩
def e217 : ℝ := (3297463/50000000000000)
theorem h217 : Model (fun x => f217 ((41/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(12513171166437/3125000000000),(426216685163/100000000000000),(583612773/12500000000000),(-34811757/50000000000000)⟩
def e218 : ℝ := (13216801/50000000000000)
theorem h218 : Model (fun x => f218 ((41/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(400632382500181/50000000000000),(255864706127/20000000000000),(14354518429/100000000000000),(-100791257/50000000000000)⟩
def e219 : ℝ := (79458809/100000000000000)
theorem h219 : Model (fun x => f219 ((41/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1603373595039237/100000000000000),(3413326294681/100000000000000),(9801795207/25000000000000),(-32360983/6250000000000)⟩
def e220 : ℝ := (53075383/25000000000000)
theorem h220 : Model (fun x => f220 ((41/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(321350682547207/20000000000000),(6839243053521/100000000000000),(84926198069/100000000000000),(-35705611/4000000000000)⟩
def e221 : ℝ := (106837571/25000000000000)
theorem h221 : Model (fun x => f221 ((41/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(10010534158937/1250000000000),(106498077907/12500000000000),(71141963/781250000000),(-3600503/2500000000000)⟩
def e222 : ℝ := (3297463/6250000000000)
theorem h222 : Model (fun x => f222 ((41/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(225263381715551/25000000000000),(213041030521/20000000000000),(1437316329/12500000000000),(-44409651/25000000000000)⟩
def e223 : ℝ := (33001579/50000000000000)
theorem h223 : Model (fun x => f223 ((41/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(250263381715551/25000000000000),(213041030521/20000000000000),(1437316329/12500000000000),(-44409651/25000000000000)⟩
def e224 : ℝ := (33001579/50000000000000)
theorem h224 : Model (fun x => f224 ((41/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(16084461706172903/100000000000000),(85579703940071/100000000000000),(1107761703749/100000000000000),(-315592831/3125000000000)⟩
def e225 : ℝ := (5359833591/100000000000000)
theorem h225 : Model (fun x => f225 ((41/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(621718039601/100000000000000),(-826985179/25000000000000),(-5043661/20000000000000),(752359/100000000000000)⟩
def e226 : ℝ := (213853/100000000000000)
theorem h226 : Model (fun x => f226 ((41/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (159977587817249/1000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(26321536013/25000000000000),(106386009193/100000000000000),(1080483681/100000000000000),(-19153123/100000000000000)⟩
def e227 : ℝ := (6976549/100000000000000)
theorem h227 : Model (fun x => f227 ((41/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(6583851771/3125000000000),(53249098043/25000000000000),(2276784297/100000000000000),(-8979859/25000000000000)⟩
def e228 : ℝ := (9313121/100000000000000)
theorem h228 : Model (fun x => f228 ((41/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(1324039299/390625000000),(84815032369/25000000000000),(281850191/100000000000000),(-24712973/100000000000000)⟩
def e229 : ℝ := (9198589/25000000000000)
theorem h229 : Model (fun x => f229 ((41/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(66137377667/20000000000000),(322919958309/100000000000000),(-7601120749/100000000000000),(161282971/100000000000000)⟩
def e230 : ℝ := (20551959/50000000000000)
theorem h230 : Model (fun x => f230 ((41/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-8189482620053/100000000000000),(-7951013371033/100000000000000),(232381640551/100000000000000),(-2968830103/50000000000000)⟩
def e231 : ℝ := (105742913/50000000000000)
theorem h231 : Model (fun x => f231 ((41/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((41/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-1681/320),(-41/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((41/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(861/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((41/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5207/320),(43/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((41/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((41/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(13527/320),(43/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((41/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((41/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(338175/32),(1075/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((41/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(8159/1600),(79/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((41/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(17759/1600),(79/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((41/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((41/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3356451/1600),(14931/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((41/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(47669398421/100000000000000),(-84821949/20000000000000),(6457499/100000000000000),(-40667/50000000000000)⟩
def e244 : ℝ := (221/20000000000000)
theorem h244 : Model (fun x => f244 ((41/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := 2079)
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(503768712844427/100000000000000),(-31979770633/2500000000000),(1253028313/50000000000000),(-47168109/50000000000000)⟩
def e245 : ℝ := (5581451/25000000000000)
theorem h245 : Model (fun x => f245 ((41/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(369/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((41/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(31201/1600),(401/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((41/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(64801/1600),(401/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((41/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(14641/1600),(121/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((41/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(948751441/2560000),(6855981/640000),(136763/1280000),(261/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((41/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((41/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(59049/160),(729/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((41/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(135480702467/50000000000000),(-6690405061/100000000000000),(12389639/10000000000000),(-2039447/100000000000000)⟩
def e253 : ℝ := (8149/25000000000000)
theorem h253 : Model (fun x => f253 ((41/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (28791/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(50209965505179/50000000000000),(423161536463/100000000000000),(399643939/12500000000000),(-32937159/100000000000000)⟩
def e254 : ℝ := (751493/3125000000000)
theorem h254 : Model (fun x => f254 ((41/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(100209965505179/50000000000000),(423161536463/100000000000000),(399643939/12500000000000),(-32937159/100000000000000)⟩
def e255 : ℝ := (751493/3125000000000)
theorem h255 : Model (fun x => f255 ((41/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(100209965505179/100000000000000),(211580768231/100000000000000),(399643939/25000000000000),(-823429/5000000000000)⟩
def e256 : ℝ := (12023889/100000000000000)
theorem h256 : Model (fun x => f256 ((41/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(209965505179/100000000000000),(211580768231/100000000000000),(399643939/25000000000000),(-823429/5000000000000)⟩
def e257 : ℝ := (12023889/100000000000000)
theorem h257 : Model (fun x => f257 ((41/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(369822491745303/100000000000000),(780833787519/100000000000000),(2949752883/50000000000000),(-60776903/100000000000000)⟩
def e258 : ℝ := (22186939/50000000000000)
theorem h258 : Model (fun x => f258 ((41/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(681384194364897/25000000000000),(780833787519/100000000000000),(2949752883/50000000000000),(-60776903/100000000000000)⟩
def e259 : ℝ := (44373879/100000000000000)
theorem h259 : Model (fun x => f259 ((41/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(136562973226161/5000000000000),(6549184921293/100000000000000),(12783439241/25000000000000),(-484797279/100000000000000)⟩
def e260 : ℝ := (372536609/100000000000000)
theorem h260 : Model (fun x => f260 ((41/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(2003410104226043/25000000000000),(6549184921293/100000000000000),(12783439241/25000000000000),(-484797279/100000000000000)⟩
def e261 : ℝ := (37253661/10000000000000)
theorem h261 : Model (fun x => f261 ((41/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8030466297488753/100000000000000),(23518257907853/100000000000000),(96601024431/50000000000000),(-1592665091/100000000000000)⟩
def e262 : ℝ := (334940281/25000000000000)
theorem h262 : Model (fun x => f262 ((41/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(3324878479134093/25000000000000),(23518257907853/100000000000000),(96601024431/50000000000000),(-1592665091/100000000000000)⟩
def e263 : ℝ := (10718089/800000000000)
theorem h263 : Model (fun x => f263 ((41/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(13327438308117579/100000000000000),(25853425926237/50000000000000),(455970622411/100000000000000),(-3001514679/100000000000000)⟩
def e264 : ℝ := (368951577/12500000000000)
theorem h264 : Model (fun x => f264 ((41/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(1957894074228983/12500000000000),(25853425926237/50000000000000),(455970622411/100000000000000),(-3001514679/100000000000000)⟩
def e265 : ℝ := (2951612617/100000000000000)
theorem h265 : Model (fun x => f265 ((41/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(784801990565123/5000000000000),(84955636992401/100000000000000),(816717117799/100000000000000),(-3795996297/100000000000000)⟩
def e266 : ℝ := (1215349011/25000000000000)
theorem h266 : Model (fun x => f266 ((41/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(4024605190920853/25000000000000),(84955636992401/100000000000000),(816717117799/100000000000000),(-3795996297/100000000000000)⟩
def e267 : ℝ := (972279209/20000000000000)
theorem h267 : Model (fun x => f267 ((41/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(403305547354143/2500000000000),(2383903536993/2000000000000),(313881795713/25000000000000),(-1684525657/50000000000000)⟩
def e268 : ℝ := (1709275151/25000000000000)
theorem h268 : Model (fun x => f268 ((41/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(1007162677909167/6250000000000),(2383903536993/2000000000000),(313881795713/25000000000000),(-1684525657/50000000000000)⟩
def e269 : ℝ := (1367420121/20000000000000)
theorem h269 : Model (fun x => f269 ((41/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(16148437953821013/100000000000000),(153540846104969/100000000000000),(1767961561997/100000000000000),(-1468092163/100000000000000)⟩
def e270 : ℝ := (8825067261/100000000000000)
theorem h270 : Model (fun x => f270 ((41/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(8075885643577173/50000000000000),(153540846104969/100000000000000),(1767961561997/100000000000000),(-1468092163/100000000000000)⟩
def e271 : ℝ := (4412533631/50000000000000)
theorem h271 : Model (fun x => f271 ((41/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(3391314817843/10000000000000),(6899284917091/20000000000000),(586773311123/100000000000000),(3532083533/100000000000000)⟩
def e272 : ℝ := (999267791/50000000000000)
theorem h272 : Model (fun x => f272 ((41/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(100420371865491/100000000000000),(424050029719/100000000000000),(1825764321/50000000000000),(-26241759/100000000000000)⟩
def e273 : ℝ := (12097103/50000000000000)
theorem h273 : Model (fun x => f273 ((41/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(200209965505179/100000000000000),(211580768231/100000000000000),(399643939/25000000000000),(-823429/5000000000000)⟩
def e274 : ℝ := (12023889/100000000000000)
theorem h274 : Model (fun x => f274 ((41/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(400840302875849/100000000000000),(847211566181/100000000000000),(3424340077/50000000000000),(-59178919/100000000000000)⟩
def e275 : ℝ := (753781/1562500000000)
theorem h275 : Model (fun x => f275 ((41/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(12539409876853/1562500000000),(2544302976611/100000000000000),(1369500801/6250000000000),(-156460991/100000000000000)⟩
def e276 : ℝ := (29028949/20000000000000)
theorem h276 : Model (fun x => f276 ((41/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(64269179363841/4000000000000),(6791930815761/100000000000000),(62082214923/100000000000000),(-358380297/100000000000000)⟩
def e277 : ℝ := (194056287/50000000000000)
theorem h277 : Model (fun x => f277 ((41/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1613483722801713/100000000000000),(13633819036847/100000000000000),(149814563041/100000000000000),(-270251957/100000000000000)⟩
def e278 : ℝ := (78286261/10000000000000)
theorem h278 : Model (fun x => f278 ((41/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(100209965505179/12500000000000),(211580768231/12500000000000),(399643939/3125000000000),(-823429/625000000000)⟩
def e279 : ℝ := (12023889/12500000000000)
theorem h279 : Model (fun x => f279 ((41/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(902100095906923/100000000000000),(2116696175567/100000000000000),(1644013469/10000000000000),(-157990399/100000000000000)⟩
def e280 : ℝ := (60192659/50000000000000)
theorem h280 : Model (fun x => f280 ((41/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1002100095906923/100000000000000),(2116696175567/100000000000000),(1644013469/10000000000000),(-157990399/100000000000000)⟩
def e281 : ℝ := (60192659/50000000000000)
theorem h281 : Model (fun x => f281 ((41/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(16168721933638557/100000000000000),(4269426547449/2500000000000),(1027568651641/50000000000000),(155192847/100000000000000)⟩
def e282 : ℝ := (9823672353/100000000000000)
theorem h282 : Model (fun x => f282 ((41/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(123695614793/20000000000000),(-6532480969/100000000000000),(-9614827/100000000000000),(925933/100000000000000)⟩
def e283 : ℝ := (392557/100000000000000)
theorem h283 : Model (fun x => f283 ((41/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (3199175951114423/20000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(104872692837/50000000000000),(52784363103/25000000000000),(1372331211/100000000000000),(-4872113/25000000000000)⟩
def e284 : ℝ := (6399767/50000000000000)
theorem h284 : Model (fun x => f284 ((41/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(50209965505179/25000000000000),(423161536463/50000000000000),(399643939/6250000000000),(-32937159/50000000000000)⟩
def e285 : ℝ := (751493/1562500000000)
theorem h285 : Model (fun x => f285 ((41/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(79832379541/160000000000),(-13168441591/12500000000000),(-286756933/50000000000000),(5545627/50000000000000)⟩
def e286 : ℝ := (1208841/20000000000000)
theorem h286 : Model (fun x => f286 ((41/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (24999189417181/12500000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(100209525573749/100000000000000),(52673766363/25000000000000),(71689233/6250000000000),(-22182509/100000000000000)⟩
def e287 : ℝ := (36366747/100000000000000)
theorem h287 : Model (fun x => f287 ((41/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(209525573749/100000000000000),(52673766363/25000000000000),(71689233/6250000000000),(-22182509/100000000000000)⟩
def e288 : ℝ := (36366747/100000000000000)
theorem h288 : Model (fun x => f288 ((41/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(73964173637767/20000000000000),(777565122501/100000000000000),(105826963/2500000000000),(-40932011/50000000000000)⟩
def e289 : ℝ := (16776327/12500000000000)
theorem h289 : Model (fun x => f289 ((41/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(34069189423789/1250000000000),(777565122501/100000000000000),(105826963/2500000000000),(-40932011/50000000000000)⟩
def e290 : ℝ := (134210617/100000000000000)
theorem h290 : Model (fun x => f290 ((41/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1365622923536033/50000000000000),(3260881198359/50000000000000),(37142883197/100000000000000),(-334394927/50000000000000)⟩
def e291 : ℝ := (70409209/6250000000000)
theorem h291 : Model (fun x => f291 ((41/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4006813399726509/50000000000000),(3260881198359/50000000000000),(37142883197/100000000000000),(-334394927/50000000000000)⟩
def e292 : ℝ := (225309469/20000000000000)
theorem h292 : Model (fun x => f292 ((41/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(321216695879307/4000000000000),(2927467923373/12500000000000),(71440129997/50000000000000),(-2294749981/100000000000000)⟩
def e293 : ℝ := (2025210809/50000000000000)
theorem h293 : Model (fun x => f293 ((41/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(6649732508015147/50000000000000),(2927467923373/12500000000000),(71440129997/50000000000000),(-2294749981/100000000000000)⟩
def e294 : ℝ := (4050421619/100000000000000)
theorem h294 : Model (fun x => f294 ((41/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(13327330796410679/100000000000000),(1609066570593/3125000000000),(69014485149/20000000000000),(-2340020243/50000000000000)⟩
def e295 : ℝ := (892109341/10000000000000)
theorem h295 : Model (fun x => f295 ((41/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3915761270531241/25000000000000),(1609066570593/3125000000000),(69014485149/20000000000000),(-2340020243/50000000000000)⟩
def e296 : ℝ := (8921093411/100000000000000)
theorem h296 : Model (fun x => f296 ((41/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(313917263343997/2000000000000),(10574909792173/12500000000000),(158485518629/25000000000000),(-6846646109/100000000000000)⟩
def e297 : ℝ := (14691137303/100000000000000)
theorem h297 : Model (fun x => f297 ((41/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(8049122059790401/50000000000000),(10574909792173/12500000000000),(158485518629/25000000000000),(-6846646109/100000000000000)⟩
def e298 : ℝ := (1836392163/12500000000000)
theorem h298 : Model (fun x => f298 ((41/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(4032993514483967/25000000000000),(118694741445081/100000000000000),(499084086961/50000000000000),(-4062962093/50000000000000)⟩
def e299 : ℝ := (20664597333/100000000000000)
theorem h299 : Model (fun x => f299 ((41/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(805717750515841/5000000000000),(118694741445081/100000000000000),(499084086961/50000000000000),(-4062962093/50000000000000)⟩
def e300 : ℝ := (10332298667/50000000000000)
theorem h300 : Model (fun x => f300 ((41/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(16148118705108137/100000000000000),(76447794059629/50000000000000),(1435179674847/100000000000000),(-8252965643/100000000000000)⟩
def e301 : ℝ := (6671949753/25000000000000)
theorem h301 : Model (fun x => f301 ((41/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(1615145203844147/10000000000000),(76447794059629/50000000000000),(1435179674847/100000000000000),(-8252965643/100000000000000)⟩
def e302 : ℝ := (26687799013/100000000000000)
theorem h302 : Model (fun x => f302 ((41/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(33841422552339/100000000000000),(17175333901043/50000000000000),(31900760079/6250000000000),(117751817/10000000000000)⟩
def e303 : ℝ := (3038806389/50000000000000)
theorem h303 : Model (fun x => f303 ((41/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(50209745078579/50000000000000),(422273050993/100000000000000),(1371393097/50000000000000),(-39624513/100000000000000)⟩
def e304 : ℝ := (36560417/50000000000000)
theorem h304 : Model (fun x => f304 ((41/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(200209525573749/100000000000000),(52673766363/25000000000000),(71689233/6250000000000),(-22182509/100000000000000)⟩
def e305 : ℝ := (36366747/100000000000000)
theorem h305 : Model (fun x => f305 ((41/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(25052408831541/6250000000000),(843663181897/100000000000000),(100736833/2000000000000),(-83989531/100000000000000)⟩
def e306 : ℝ := (18231791/12500000000000)
theorem h306 : Model (fun x => f306 ((41/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(802516941862787/100000000000000),(20269128647/800000000000),(16459522677/100000000000000),(-11839083/5000000000000)⟩
def e307 : ℝ := (438712373/100000000000000)
theorem h307 : Model (fun x => f307 ((41/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(401678840488111/25000000000000),(3381727191841/50000000000000),(23748440421/50000000000000),(-18385527/3125000000000)⟩
def e308 : ℝ := (234585783/20000000000000)
theorem h308 : Model (fun x => f308 ((41/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(80672768737469/5000000000000),(2715310477759/20000000000000),(24065027577/20000000000000),(-210346099/25000000000000)⟩
def e309 : ℝ := (2366556847/100000000000000)
theorem h309 : Model (fun x => f309 ((41/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(100209525573749/12500000000000),(52673766363/3125000000000),(71689233/781250000000),(-22182509/12500000000000)⟩
def e310 : ℝ := (36366747/12500000000000)
theorem h310 : Model (fun x => f310 ((41/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(18041913894943/2000000000000),(2107833574609/100000000000000),(5959504009/50000000000000),(-43416917/20000000000000)⟩
def e311 : ℝ := (36405481/10000000000000)
theorem h311 : Model (fun x => f311 ((41/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(20041913894943/2000000000000),(2107833574609/100000000000000),(5959504009/50000000000000),(-43416917/20000000000000)⟩
def e312 : ℝ := (36405481/10000000000000)
theorem h312 : Model (fun x => f312 ((41/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(1010522927939377/6250000000000),(85029500541753/50000000000000),(421063007863/25000000000000),(-7779595691/100000000000000)⟩
def e313 : ℝ := (7430575407/25000000000000)
theorem h313 : Model (fun x => f313 ((41/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(618491656863/100000000000000),(-813162473/12500000000000),(998693/25000000000000),(933231/100000000000000)⟩
def e314 : ℝ := (234977/20000000000000)
theorem h314 : Model (fun x => f314 ((41/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (3199317218403551/20000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(209306375049/100000000000000),(52563632111/25000000000000),(461797301/50000000000000),(-24232941/100000000000000)⟩
def e315 : ℝ := (39061639/100000000000000)
theorem h315 : Model (fun x => f315 ((41/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(419051760723/100000000000000),(52673997607/12500000000000),(2295925813/100000000000000),(-43721393/100000000000000)⟩
def e316 : ℝ := (51861173/100000000000000)
theorem h316 : Model (fun x => f316 ((41/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(1055525830573/50000000000000),(2117480486311/100000000000000),(386640627/6250000000000),(-29932371/12500000000000)⟩
def e317 : ℝ := (262335883/100000000000000)
theorem h317 : Model (fun x => f317 ((41/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(2059562596239/100000000000000),(125975086671/6250000000000),(-10781410887/25000000000000),(818226459/100000000000000)⟩
def e318 : ℝ := (8898441/3125000000000)
theorem h318 : Model (fun x => f318 ((41/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-3064960011907/50000000000000),(-5935411984297/100000000000000),(189255997003/100000000000000),(-5119433747/100000000000000)⟩
def e319 : ℝ := (248117969/50000000000000)
theorem h319 : Model (fun x => f319 ((41/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((41/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-18491/1600),(-451/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((41/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((41/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(3977/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((41/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(140589/1600),(1489/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((41/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((41/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(313389/1600),(1489/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((41/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1566945/32),(7445/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((41/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((41/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(203116856646273587/25000000000000),(3614219646389011/50000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (105831/100000000000000)
theorem h329 : Model (fun x => f329 ((41/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(12308185747/100000000000000),(-54752333/50000000000000),(1667319/100000000000000),(-21001/100000000000000)⟩
def e330 : ℝ := (287/100000000000000)
theorem h330 : Model (fun x => f330 ((41/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (402596618838216709/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(602695316104153/100000000000000),(182517139179/50000000000000),(381403097/4000000000000),(-64321107/100000000000000)⟩
def e331 : ℝ := (13430703/50000000000000)
theorem h331 : Model (fun x => f331 ((41/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((41/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(401/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((41/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((41/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((41/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(455806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((41/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((41/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((41/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2022182458365389/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (201/20000000000000)
theorem h339 : Model (fun x => f339 ((41/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3554193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((41/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((41/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((41/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(125176096352147/6250000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (251/25000000000000)
theorem h343 : Model (fun x => f343 ((41/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(499296605513/10000000000000),(-3512024797/50000000000000),(1976271/20000000000000),(-13901/100000000000000)⟩
def e344 : ℝ := (3/12500000000000)
theorem h344 : Model (fun x => f344 ((41/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1999999999998867/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(100966883718977/100000000000000),(482761758813/50000000000000),(-27165757/2000000000000),(1910823/100000000000000)⟩
def e345 : ℝ := (907/25000000000000)
theorem h345 : Model (fun x => f345 ((41/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(200966883718977/100000000000000),(482761758813/50000000000000),(-27165757/2000000000000),(1910823/100000000000000)⟩
def e346 : ℝ := (907/25000000000000)
theorem h346 : Model (fun x => f346 ((41/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(3140107558109/3125000000000),(482761758813/100000000000000),(-27165757/4000000000000),(955411/100000000000000)⟩
def e347 : ℝ := (363/20000000000000)
theorem h347 : Model (fun x => f347 ((41/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(15107558109/3125000000000),(482761758813/100000000000000),(-27165757/4000000000000),(955411/100000000000000)⟩
def e348 : ℝ := (363/20000000000000)
theorem h348 : Model (fun x => f348 ((41/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(370831749719539/100000000000000),(1781620776571/100000000000000),(-1253182243/50000000000000),(3525921/100000000000000)⟩
def e349 : ℝ := (6701/100000000000000)
theorem h349 : Model (fun x => f349 ((41/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(85204563607307/3125000000000),(1781620776571/100000000000000),(-1253182243/50000000000000),(3525921/100000000000000)⟩
def e350 : ℝ := (3351/50000000000000)
theorem h350 : Model (fun x => f350 ((41/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(2739727300287321/100000000000000),(934559717043/6250000000000),(-12434669267/100000000000000),(1348287/25000000000000)⟩
def e351 : ℝ := (53701/50000000000000)
theorem h351 : Model (fun x => f351 ((41/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8022108252668273/100000000000000),(934559717043/6250000000000),(-12434669267/100000000000000),(1348287/25000000000000)⟩
def e352 : ℝ := (107403/100000000000000)
theorem h352 : Model (fun x => f352 ((41/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(1007611310246889/12500000000000),(53752915213137/100000000000000),(1302676579/25000000000000),(-621239/781250000000)⟩
def e353 : ℝ := (25391/5000000000000)
theorem h353 : Model (fun x => f353 ((41/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(13329938101022731/100000000000000),(53752915213137/100000000000000),(1302676579/25000000000000),(-621239/781250000000)⟩
def e354 : ℝ := (507821/100000000000000)
theorem h354 : Model (fun x => f354 ((41/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(6697190300823457/50000000000000),(118364622931153/100000000000000),(21775618891/12500000000000),(-73112921/25000000000000)⟩
def e355 : ℝ := (425263/50000000000000)
theorem h355 : Model (fun x => f355 ((41/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(15730094887361199/100000000000000),(118364622931153/100000000000000),(21775618891/12500000000000),(-73112921/25000000000000)⟩
def e356 : ℝ := (850527/100000000000000)
theorem h356 : Model (fun x => f356 ((41/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(3951535187645971/25000000000000),(97437864903203/50000000000000),(639636282433/100000000000000),(-106449721/100000000000000)⟩
def e357 : ℝ := (2614137/100000000000000)
theorem h357 : Model (fun x => f357 ((41/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(4052130425741209/25000000000000),(97437864903203/50000000000000),(639636282433/100000000000000),(-106449721/100000000000000)⟩
def e358 : ℝ := (1307069/50000000000000)
theorem h358 : Model (fun x => f358 ((41/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(3257376096336233/20000000000000),(68516596277273/25000000000000),(294686972441/20000000000000),(906163171/50000000000000)⟩
def e359 : ℝ := (594007/10000000000000)
theorem h359 : Model (fun x => f359 ((41/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(16269261434062117/100000000000000),(68516596277273/25000000000000),(294686972441/20000000000000),(906163171/50000000000000)⟩
def e360 : ℝ := (5940071/100000000000000)
theorem h360 : Model (fun x => f360 ((41/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(1634791385406391/10000000000000),(176966554691229/50000000000000),(2693154063497/100000000000000),(144568021/2000000000000)⟩
def e361 : ℝ := (7660517/100000000000000)
theorem h361 : Model (fun x => f361 ((41/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(16351247187397243/100000000000000),(176966554691229/50000000000000),(2693154063497/100000000000000),(144568021/2000000000000)⟩
def e362 : ℝ := (3830259/50000000000000)
theorem h362 : Model (fun x => f362 ((41/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(9881096681529/12500000000000),(40324314657541/50000000000000),(201328129503/12500000000000),(2697242361/25000000000000)⟩
def e363 : ℝ := (5096957/25000000000000)
theorem h363 : Model (fun x => f363 ((41/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(100969220879291/100000000000000),(970191262473/100000000000000),(38629391/4000000000000),(-927447/20000000000000)⟩
def e364 : ℝ := (17517/100000000000000)
theorem h364 : Model (fun x => f364 ((41/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(6265107558109/3125000000000),(482761758813/100000000000000),(-27165757/4000000000000),(955411/100000000000000)⟩
def e365 : ℝ := (363/20000000000000)
theorem h365 : Model (fun x => f365 ((41/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(401936104598267/100000000000000),(1935714780099/100000000000000),(-15702123/4000000000000),(-2726413/100000000000000)⟩
def e366 : ℝ := (21147/100000000000000)
theorem h366 : Model (fun x => f366 ((41/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(805815336574557/100000000000000),(1455295355897/25000000000000),(1165632433/20000000000000),(-16667251/100000000000000)⟩
def e367 : ℝ := (14461/25000000000000)
theorem h367 : Model (fun x => f367 ((41/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1615526321796289/100000000000000),(7780336583263/50000000000000),(4289286503/12500000000000),(-9278573/25000000000000)⟩
def e368 : ℝ := (195579/100000000000000)
theorem h368 : Model (fun x => f368 ((41/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(81559217010879/5000000000000),(31385185676833/100000000000000),(201216864239/100000000000000),(370799331/100000000000000)⟩
def e369 : ℝ := (1237331/100000000000000)
theorem h369 : Model (fun x => f369 ((41/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(3140107558109/390625000000),(482761758813/12500000000000),(-27165757/500000000000),(955411/12500000000000)⟩
def e370 : ℝ := (363/2500000000000)
theorem h370 : Model (fun x => f370 ((41/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(180967351151039/20000000000000),(4832285332977/100000000000000),(-35739333/800000000000),(3006053/100000000000000)⟩
def e371 : ℝ := (32037/100000000000000)
theorem h371 : Model (fun x => f371 ((41/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(200967351151039/20000000000000),(4832285332977/100000000000000),(-35739333/800000000000),(3006053/100000000000000)⟩
def e372 : ℝ := (32037/100000000000000)
theorem h372 : Model (fun x => f372 ((41/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(16390739804629113/100000000000000),(49274170396123/12500000000000),(3465650934441/100000000000000),(12096228249/100000000000000)⟩
def e373 : ℝ := (715893/3125000000000)
theorem h373 : Model (fun x => f373 ((41/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(610100588453/100000000000000),(-7336386451/50000000000000),(111938633/50000000000000),(-2732039/100000000000000)⟩
def e374 : ℝ := (15623/50000000000000)
theorem h374 : Model (fun x => f374 ((41/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (15993068671388863/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(120569257999/25000000000000),(24021955751/5000000000000),(-1829985173/100000000000000),(1578903/20000000000000)⟩
def e375 : ℝ := (75709/20000000000000)
theorem h375 : Model (fun x => f375 ((41/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(100966883718977/50000000000000),(482761758813/25000000000000),(-27165757/1000000000000),(1910823/50000000000000)⟩
def e376 : ℝ := (907/12500000000000)
theorem h376 : Model (fun x => f376 ((41/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(49759442028187/100000000000000),(-5976595573/2500000000000),(371217117/25000000000000),(-4611393/50000000000000)⟩
def e377 : ℝ := (57879/100000000000000)
theorem h377 : Model (fun x => f377 ((41/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (3999999999981/2000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(50240557971811/50000000000000),(478127645839/100000000000000),(-2969736937/100000000000000),(72053/390625000000)⟩
def e378 : ℝ := (69901/20000000000000)
theorem h378 : Model (fun x => f378 ((41/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(240557971811/50000000000000),(478127645839/100000000000000),(-2969736937/100000000000000),(72053/390625000000)⟩
def e379 : ℝ := (69901/20000000000000)
theorem h379 : Model (fun x => f379 ((41/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(185411582991207/50000000000000),(1764518692977/100000000000000),(-5479871729/50000000000000),(68072929/100000000000000)⟩
def e380 : ℝ := (644921/50000000000000)
theorem h380 : Model (fun x => f380 ((41/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2726537451696699/100000000000000),(1764518692977/100000000000000),(-5479871729/50000000000000),(68072929/100000000000000)⟩
def e381 : ℝ := (1289843/100000000000000)
theorem h381 : Model (fun x => f381 ((41/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(684913814521409/25000000000000),(14809337404453/100000000000000),(-83546810649/100000000000000),(466522631/100000000000000)⟩
def e382 : ℝ := (1181833/10000000000000)
theorem h382 : Model (fun x => f382 ((41/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2005509052616647/25000000000000),(14809337404453/100000000000000),(-83546810649/100000000000000),(466522631/100000000000000)⟩
def e383 : ℝ := (11818331/100000000000000)
theorem h383 : Model (fun x => f383 ((41/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(125947367276223/1562500000000),(26618080184653/50000000000000),(-251374603821/100000000000000),(1109218527/100000000000000)⟩
def e384 : ℝ := (11873559/25000000000000)
theorem h384 : Model (fun x => f384 ((41/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(13329679124725891/100000000000000),(26618080184653/50000000000000),(-251374603821/100000000000000),(1109218527/100000000000000)⟩
def e385 : ℝ := (47494237/100000000000000)
theorem h385 : Model (fun x => f385 ((41/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(66969051681143/500000000000),(117225169021559/100000000000000),(-2461897571/625000000000),(790424787/100000000000000)⟩
def e386 : ℝ := (23478791/20000000000000)
theorem h386 : Model (fun x => f386 ((41/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3145904924388577/20000000000000),(117225169021559/100000000000000),(-2461897571/625000000000),(790424787/100000000000000)⟩
def e387 : ℝ := (29348489/25000000000000)
theorem h387 : Model (fun x => f387 ((41/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(3161040374551/20000000000),(9649818188811/5000000000000),(-2362799267/781250000000),(-1669013401/100000000000000)⟩
def e388 : ℝ := (211106389/100000000000000)
theorem h388 : Model (fun x => f388 ((41/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(1012973926570997/6250000000000),(9649818188811/5000000000000),(-2362799267/781250000000),(-1669013401/100000000000000)⟩
def e389 : ℝ := (21110639/10000000000000)
theorem h389 : Model (fun x => f389 ((41/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(8142780045091711/50000000000000),(135708917131093/50000000000000),(68776505919/50000000000000),(-1172997607/20000000000000)⟩
def e390 : ℝ := (61413409/20000000000000)
theorem h390 : Model (fun x => f390 ((41/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(8133970521282187/50000000000000),(135708917131093/50000000000000),(68776505919/50000000000000),(-1172997607/20000000000000)⟩
def e391 : ℝ := (153533523/50000000000000)
theorem h391 : Model (fun x => f391 ((41/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(8173104350309589/50000000000000),(43813149033743/12500000000000),(952823448623/100000000000000),(-10295208001/100000000000000)⟩
def e392 : ℝ := (385966231/100000000000000)
theorem h392 : Model (fun x => f392 ((41/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(16349542033952511/100000000000000),(43813149033743/12500000000000),(952823448623/100000000000000),(-10295208001/100000000000000)⟩
def e393 : ℝ := (48245779/12500000000000)
theorem h393 : Model (fun x => f393 ((41/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(39330126717263/50000000000000),(19964504198907/25000000000000),(1194908021057/100000000000000),(-2887135831/100000000000000)⟩
def e394 : ℝ := (2357377/3125000000000)
theorem h394 : Model (fun x => f394 ((41/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(25241136653189/25000000000000),(960855988347/100000000000000),(-3681989173/100000000000000),(4335179/50000000000000)⟩
def e395 : ℝ := (485709/50000000000000)
theorem h395 : Model (fun x => f395 ((41/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(100240557971811/50000000000000),(478127645839/100000000000000),(-2969736937/100000000000000),(72053/390625000000)⟩
def e396 : ℝ := (69901/20000000000000)
theorem h396 : Model (fun x => f396 ((41/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(803853557/200000000),(76684451201/4000000000000),(-9621463047/100000000000000),(22780747/50000000000000)⟩
def e397 : ℝ := (417607/25000000000000)
theorem h397 : Model (fun x => f397 ((41/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(805787290813049/100000000000000),(5765169132113/100000000000000),(-22059145457/100000000000000),(7817979/12500000000000)⟩
def e398 : ℝ := (5628753/100000000000000)
theorem h398 : Model (fun x => f398 ((41/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1615451352753879/100000000000000),(15410767216131/100000000000000),(-40589316339/100000000000000),(-332577/12500000000000)⟩
def e399 : ℝ := (8085829/50000000000000)
theorem h399 : Model (fun x => f399 ((41/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1631033134057587/100000000000000),(15540786155541/50000000000000),(2975857283/6250000000000),(-820048521/100000000000000)⟩
def e400 : ℝ := (35135029/100000000000000)
theorem h400 : Model (fun x => f400 ((41/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(50240557971811/6250000000000),(478127645839/12500000000000),(-2969736937/12500000000000),(72053/48828125000)⟩
def e401 : ℝ := (69901/2500000000000)
theorem h401 : Model (fun x => f401 ((41/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(226203368540433/25000000000000),(4785877155059/100000000000000),(-27439884669/100000000000000),(78117451/50000000000000)⟩
def e402 : ℝ := (1883729/50000000000000)
theorem h402 : Model (fun x => f402 ((41/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(251203368540433/25000000000000),(4785877155059/100000000000000),(-27439884669/100000000000000),(78117451/50000000000000)⟩
def e403 : ℝ := (1883729/50000000000000)
theorem h403 : Model (fun x => f403 ((41/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(16388840699053019/100000000000000),(195185534358689/50000000000000),(1518401296993/100000000000000),(-11941728629/100000000000000)⟩
def e404 : ℝ := (421406113/100000000000000)
theorem h404 : Model (fun x => f404 ((41/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(610171285671/100000000000000),(-14533866139/100000000000000),(144827693/50000000000000),(-5108253/100000000000000)⟩
def e405 : ℝ := (25871/25000000000000)
theorem h405 : Model (fun x => f405 ((41/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (7998469432951953/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(479962279693/100000000000000),(237919155927/50000000000000),(-4087627967/100000000000000),(1440483/4000000000000)⟩
def e406 : ℝ := (904929/100000000000000)
theorem h406 : Model (fun x => f406 ((41/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(962239311689/100000000000000),(478138713437/50000000000000),(-295880657/5000000000000),(4390659/10000000000000)⟩
def e407 : ℝ := (641737/50000000000000)
theorem h407 : Model (fun x => f407 ((41/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(2899685630631/50000000000000),(2883475882029/50000000000000),(-32082686553/100000000000000),(66716903/20000000000000)⟩
def e408 : ℝ := (371371/4000000000000)
theorem h408 : Model (fun x => f408 ((41/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(5657923181719/100000000000000),(219531851103/4000000000000),(-82580533411/50000000000000),(435376701/10000000000000)⟩
def e409 : ℝ := (15279137/12500000000000)
theorem h409 : Model (fun x => f409 ((41/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-94399368419/20000000000000),(-223557853361/50000000000000),(24094930181/100000000000000),(-765666737/100000000000000)⟩
def e410 : ℝ := (309234517/50000000000000)
theorem h410 : Model (fun x => f410 ((41/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(111761055175781/50000000000000),(6141641845703/25000000000000),(21853/2048000),(2337/10240000)⟩
def e411 : ℝ := (30029297/12500000000000)
theorem h411 : Model (fun x => f411 ((41/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(25921/1600),(161/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((41/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(4173281/64000),(77763/64000),(483/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((41/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(14575321503282453/100000000000000),(1873514668143399/100000000000000),(20223103610681/20000000000000),(2973581440063/100000000000000)⟩
def e414 : ℝ := (52314865837/100000000000000)
theorem h414 : Model (fun x => f414 ((41/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(68609121231/10000000000000),(-17638059643/20000000000000),(3288138409/50000000000000),(-23342073/6250000000000)⟩
def e415 : ℝ := (1417621/5000000000000)
theorem h415 : Model (fun x => f415 ((41/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (12597665420779749/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(238511132159/50000000000000),(456988680297/100000000000000),(-19420342701/100000000000000),(597484979/100000000000000)⟩
def e416 : ℝ := (12801963/10000000000000)
theorem h416 : Model (fun x => f416 ((41/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(5025422223/100000000000000),(394918943/4000000000000),(116864687/2500000000000),(-84090879/50000000000000)⟩
def e417 : ℝ := (93311083/12500000000000)
theorem h417 : Model (fun x => f417 ((41/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((41/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((17511388157/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ∧
    SigmaActualBlockSeparable.endpointCellMass 1 (21/20) ≤ (21990320141/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(41/40)-(1/40)) (by norm_num : ((41/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel0
