import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel4
open Hf4Quad.Dag

def p0 : Cubic := ⟨(49/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((49/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((49/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((49/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((49/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(107333333333333/50000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((49/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-107333333333333/50000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((49/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-24647619047619/20000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((49/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((49/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(2401/1600),(49/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((49/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(90831481481481/50000000000000),(3707407407407/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (3/100000000000000)
theorem h9 : Model (fun x => f9 ((49/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-90831481481481/50000000000000),(-3707407407407/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (3/100000000000000)
theorem h10 : Model (fun x => f10 ((49/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-304901058201057/100000000000000),(-5897883597883/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (3/50000000000000)
theorem h11 : Model (fun x => f11 ((49/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((49/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(117649/64000),(7203/64000),(147/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((49/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1790947306134259/100000000000000),(27412458767361/25000000000000),(2237751736111/100000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((49/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1790947306134259/100000000000000),(-27412458767361/25000000000000),(-2237751736111/100000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((49/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-523962091083829/25000000000000),(-12144560226521/10000000000000),(-578353277943/25000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/12500000000000)
theorem h16 : Model (fun x => f16 ((49/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((49/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(5764801/2560000),(117649/640000),(7203/1280000),(49/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((49/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(314547673611111/50000000000000),(25677361111111/50000000000000),(1572083333333/100000000000000),(2673611111/12500000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((49/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-733376508556547/50000000000000),(-17522720010747/25000000000000),(-741329778439/100000000000000),(6166087963/100000000000000)⟩
def e20 : ℝ := (54563497/50000000000000)
theorem h20 : Model (fun x => f20 ((49/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((49/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(137927367675781/50000000000000),(7037110595703/25000000000000),(117649/10240000),(2401/10240000)⟩
def e22 : ℝ := (30029297/12500000000000)
theorem h22 : Model (fun x => f22 ((49/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(224642814575647/12500000000000),(5730684045297/3125000000000),(7484975079571/100000000000000),(7637729673/5000000000000)⟩
def e23 : ℝ := (62603299/4000000000000)
theorem h23 : Model (fun x => f23 ((49/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(165194749746041/50000000000000),(28322752351629/25000000000000),(1685911325283/25000000000000),(158920681423/100000000000000)⟩
def e24 : ℝ := (1674209469/100000000000000)
theorem h24 : Model (fun x => f24 ((49/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((49/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(337922050805663/100000000000000),(41378210302733/100000000000000),(211113317871/10000000000000),(57445800781/100000000000000)⟩
def e26 : ℝ := (886474613/100000000000000)
theorem h26 : Model (fun x => f26 ((49/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(151760971811559/20000000000000),(92914880700951/100000000000000),(4740555137801/100000000000000),(64497348813/50000000000000)⟩
def e27 : ℝ := (497645273/25000000000000)
theorem h27 : Model (fun x => f27 ((49/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(1089194358549877/100000000000000),(206205890107467/100000000000000),(11484200438933/100000000000000),(287915379049/100000000000000)⟩
def e28 : ℝ := (3664790561/100000000000000)
theorem h28 : Model (fun x => f28 ((49/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((49/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(413954512236937/100000000000000),(59136358890989/100000000000000),(226287087593/6250000000000),(3848419857/3125000000000)⟩
def e30 : ℝ := (2544238287/100000000000000)
theorem h30 : Model (fun x => f30 ((49/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(98232062824479/100000000000000),(3508287958017/25000000000000),(429586280573/50000000000000),(29223556501/100000000000000)⟩
def e31 : ℝ := (301875893/50000000000000)
theorem h31 : Model (fun x => f31 ((49/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(296856605343589/25000000000000),(44047808387907/20000000000000),(12343373000079/100000000000000),(6342778711/2000000000000)⟩
def e32 : ℝ := (4268542347/100000000000000)
theorem h32 : Model (fun x => f32 ((49/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((49/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1030029/320),(21021/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((49/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((49/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(108241/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((49/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(552377/64),(38693/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((49/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((49/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(698297/64),(38693/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((49/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-698297/64),(-38693/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((49/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((49/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(89/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((49/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(7921/1600),(89/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((49/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((49/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(166341/160),(1869/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((49/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(12023493907/12500000000000),(-432305399/20000000000000),(3643023/10000000000000),(-136443/25000000000000)⟩
def e46 : ℝ := (1979/25000000000000)
theorem h46 : Model (fun x => f46 ((49/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (81291/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-131187026949631/12500000000000),(80733034563/25000000000000),(-3713452017/100000000000000),(42687667/100000000000000)⟩
def e47 : ℝ := (43043171/25000000000000)
theorem h47 : Model (fun x => f47 ((49/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((49/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(129/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((49/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((49/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((49/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(53749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((49/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(103749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((49/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((49/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(103749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((49/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((49/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2178749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((49/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((49/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(3749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((49/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(81703124999977/100000000000000),(587890624999/6250000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (7/10000000000000)
theorem h60 : Model (fun x => f60 ((49/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(107640624999997/100000000000000),(864583333331/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (9/100000000000000)
theorem h61 : Model (fun x => f61 ((49/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((49/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(103749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((49/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1145140624999987/100000000000000),(5031249999991/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (39/100000000000000)
theorem h64 : Model (fun x => f64 ((49/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1245140624999987/100000000000000),(5031249999991/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (39/100000000000000)
theorem h65 : Model (fun x => f65 ((49/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(508659400634617/50000000000000),(15153966064427/12500000000000),(928627929681/100000000000000),(1997612847/100000000000000)⟩
def e66 : ℝ := (633869/100000000000000)
theorem h66 : Model (fun x => f66 ((49/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(203749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((49/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(83028124999999/20000000000000),(1697916666663/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (3/20000000000000)
theorem h68 : Model (fun x => f68 ((49/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(169169804687497/20000000000000),(5189257812489/100000000000000),(5305989583/50000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (23/50000000000000)
theorem h69 : Model (fun x => f69 ((49/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(537811321611359/6250000000000),(269557171779203/25000000000000),(7126887438509/50000000000000),(78024362687/100000000000000)⟩
def e70 : ℝ := (216651107/100000000000000)
theorem h70 : Model (fun x => f70 ((49/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((49/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2260453124999937/12500000000000),(18156249999951/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (189/12500000000000)
theorem h72 : Model (fun x => f72 ((49/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(3390679687499/500000000000),(80795312499861/100000000000000),(61614583333/10000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (153/25000000000000)
theorem h73 : Model (fun x => f73 ((49/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(5736006204920691/100000000000000),(359298291939671/50000000000000),(9476304224601/100000000000000),(50875847701/100000000000000)⟩
def e74 : ℝ := (33618229/25000000000000)
theorem h74 : Model (fun x => f74 ((49/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(2868197470140487/20000000000000),(898412635498077/50000000000000),(23730079101619/100000000000000),(32225052597/25000000000000)⟩
def e75 : ℝ := (351124023/100000000000000)
theorem h75 : Model (fun x => f75 ((49/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((49/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(753484374999979/12500000000000),(6052083333317/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (63/12500000000000)
theorem h77 : Model (fun x => f77 ((49/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(140624999999/100000000000000),(31249999999/100000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((49/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(5273437499/100000000000000),(1757812499/100000000000000),(195312499/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((49/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(158938110321/50000000000000),(108511962829/100000000000000),(1262939447/10000000000000),(266158483/50000000000000)⟩
def e80 : ℝ := (3699529/100000000000000)
theorem h80 : Model (fun x => f80 ((49/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(323836399779/50000000000000),(55604402129/25000000000000),(26184524411/100000000000000),(227443659/20000000000000)⟩
def e81 : ℝ := (4885597/50000000000000)
theorem h81 : Model (fun x => f81 ((49/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(14341635023501993/100000000000000),(179704768860467/10000000000000),(2375626362603/10000000000000),(130037428683/100000000000000)⟩
def e82 : ℝ := (360895217/100000000000000)
theorem h82 : Model (fun x => f82 ((49/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(98876953/50000000000000),(1373291/1562500000000),(14648437/100000000000000),(1085069/100000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((49/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(7415771/100000000000000),(4119873/100000000000000),(915527/100000000000000),(4069/4000000000000)⟩
def e84 : ℝ := (5779/100000000000000)
theorem h84 : Model (fun x => f84 ((49/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(278091/100000000000000),(92697/50000000000000),(25749/50000000000000),(7629/100000000000000)⟩
def e85 : ℝ := (667/100000000000000)
theorem h85 : Model (fun x => f85 ((49/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(2607/25000000000000),(811/10000000000000),(2703/100000000000000),(1/200000000000)⟩
def e86 : ℝ := (63/100000000000000)
theorem h86 : Model (fun x => f86 ((49/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(7821/25000000000000),(2433/10000000000000),(8109/100000000000000),(3/200000000000)⟩
def e87 : ℝ := (189/100000000000000)
theorem h87 : Model (fun x => f87 ((49/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-7821/25000000000000),(-2433/10000000000000),(-8109/100000000000000),(-3/200000000000)⟩
def e88 : ℝ := (189/100000000000000)
theorem h88 : Model (fun x => f88 ((49/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(14341635023470709/100000000000000),(89852384429017/5000000000000),(23756263617921/100000000000000),(130037427183/100000000000000)⟩
def e89 : ℝ := (180447703/50000000000000)
theorem h89 : Model (fun x => f89 ((49/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2260453124999937/10000000000000),(18156249999951/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (189/10000000000000)
theorem h90 : Model (fun x => f90 ((49/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1723417385253867/100000000000000),(1409748372393/10000000000000),(21621907551/50000000000000),(58955439/100000000000000)⟩
def e91 : ℝ := (15131/50000000000000)
theorem h91 : Model (fun x => f91 ((49/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(973926053544081/250000000000),(6315749803932439/100000000000000),(41654098134617/100000000000000),(286476457/200000000000)⟩
def e92 : ℝ := (271844133/100000000000000)
theorem h92 : Model (fun x => f92 ((49/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(1604331247/6250000000000),(-20807647/5000000000000),(800413/20000000000000),(-233/781250000000)⟩
def e93 : ℝ := (117/50000000000000)
theorem h93 : Model (fun x => f93 ((49/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (383212874005492711/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(736279462439/20000000000000),(401606425667/100000000000000),(-806438669/100000000000000),(86363/4000000000000)⟩
def e94 : ℝ := (32533/12500000000000)
theorem h94 : Model (fun x => f94 ((49/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(53749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((49/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(48192771084337/100000000000000),(-193545265399/100000000000000),(388645111/50000000000000),(-195103/6250000000000)⟩
def e96 : ℝ := (12591/100000000000000)
theorem h96 : Model (fun x => f96 ((49/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (10333333333333/5000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(51807228915661/50000000000000),(387090530797/100000000000000),(-1554580447/100000000000000),(6243293/100000000000000)⟩
def e97 : ℝ := (19829/25000000000000)
theorem h97 : Model (fun x => f97 ((49/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(1087951807228881/50000000000000),(8128901146737/100000000000000),(-32646189387/100000000000000),(131109153/100000000000000)⟩
def e98 : ℝ := (416409/25000000000000)
theorem h98 : Model (fun x => f98 ((49/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1807228915661/50000000000000),(387090530797/100000000000000),(-1554580447/100000000000000),(6243293/100000000000000)⟩
def e99 : ℝ := (19829/25000000000000)
theorem h99 : Model (fun x => f99 ((49/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(78647118594787/100000000000000),(4358266277467/50000000000000),(-13827923/390625000000),(-112153693/100000000000000)⟩
def e100 : ℝ := (332561/10000000000000)
theorem h100 : Model (fun x => f100 ((49/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(26839889679197/25000000000000),(802163509603/100000000000000),(-861574707/50000000000000),(11283/1250000000000)⟩
def e101 : ℝ := (237681/100000000000000)
theorem h101 : Model (fun x => f101 ((49/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(51807228915661/5000000000000),(387090530797/10000000000000),(-1554580447/10000000000000),(6243293/10000000000000)⟩
def e102 : ℝ := (19829/2500000000000)
theorem h102 : Model (fun x => f102 ((49/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(142938017128751/12500000000000),(4673068817573/100000000000000),(-4317238471/25000000000000),(6333557/10000000000000)⟩
def e103 : ℝ := (1030841/100000000000000)
theorem h103 : Model (fun x => f103 ((49/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(155438017128751/12500000000000),(4673068817573/100000000000000),(-4317238471/25000000000000),(6333557/10000000000000)⟩
def e104 : ℝ := (1030841/100000000000000)
theorem h104 : Model (fun x => f104 ((49/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(977980173381073/100000000000000),(14008209612643/12500000000000),(174864313373/50000000000000),(-3015502419/100000000000000)⟩
def e105 : ℝ := (21659429/50000000000000)
theorem h105 : Model (fun x => f105 ((49/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(101807228915661/50000000000000),(387090530797/100000000000000),(-1554580447/100000000000000),(6243293/100000000000000)⟩
def e106 : ℝ := (19829/25000000000000)
theorem h106 : Model (fun x => f106 ((49/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(51823559297429/12500000000000),(1576344571197/100000000000000),(-1208077577/25000000000000),(6694613/50000000000000)⟩
def e107 : ℝ := (396313/100000000000000)
theorem h107 : Model (fun x => f107 ((49/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(844162074338829/100000000000000),(2407249089147/50000000000000),(-407300529/4000000000000),(9935413/100000000000000)⟩
def e108 : ℝ := (1364459/100000000000000)
theorem h108 : Model (fun x => f108 ((49/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(4127868859118071/50000000000000),(198620156076411/20000000000000),(8248093442501/100000000000000),(-19931985411/100000000000000)⟩
def e109 : ℝ := (276324901/50000000000000)
theorem h109 : Model (fun x => f109 ((49/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(563637683263137/3125000000000),(16845433701663/12500000000000),(-18093068847/6250000000000),(236943/156250000000)⟩
def e110 : ℝ := (4991301/12500000000000)
theorem h110 : Model (fun x => f110 ((49/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(651918284255563/100000000000000),(14937637595697/20000000000000),(115401364717/50000000000000),(-2084044693/100000000000000)⟩
def e111 : ℝ := (3691599/12500000000000)
theorem h111 : Model (fun x => f111 ((49/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(687905863920733/12500000000000),(82734493855589/12500000000000),(1095565778507/20000000000000),(-14021085551/100000000000000)⟩
def e112 : ℝ := (377299501/100000000000000)
theorem h112 : Model (fun x => f112 ((49/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(6879492314801003/50000000000000),(1654976731226767/100000000000000),(3431480583759/25000000000000),(-16976535481/50000000000000)⟩
def e113 : ℝ := (929949303/100000000000000)
theorem h113 : Model (fun x => f113 ((49/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(187879227754379/3125000000000),(5615144567221/12500000000000),(-6031022949/6250000000000),(78981/156250000000)⟩
def e114 : ℝ := (1663767/12500000000000)
theorem h114 : Model (fun x => f114 ((49/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(2041297721/1562500000000),(27982448009/100000000000000),(34650287/2500000000000),(-5791973/50000000000000)⟩
def e115 : ℝ := (79049/100000000000000)
theorem h115 : Model (fun x => f115 ((49/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(4722038101/100000000000000),(60684827/4000000000000),(31276651/20000000000000),(4519569/100000000000000)⟩
def e116 : ℝ := (68201/100000000000000)
theorem h116 : Model (fun x => f116 ((49/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(283895318989/100000000000000),(11666567699/12500000000000),(78741597/781250000000),(34051019/10000000000000)⟩
def e117 : ℝ := (6016283/100000000000000)
theorem h117 : Model (fun x => f117 ((49/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(578051914567/100000000000000),(191137480439/100000000000000),(10439507677/50000000000000),(365454667/50000000000000)⟩
def e118 : ℝ := (21513/160000000000)
theorem h118 : Model (fun x => f118 ((49/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(13759562681516573/100000000000000),(827583934353603/50000000000000),(1374680135039/10000000000000),(-8305540407/25000000000000)⟩
def e119 : ℝ := (58962183/6250000000000)
theorem h119 : Model (fun x => f119 ((49/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(6827043/4000000000000),(73114249/100000000000000),(11451629/100000000000000),(186353/25000000000000)⟩
def e120 : ℝ := (17957/100000000000000)
theorem h120 : Model (fun x => f120 ((49/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(3084507/50000000000000),(1651677/50000000000000),(694279/100000000000000),(137/195312500000)⟩
def e121 : ℝ := (689/20000000000000)
theorem h121 : Model (fun x => f121 ((49/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(871/390625000000),(71639/50000000000000),(7557/20000000000000),(5171/100000000000000)⟩
def e122 : ℝ := (201/50000000000000)
theorem h122 : Model (fun x => f122 ((49/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(8059/100000000000000),(6041/100000000000000),(479/25000000000000),(33/10000000000000)⟩
def e123 : ℝ := (39/100000000000000)
theorem h123 : Model (fun x => f123 ((49/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(24177/100000000000000),(18123/100000000000000),(1437/25000000000000),(99/10000000000000)⟩
def e124 : ℝ := (117/100000000000000)
theorem h124 : Model (fun x => f124 ((49/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-24177/100000000000000),(-18123/100000000000000),(-1437/25000000000000),(-99/10000000000000)⟩
def e125 : ℝ := (117/100000000000000)
theorem h125 : Model (fun x => f125 ((49/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(3439890670373099/25000000000000),(1655167868689083/100000000000000),(6873400672321/50000000000000),(-16611081309/50000000000000)⟩
def e126 : ℝ := (188679009/20000000000000)
theorem h126 : Model (fun x => f126 ((49/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(563637683263137/2500000000000),(16845433701663/10000000000000),(-18093068847/5000000000000),(236943/125000000000)⟩
def e127 : ℝ := (4991301/10000000000000)
theorem h127 : Model (fun x => f127 ((49/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(214854503860331/12500000000000),(13070685817377/100000000000000),(-3804945273/25000000000000),(-41327343/100000000000000)⟩
def e128 : ℝ := (3955051/100000000000000)
theorem h128 : Model (fun x => f128 ((49/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(12110009479448769/3125000000000),(365144141833313/6250000000000),(12366956546709/100000000000000),(-78995474829/100000000000000)⟩
def e129 : ℝ := (14185369/800000000000)
theorem h129 : Model (fun x => f129 ((49/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(1612818721/6250000000000),(-194520511/50000000000000),(5041713/100000000000000),(-29167/50000000000000)⟩
def e130 : ℝ := (31/4000000000000)
theorem h130 : Model (fun x => f130 ((49/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (381665549347834937/100000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(3550668845677/100000000000000),(93396843181/25000000000000),(-1099094281/50000000000000),(13368601/100000000000000)⟩
def e131 : ℝ := (129913/25000000000000)
theorem h131 : Model (fun x => f131 ((49/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(452004134867/6250000000000),(775193798391/100000000000000),(-3004627231/100000000000000),(3881919/25000000000000)⟩
def e132 : ℝ := (194979/25000000000000)
theorem h132 : Model (fun x => f132 ((49/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-37950130318171/50000000000000),(-4056137455887/50000000000000),(8442059921/25000000000000),(-198364529/100000000000000)⟩
def e133 : ℝ := (2809219/12500000000000)
theorem h133 : Model (fun x => f133 ((49/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(10204081632653/12500000000000),(-832986255727/50000000000000),(33999439009/100000000000000),(-693866103/100000000000000)⟩
def e134 : ℝ := (7227773/50000000000000)
theorem h134 : Model (fun x => f134 ((49/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (6/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-6195939643783/10000000000000),(-2678893877889/50000000000000),(136908517207/100000000000000),(-2955981599/100000000000000)⟩
def e135 : ℝ := (102254671/100000000000000)
theorem h135 : Model (fun x => f135 ((49/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(5764801/256000),(117649/64000),(7203/128000),(49/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((49/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((49/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(1058841/32000),(64827/32000),(1323/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((49/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(14235529/256000),(247303/64000),(2499/25600),(67/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((49/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-2401/1600),(-49/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((49/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(13851369/256000),(243383/64000),(2483/25600),(67/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((49/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((49/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(147/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((49/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-147/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((49/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(11969769/256000),(233783/64000),(2483/25600),(67/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((49/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(12737769/256000),(233783/64000),(2483/25600),(67/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((49/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((49/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(12737769/4000),(233783/1000),(2483/400),(67/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((49/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((49/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(1089547389/512000),(22235661/128000),(1361367/256000),(9261/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((49/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(5873998749/12500000000000),(-239755051/6250000000000),(24464801/12500000000000),(-7988507/100000000000000)⟩
def e151 : ℝ := (344921/100000000000000)
theorem h151 : Model (fun x => f151 ((49/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (498922389/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(149643278342101/100000000000000),(-614924714293/50000000000000),(9073132003/50000000000000),(-86827741/25000000000000)⟩
def e152 : ℝ := (428124639/20000000000000)
theorem h152 : Model (fun x => f152 ((49/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(169/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((49/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(21801/1600),(149/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((49/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(267/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((49/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(7490636704119/100000000000000),(-1683289147/2000000000000),(47283403/5000000000000),(-2656371/25000000000000)⟩
def e156 : ℝ := (60373/50000000000000)
theorem h156 : Model (fun x => f156 ((49/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (66/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(102064606741561/100000000000000),(124168875981/50000000000000),(945668059/50000000000000),(-21250971/100000000000000)⟩
def e157 : ℝ := (1531201/50000000000000)
theorem h157 : Model (fun x => f157 ((49/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(202064606741561/100000000000000),(124168875981/50000000000000),(945668059/50000000000000),(-21250971/100000000000000)⟩
def e158 : ℝ := (1531201/50000000000000)
theorem h158 : Model (fun x => f158 ((49/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(5051615168539/5000000000000),(124168875981/100000000000000),(945668059/100000000000000),(-5312743/50000000000000)⟩
def e159 : ℝ := (765601/50000000000000)
theorem h159 : Model (fun x => f159 ((49/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(51615168539/5000000000000),(124168875981/100000000000000),(945668059/100000000000000),(-5312743/50000000000000)⟩
def e160 : ℝ := (765601/50000000000000)
theorem h160 : Model (fun x => f160 ((49/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((49/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((49/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(37285731005883/10000000000000),(229121140203/50000000000000),(697993091/20000000000000),(-2450819/6250000000000)⟩
def e163 : ℝ := (1412717/25000000000000)
theorem h163 : Model (fun x => f163 ((49/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(545714319154623/20000000000000),(229121140203/50000000000000),(697993091/20000000000000),(-2450819/6250000000000)⟩
def e164 : ℝ := (5650869/100000000000000)
theorem h164 : Model (fun x => f164 ((49/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((49/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1378369366165213/50000000000000),(3851009411721/100000000000000),(29898216823/100000000000000),(-160437497/50000000000000)⟩
def e166 : ℝ := (47568413/100000000000000)
theorem h166 : Model (fun x => f166 ((49/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4019559842355689/50000000000000),(3851009411721/100000000000000),(29898216823/100000000000000),(-160437497/50000000000000)⟩
def e167 : ℝ := (23784207/50000000000000)
theorem h167 : Model (fun x => f167 ((49/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((49/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(2030526947049423/25000000000000),(173410600787/1250000000000),(55505999653/50000000000000),(-1104840889/100000000000000)⟩
def e169 : ℝ := (171804701/100000000000000)
theorem h169 : Model (fun x => f169 ((49/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13391155407245311/100000000000000),(173410600787/1250000000000),(55505999653/50000000000000),(-1104840889/100000000000000)⟩
def e170 : ℝ := (85902351/50000000000000)
theorem h170 : Model (fun x => f170 ((49/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((49/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(3382348188975173/25000000000000),(15321852545591/50000000000000),(6400490471/2500000000000),(-1135044049/50000000000000)⟩
def e172 : ℝ := (95217871/25000000000000)
theorem h172 : Model (fun x => f172 ((49/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(15865107041614977/100000000000000),(15321852545591/50000000000000),(6400490471/2500000000000),(-1135044049/50000000000000)⟩
def e173 : ℝ := (76174297/20000000000000)
theorem h173 : Model (fun x => f173 ((49/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((49/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(16028883076383423/100000000000000),(2026382647141/4000000000000),(27921481999/6250000000000),(-210723913/6250000000000)⟩
def e175 : ℝ := (632382419/100000000000000)
theorem h175 : Model (fun x => f175 ((49/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(26290022446023/160000000000),(2026382647141/4000000000000),(27921481999/6250000000000),(-210723913/6250000000000)⟩
def e176 : ℝ := (31619121/5000000000000)
theorem h176 : Model (fun x => f176 ((49/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((49/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(16600884521195071/100000000000000),(14317008488359/20000000000000),(167411022973/25000000000000),(-4118501247/100000000000000)⟩
def e178 : ℝ := (448752261/50000000000000)
theorem h178 : Model (fun x => f178 ((49/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(16583265473576023/100000000000000),(14317008488359/20000000000000),(167411022973/25000000000000),(-4118501247/100000000000000)⟩
def e179 : ℝ := (897504523/100000000000000)
theorem h179 : Model (fun x => f179 ((49/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((49/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(2094306885255643/12500000000000),(4645763579369/5000000000000),(461132918859/50000000000000),(-4414622803/100000000000000)⟩
def e181 : ℝ := (292355079/25000000000000)
theorem h181 : Model (fun x => f181 ((49/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(16757788415378477/100000000000000),(4645763579369/5000000000000),(461132918859/50000000000000),(-4414622803/100000000000000)⟩
def e182 : ℝ := (1169420317/100000000000000)
theorem h182 : Model (fun x => f182 ((49/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(43247803670033/25000000000000),(4353424999043/20000000000000),(141682741057/50000000000000),(197668407/100000000000000)⟩
def e183 : ℝ := (278340651/100000000000000)
theorem h183 : Model (fun x => f183 ((49/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(102075263244053/100000000000000),(125450675473/50000000000000),(1032519771/50000000000000),(-2390237/12500000000000)⟩
def e184 : ℝ := (3115497/100000000000000)
theorem h184 : Model (fun x => f184 ((49/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(10051615168539/5000000000000),(124168875981/100000000000000),(945668059/100000000000000),(-5312743/50000000000000)⟩
def e185 : ℝ := (765601/50000000000000)
theorem h185 : Model (fun x => f185 ((49/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(404139869985613/100000000000000),(124809775727/25000000000000),(197818783/5000000000000),(-10093217/25000000000000)⟩
def e186 : ℝ := (6177901/100000000000000)
theorem h186 : Model (fun x => f186 ((49/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(812451689471753/100000000000000),(301089560371/20000000000000),(2479062873/20000000000000),(-572353/500000000000)⟩
def e187 : ℝ := (9344891/50000000000000)
theorem h187 : Model (fun x => f187 ((49/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1633290345119881/100000000000000),(4035248522819/100000000000000),(17235489857/50000000000000),(-286822163/100000000000000)⟩
def e188 : ℝ := (25123349/50000000000000)
theorem h188 : Model (fun x => f188 ((49/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(83359270966041/5000000000000),(1643387618599/20000000000000),(39519463903/50000000000000),(-13602279/3125000000000)⟩
def e189 : ℝ := (103220469/100000000000000)
theorem h189 : Model (fun x => f189 ((49/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((49/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(5051615168539/625000000000),(124168875981/12500000000000),(945668059/12500000000000),(-5312743/6250000000000)⟩
def e191 : ℝ := (765601/6250000000000)
theorem h191 : Model (fun x => f191 ((49/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(910333690210293/100000000000000),(622126179397/50000000000000),(4815192007/50000000000000),(-13015723/12500000000000)⟩
def e192 : ℝ := (15365113/100000000000000)
theorem h192 : Model (fun x => f192 ((49/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1010333690210293/100000000000000),(622126179397/50000000000000),(4815192007/50000000000000),(-13015723/12500000000000)⟩
def e193 : ℝ := (15365113/100000000000000)
theorem h193 : Model (fun x => f193 ((49/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(16844135969671987/100000000000000),(5188124388131/5000000000000),(1061352720153/100000000000000),(-4358912509/100000000000000)⟩
def e194 : ℝ := (261618001/20000000000000)
theorem h194 : Model (fun x => f194 ((49/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(593678418293/100000000000000),(-1828575527/50000000000000),(-14879191/100000000000000),(475727/100000000000000)⟩
def e195 : ℝ := (24837/50000000000000)
theorem h195 : Model (fun x => f195 ((49/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (167393064621867/1000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(513505753549/50000000000000),(30725043337/25000000000000),(860483377/100000000000000),(-2901349/25000000000000)⟩
def e196 : ℝ := (1815039/100000000000000)
theorem h196 : Model (fun x => f196 ((49/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(102064606741561/50000000000000),(124168875981/25000000000000),(945668059/25000000000000),(-21250971/50000000000000)⟩
def e197 : ℝ := (1531201/25000000000000)
theorem h197 : Model (fun x => f197 ((49/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(24744561062071/50000000000000),(-760277711/1250000000000),(-77694073/20000000000000),(6251461/100000000000000)⟩
def e198 : ℝ := (762453/100000000000000)
theorem h198 : Model (fun x => f198 ((49/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (50453588335027/25000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(3156929867241/3125000000000),(121644433757/100000000000000),(776940729/100000000000000),(-12502923/100000000000000)⟩
def e199 : ℝ := (57971/1250000000000)
theorem h199 : Model (fun x => f199 ((49/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(31929867241/3125000000000),(121644433757/100000000000000),(776940729/100000000000000),(-12502923/100000000000000)⟩
def e200 : ℝ := (57971/1250000000000)
theorem h200 : Model (fun x => f200 ((49/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(186409192160897/50000000000000),(112231471621/25000000000000),(2867281261/100000000000000),(-2307087/5000000000000)⟩
def e201 : ℝ := (68461/400000000000)
theorem h201 : Model (fun x => f201 ((49/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2728532670036079/100000000000000),(112231471621/25000000000000),(2867281261/100000000000000),(-2307087/5000000000000)⟩
def e202 : ℝ := (17115251/100000000000000)
theorem h202 : Model (fun x => f202 ((49/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2756411609529513/100000000000000),(377262092889/10000000000000),(12320876421/50000000000000),(-380783759/100000000000000)⟩
def e203 : ℝ := (143963357/100000000000000)
theorem h203 : Model (fun x => f203 ((49/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1607758512382093/20000000000000),(377262092889/10000000000000),(12320876421/50000000000000),(-380783759/100000000000000)⟩
def e204 : ℝ := (71981679/50000000000000)
theorem h204 : Model (fun x => f204 ((49/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(8120929387279981/100000000000000),(13589911593057/100000000000000),(91939368269/100000000000000),(-665236067/50000000000000)⟩
def e205 : ℝ := (519349703/100000000000000)
theorem h205 : Model (fun x => f205 ((49/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(33474942515819/250000000000),(13589911593057/100000000000000),(91939368269/100000000000000),(-665236067/50000000000000)⟩
def e206 : ℝ := (64918713/12500000000000)
theorem h206 : Model (fun x => f206 ((49/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(6763394933271333/50000000000000),(30016929005951/100000000000000),(213442320023/100000000000000),(-2800780143/100000000000000)⟩
def e207 : ℝ := (114953621/10000000000000)
theorem h207 : Model (fun x => f207 ((49/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(15862504152256951/100000000000000),(30016929005951/100000000000000),(213442320023/100000000000000),(-2800780143/100000000000000)⟩
def e208 : ℝ := (1149536211/100000000000000)
theorem h208 : Model (fun x => f208 ((49/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(16024580200798191/100000000000000),(198477928241/400000000000),(375379357923/100000000000000),(-4319819507/100000000000000)⟩
def e209 : ℝ := (119080869/6250000000000)
theorem h209 : Model (fun x => f209 ((49/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16426961153179143/100000000000000),(198477928241/400000000000),(375379357923/100000000000000),(-4319819507/100000000000000)⟩
def e210 : ℝ := (381058781/20000000000000)
theorem h210 : Model (fun x => f210 ((49/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(8297402286796623/50000000000000),(70108955850437/100000000000000),(35450119239/6250000000000),(-1393916439/25000000000000)⟩
def e211 : ℝ := (674966533/25000000000000)
theorem h211 : Model (fun x => f211 ((49/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(8288592762987099/50000000000000),(70108955850437/100000000000000),(35450119239/6250000000000),(-1393916439/25000000000000)⟩
def e212 : ℝ := (2699866133/100000000000000)
theorem h212 : Model (fun x => f212 ((49/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(1046660242034863/6250000000000),(45495260802611/50000000000000),(787075874371/100000000000000),(-3235296801/50000000000000)⟩
def e213 : ℝ := (1757044463/50000000000000)
theorem h213 : Model (fun x => f213 ((49/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(16749897205891141/100000000000000),(45495260802611/50000000000000),(787075874371/100000000000000),(-3235296801/50000000000000)⟩
def e214 : ℝ := (3514088927/100000000000000)
theorem h214 : Model (fun x => f214 ((49/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(1069643988169/625000000000),(21305018498999/100000000000000),(124431835627/50000000000000),(-495964001/100000000000000)⟩
def e215 : ℝ := (834553259/100000000000000)
theorem h215 : Model (fun x => f215 ((49/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(20410790270317/20000000000000),(245774685511/100000000000000),(1717732013/100000000000000),(-4674227/20000000000000)⟩
def e216 : ℝ := (2351517/25000000000000)
theorem h216 : Model (fun x => f216 ((49/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(6281929867241/3125000000000),(121644433757/100000000000000),(776940729/100000000000000),(-12502923/100000000000000)⟩
def e217 : ℝ := (57971/1250000000000)
theorem h217 : Model (fun x => f217 ((49/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(404097462855009/100000000000000),(19562542121/4000000000000),(3271613471/100000000000000),(-48376981/100000000000000)⟩
def e218 : ℝ := (4670357/25000000000000)
theorem h218 : Model (fun x => f218 ((49/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(812323814779261/100000000000000),(368671552887/25000000000000),(2577792801/25000000000000),(-69996391/50000000000000)⟩
def e219 : ℝ := (1410889/2500000000000)
theorem h219 : Model (fun x => f219 ((49/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(326589518971711/20000000000000),(3952586819043/100000000000000),(7208211413/25000000000000),(-179489883/50000000000000)⟩
def e220 : ℝ := (30307133/20000000000000)
theorem h220 : Model (fun x => f220 ((49/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1666487544053827/100000000000000),(4023571422629/50000000000000),(67189179691/100000000000000),(-304616369/50000000000000)⟩
def e221 : ℝ := (155158839/50000000000000)
theorem h221 : Model (fun x => f221 ((49/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(3156929867241/390625000000),(121644433757/12500000000000),(776940729/12500000000000),(-12502923/12500000000000)⟩
def e222 : ℝ := (57971/156250000000)
theorem h222 : Model (fun x => f222 ((49/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(910227997365281/100000000000000),(1218930155567/100000000000000),(1586651569/20000000000000),(-123394519/100000000000000)⟩
def e223 : ℝ := (11626877/25000000000000)
theorem h223 : Model (fun x => f223 ((49/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1010227997365281/100000000000000),(1218930155567/100000000000000),(1586651569/20000000000000),(-123394519/100000000000000)⟩
def e224 : ℝ := (11626877/25000000000000)
theorem h224 : Model (fun x => f224 ((49/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(16835323742636831/100000000000000),(101607809224013/100000000000000),(181811941813/20000000000000),(-3376802107/50000000000000)⟩
def e225 : ℝ := (3929697207/100000000000000)
theorem h225 : Model (fun x => f225 ((49/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(593989171391/100000000000000),(-3584958587/100000000000000),(-10437093/100000000000000),(123713/25000000000000)⟩
def e226 : ℝ := (144261/100000000000000)
theorem h226 : Model (fun x => f226 ((49/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (4183199047600583/25000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(203314222789/20000000000000),(60207047903/50000000000000),(69658481/10000000000000),(-206943/1562500000000)⟩
def e227 : ℝ := (1340919/25000000000000)
theorem h227 : Model (fun x => f227 ((49/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(2043582621043/100000000000000),(121657134577/50000000000000),(1557068187/100000000000000),(-6212437/25000000000000)⟩
def e228 : ℝ := (1435743/20000000000000)
theorem h228 : Model (fun x => f228 ((49/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(1529042014879/50000000000000),(42371307481/12500000000000),(-291517371/100000000000000),(-19280709/100000000000000)⟩
def e229 : ℝ := (1502171/2500000000000)
theorem h229 : Model (fun x => f229 ((49/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(2496395126333/100000000000000),(112881870077/50000000000000),(-4845396633/100000000000000),(83146291/100000000000000)⟩
def e230 : ℝ := (52698047/100000000000000)
theorem h230 : Model (fun x => f230 ((49/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-59463001311497/100000000000000),(-641503001953/12500000000000),(66031560287/50000000000000),(-718208827/25000000000000)⟩
def e231 : ℝ := (77476359/50000000000000)
theorem h231 : Model (fun x => f231 ((49/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((49/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2401/320),(-49/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((49/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1029/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((49/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5831/320),(7/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((49/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((49/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14151/320),(7/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((49/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((49/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(353775/32),(875/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((49/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(9359/1600),(71/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((49/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(18959/1600),(71/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((49/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((49/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3583251/1600),(13419/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((49/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(2790761797/6250000000000),(-334438041/100000000000000),(4860087/100000000000000),(-27021/50000000000000)⟩
def e244 : ℝ := (21/3125000000000)
theorem h244 : Model (fun x => f244 ((49/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (55566/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(493650877366837/100000000000000),(-156931592339/12500000000000),(556437121/100000000000000),(-14078783/20000000000000)⟩
def e245 : ℝ := (14261137/100000000000000)
theorem h245 : Model (fun x => f245 ((49/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(441/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((49/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(37681/1600),(409/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((49/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(71281/1600),(409/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((49/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(16641/1600),(129/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((49/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1186187121/2560000),(8000709/640000),(149483/1280000),(269/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((49/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((49/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(71289/160),(801/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((49/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(56109638233/25000000000000),(-1260890747/25000000000000),(8500387/10000000000000),(-1273467/100000000000000)⟩
def e253 : ℝ := (18467/100000000000000)
theorem h253 : Model (fun x => f253 ((49/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (34839/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(103994578493677/100000000000000),(468773727047/100000000000000),(636882137/25000000000000),(-4419001/20000000000000)⟩
def e254 : ℝ := (3421111/20000000000000)
theorem h254 : Model (fun x => f254 ((49/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(203994578493677/100000000000000),(468773727047/100000000000000),(636882137/25000000000000),(-4419001/20000000000000)⟩
def e255 : ℝ := (3421111/20000000000000)
theorem h255 : Model (fun x => f255 ((49/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(50998644623419/50000000000000),(234386863523/100000000000000),(636882137/50000000000000),(-11047503/100000000000000)⟩
def e256 : ℝ := (8552779/100000000000000)
theorem h256 : Model (fun x => f256 ((49/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(998644623419/50000000000000),(234386863523/100000000000000),(636882137/50000000000000),(-11047503/100000000000000)⟩
def e257 : ℝ := (8552779/100000000000000)
theorem h257 : Model (fun x => f257 ((49/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(47052320932321/12500000000000),(108124892399/12500000000000),(188031869/4000000000000),(-40770547/100000000000000)⟩
def e258 : ℝ := (31563829/100000000000000)
theorem h258 : Model (fun x => f258 ((49/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2732132853172853/100000000000000),(108124892399/12500000000000),(188031869/4000000000000),(-40770547/100000000000000)⟩
def e259 : ℝ := (3156383/10000000000000)
theorem h259 : Model (fun x => f259 ((49/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1393350724429301/50000000000000),(7286036175817/100000000000000),(20811530893/50000000000000),(-80345303/25000000000000)⟩
def e260 : ℝ := (266148603/100000000000000)
theorem h260 : Model (fun x => f260 ((49/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4034541200619777/50000000000000),(7286036175817/100000000000000),(20811530893/50000000000000),(-80345303/25000000000000)⟩
def e261 : ℝ := (66537151/25000000000000)
theorem h261 : Model (fun x => f261 ((49/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(8230245316358009/100000000000000),(26344428548229/100000000000000),(162312995257/100000000000000),(-102886633/10000000000000)⟩
def e262 : ℝ := (481942951/50000000000000)
theorem h262 : Model (fun x => f262 ((49/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(3374823233851407/25000000000000),(26344428548229/100000000000000),(162312995257/100000000000000),(-102886633/10000000000000)⟩
def e263 : ℝ := (963885903/100000000000000)
theorem h263 : Model (fun x => f263 ((49/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(6884456430801823/50000000000000),(29255586147921/50000000000000),(199625952849/50000000000000),(-1824744301/100000000000000)⟩
def e264 : ℝ := (107276331/5000000000000)
theorem h264 : Model (fun x => f264 ((49/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(16104627147317931/100000000000000),(29255586147921/50000000000000),(199625952849/50000000000000),(-1824744301/100000000000000)⟩
def e265 : ℝ := (2145526621/100000000000000)
theorem h265 : Model (fun x => f265 ((49/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(3285256626714933/20000000000000),(97426940100977/100000000000000),(23421987803/3125000000000),(-979630231/50000000000000)⟩
def e266 : ℝ := (3581590389/100000000000000)
theorem h266 : Model (fun x => f266 ((49/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(16828664085955617/100000000000000),(97426940100977/100000000000000),(23421987803/3125000000000),(-979630231/50000000000000)⟩
def e267 : ℝ := (358159039/10000000000000)
theorem h267 : Model (fun x => f267 ((49/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(1072798824008181/6250000000000),(13881701582303/10000000000000),(150898353093/12500000000000),(-214953043/25000000000000)⟩
def e268 : ℝ := (5115198201/100000000000000)
theorem h268 : Model (fun x => f268 ((49/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(2143395267063981/12500000000000),(13881701582303/10000000000000),(150898353093/12500000000000),(-214953043/25000000000000)⟩
def e269 : ℝ := (2557599101/50000000000000)
theorem h269 : Model (fun x => f269 ((49/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(4372410140500569/25000000000000),(90890144333909/50000000000000),(1775081112107/100000000000000),(1826370529/100000000000000)⟩
def e270 : ℝ := (1677518183/25000000000000)
theorem h270 : Model (fun x => f270 ((49/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(17492973895335609/100000000000000),(90890144333909/50000000000000),(1775081112107/100000000000000),(1826370529/100000000000000)⟩
def e271 : ℝ := (6710072733/100000000000000)
theorem h271 : Model (fun x => f271 ((49/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(87346321640929/25000000000000),(44631911008607/100000000000000),(27373674929/4000000000000),(1144987601/25000000000000)⟩
def e272 : ℝ := (3259083/195312500000)
theorem h272 : Model (fun x => f272 ((49/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(104034470137031/100000000000000),(29883530893/6250000000000),(3147782079/100000000000000),(-3313047/20000000000000)⟩
def e273 : ℝ := (17523367/100000000000000)
theorem h273 : Model (fun x => f273 ((49/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(100998644623419/50000000000000),(234386863523/100000000000000),(636882137/50000000000000),(-11047503/100000000000000)⟩
def e274 : ℝ := (8552779/100000000000000)
theorem h274 : Model (fun x => f274 ((49/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(408029048630707/100000000000000),(473455110667/50000000000000),(5695310627/100000000000000),(-38660241/100000000000000)⟩
def e275 : ℝ := (1385157/4000000000000)
theorem h275 : Model (fun x => f275 ((49/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(82420761757369/10000000000000),(717274867011/25000000000000),(18921134497/100000000000000),(-97759197/100000000000000)⟩
def e276 : ℝ := (26283553/25000000000000)
theorem h276 : Model (fun x => f276 ((49/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(832438522632399/50000000000000),(482958595937/6250000000000),(55443433209/100000000000000),(-6488471/3125000000000)⟩
def e277 : ℝ := (283664147/100000000000000)
theorem h277 : Model (fun x => f277 ((49/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(173204601247429/10000000000000),(15999479398663/100000000000000),(18379275503/12500000000000),(16536353/100000000000000)⟩
def e278 : ℝ := (295061753/50000000000000)
theorem h278 : Model (fun x => f278 ((49/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(50998644623419/6250000000000),(234386863523/12500000000000),(636882137/6250000000000),(-11047503/12500000000000)⟩
def e279 : ℝ := (8552779/12500000000000)
theorem h279 : Model (fun x => f279 ((49/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(184002556822347/20000000000000),(294153925309/12500000000000),(13337896271/100000000000000),(-104945259/100000000000000)⟩
def e280 : ℝ := (85945599/100000000000000)
theorem h280 : Model (fun x => f280 ((49/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(204002556822347/20000000000000),(294153925309/12500000000000),(13337896271/100000000000000),(-104945259/100000000000000)⟩
def e281 : ℝ := (85945599/100000000000000)
theorem h281 : Model (fun x => f281 ((49/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(8833545376967647/50000000000000),(40791157185699/20000000000000),(526822738003/25000000000000),(493127721/12500000000000)⟩
def e282 : ℝ := (1884789599/25000000000000)
theorem h282 : Model (fun x => f282 ((49/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(566024148473/100000000000000),(-6534403523/100000000000000),(1980403/25000000000000),(280783/50000000000000)⟩
def e283 : ℝ := (253329/100000000000000)
theorem h283 : Model (fun x => f283 ((49/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (17461016192874623/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(988802546581/50000000000000),(229797149759/100000000000000),(492394021/50000000000000),(-13296439/100000000000000)⟩
def e284 : ℝ := (5281931/50000000000000)
theorem h284 : Model (fun x => f284 ((49/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(103994578493677/50000000000000),(468773727047/50000000000000),(636882137/12500000000000),(-4419001/10000000000000)⟩
def e285 : ℝ := (3421111/10000000000000)
theorem h285 : Model (fun x => f285 ((49/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(6127613827927/12500000000000),(-563243277/500000000000),(-353320367/100000000000000),(94103/1250000000000)⟩
def e286 : ℝ := (83097/2000000000000)
theorem h286 : Model (fun x => f286 ((49/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (101761609018761/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(101958178753167/100000000000000),(225297310799/100000000000000),(706640731/100000000000000),(-7528241/50000000000000)⟩
def e287 : ℝ := (25592969/100000000000000)
theorem h287 : Model (fun x => f287 ((49/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(1958178753167/100000000000000),(225297310799/100000000000000),(706640731/100000000000000),(-7528241/50000000000000)⟩
def e288 : ℝ := (25592969/100000000000000)
theorem h288 : Model (fun x => f288 ((49/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(188137115556439/50000000000000),(415727180641/50000000000000),(325980099/12500000000000),(-55565589/100000000000000)⟩
def e289 : ℝ := (18890049/20000000000000)
theorem h289 : Model (fun x => f289 ((49/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2731988516827163/100000000000000),(415727180641/50000000000000),(325980099/12500000000000),(-55565589/100000000000000)⟩
def e290 : ℝ := (47225123/50000000000000)
theorem h290 : Model (fun x => f290 ((49/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1392742867751317/50000000000000),(280113295347/4000000000000),(11918747459/50000000000000),(-57030529/12500000000000)⟩
def e291 : ℝ := (159231289/20000000000000)
theorem h291 : Model (fun x => f291 ((49/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4033933343941793/50000000000000),(280113295347/4000000000000),(11918747459/50000000000000),(-57030529/12500000000000)⟩
def e292 : ℝ := (398078223/50000000000000)
theorem h292 : Model (fun x => f292 ((49/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(205646248479989/2500000000000),(12658323523091/50000000000000),(48546150429/50000000000000),(-315345021/20000000000000)⟩
def e293 : ℝ := (720518019/25000000000000)
theorem h293 : Model (fun x => f293 ((49/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(13494897558247179/100000000000000),(12658323523091/50000000000000),(48546150429/50000000000000),(-315345021/20000000000000)⟩
def e294 : ℝ := (2882072077/100000000000000)
theorem h294 : Model (fun x => f294 ((49/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(13759151774994427/100000000000000),(11243206708693/20000000000000),(251391709397/100000000000000),(-3241812941/100000000000000)⟩
def e295 : ℝ := (6411976473/100000000000000)
theorem h295 : Model (fun x => f295 ((49/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(2011858257588589/12500000000000),(11243206708693/20000000000000),(251391709397/100000000000000),(-3241812941/100000000000000)⟩
def e296 : ℝ := (3205988237/50000000000000)
theorem h296 : Model (fun x => f296 ((49/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(4102508077065049/25000000000000),(5848634023729/6250000000000),(496700499433/100000000000000),(-2382494947/50000000000000)⟩
def e297 : ℝ := (10699687651/100000000000000)
theorem h297 : Model (fun x => f297 ((49/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(4203103315160287/25000000000000),(5848634023729/6250000000000),(496700499433/100000000000000),(-2382494947/50000000000000)⟩
def e298 : ℝ := (2674921913/25000000000000)
theorem h298 : Model (fun x => f298 ((49/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(8570815182502827/50000000000000),(133288486677153/100000000000000),(418029592913/50000000000000),(-5609340739/100000000000000)⟩
def e299 : ℝ := (15281690467/100000000000000)
theorem h299 : Model (fun x => f299 ((49/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(8562005658693303/50000000000000),(133288486677153/100000000000000),(418029592913/50000000000000),(-5609340739/100000000000000)⟩
def e300 : ℝ := (3820422617/25000000000000)
theorem h300 : Model (fun x => f300 ((49/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(17459330068693583/100000000000000),(174478450502671/100000000000000),(318432833501/25000000000000),(-5471965741/100000000000000)⟩
def e301 : ℝ := (20059312199/100000000000000)
theorem h301 : Model (fun x => f301 ((49/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(4365665850506729/25000000000000),(174478450502671/100000000000000),(318432833501/25000000000000),(-5471965741/100000000000000)⟩
def e302 : ℝ := (100296561/500000000000)
theorem h302 : Model (fun x => f302 ((49/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(8548754111889/2500000000000),(21379755492623/50000000000000),(541435485577/100000000000000),(683102299/50000000000000)⟩
def e303 : ℝ := (498216489/10000000000000)
theorem h303 : Model (fun x => f303 ((49/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(103954702146627/100000000000000),(459418069741/100000000000000),(1948544821/100000000000000),(-5503709/20000000000000)⟩
def e304 : ℝ := (26183507/50000000000000)
theorem h304 : Model (fun x => f304 ((49/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(201958178753167/100000000000000),(225297310799/100000000000000),(706640731/100000000000000),(-7528241/50000000000000)⟩
def e305 : ℝ := (25592969/100000000000000)
theorem h305 : Model (fun x => f305 ((49/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(407871059652961/100000000000000),(910012691339/100000000000000),(3361826283/100000000000000),(-57631509/100000000000000)⟩
def e306 : ℝ := (12944119/12500000000000)
theorem h306 : Model (fun x => f306 ((49/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(823728963736363/100000000000000),(344595948347/12500000000000),(2930475073/25000000000000),(-32759591/20000000000000)⟩
def e307 : ℝ := (314231847/100000000000000)
theorem h307 : Model (fun x => f307 ((49/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(831794006512147/50000000000000),(185583920357/2500000000000),(35705063953/100000000000000),(-204469201/50000000000000)⟩
def e308 : ℝ := (847556721/100000000000000)
theorem h308 : Model (fun x => f308 ((49/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(345875592777279/20000000000000),(3839938100861/25000000000000),(5181854677/5000000000000),(-143555741/25000000000000)⟩
def e309 : ℝ := (110206717/6250000000000)
theorem h309 : Model (fun x => f309 ((49/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(101958178753167/12500000000000),(225297310799/12500000000000),(706640731/12500000000000),(-7528241/6250000000000)⟩
def e310 : ℝ := (25592969/12500000000000)
theorem h310 : Model (fun x => f310 ((49/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(919620132171963/100000000000000),(2261796556133/100000000000000),(7601670669/100000000000000),(-147970401/100000000000000)⟩
def e311 : ℝ := (128555383/50000000000000)
theorem h311 : Model (fun x => f311 ((49/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1019620132171963/100000000000000),(2261796556133/100000000000000),(7601670669/100000000000000),(-147970401/100000000000000)⟩
def e312 : ℝ := (128555383/50000000000000)
theorem h312 : Model (fun x => f312 ((49/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(17633085881131263/100000000000000),(195726138986987/100000000000000),(76778631923/5000000000000),(-4902202447/100000000000000)⟩
def e313 : ℝ := (1126663669/5000000000000)
theorem h313 : Model (fun x => f313 ((49/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(141778927231/25000000000000),(-1573737133/25000000000000),(2560801/12500000000000),(23923/5000000000000)⟩
def e314 : ℝ := (750063/100000000000000)
theorem h314 : Model (fun x => f314 ((49/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (17435796734029989/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(242406637429/12500000000000),(220970316997/100000000000000),(448929789/100000000000000),(-7969571/50000000000000)⟩
def e315 : ℝ := (3961421/12500000000000)
theorem h315 : Model (fun x => f315 ((49/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1958429096297/50000000000000),(112691866689/25000000000000),(1433717831/100000000000000),(-29235581/100000000000000)⟩
def e316 : ℝ := (4225523/10000000000000)
theorem h316 : Model (fun x => f316 ((49/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(3867120966591/20000000000000),(1088021625537/50000000000000),(720091499/50000000000000),(-32514069/20000000000000)⟩
def e317 : ℝ := (209806059/100000000000000)
theorem h317 : Model (fun x => f317 ((49/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(631366688423/4000000000000),(1454235976171/100000000000000),(-14251312819/50000000000000),(448975751/100000000000000)⟩
def e318 : ℝ := (189915431/100000000000000)
theorem h318 : Model (fun x => f318 ((49/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-21839417050461/50000000000000),(-3677788039453/100000000000000),(12945061867/12500000000000),(-2423859557/100000000000000)⟩
def e319 : ℝ := (344868149/100000000000000)
theorem h319 : Model (fun x => f319 ((49/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((49/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-26411/1600),(-539/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((49/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((49/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(4753/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((49/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(163709/1600),(1401/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((49/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((49/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(336509/1600),(1401/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((49/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1682545/32),(7005/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((49/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((49/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(867366965517585661/100000000000000),(1299289088068961/20000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (112823/100000000000000)
theorem h329 : Model (fun x => f329 ((49/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(288228639/2500000000000),(-86351531/100000000000000),(1254869/100000000000000),(-6977/50000000000000)⟩
def e330 : ℝ := (7/4000000000000)
theorem h330 : Model (fun x => f330 ((49/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (215206192615337739/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(303098534628909/50000000000000),(507281017787/100000000000000),(4179462601/50000000000000),(-2242547/6250000000000)⟩
def e331 : ℝ := (3513673/20000000000000)
theorem h331 : Model (fun x => f331 ((49/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((49/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(409/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((49/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((49/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((49/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(495806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((49/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((49/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((49/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2199642125289539/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (203/20000000000000)
theorem h339 : Model (fun x => f339 ((49/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3594193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((49/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((49/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((49/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1012678937355101/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (507/50000000000000)
theorem h343 : Model (fun x => f343 ((49/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(4937399027039/100000000000000),(-34342887/500000000000),(4777551/50000000000000),(-13293/100000000000000)⟩
def e344 : ℝ := (23/100000000000000)
theorem h344 : Model (fun x => f344 ((49/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2022540333074707/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(21721021778477/20000000000000),(944152361613/100000000000000),(-656720637/50000000000000),(913579/50000000000000)⟩
def e345 : ℝ := (3513/100000000000000)
theorem h345 : Model (fun x => f345 ((49/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(41721021778477/20000000000000),(944152361613/100000000000000),(-656720637/50000000000000),(913579/50000000000000)⟩
def e346 : ℝ := (3513/100000000000000)
theorem h346 : Model (fun x => f346 ((49/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(6518909652887/6250000000000),(236038090403/50000000000000),(-656720637/100000000000000),(913579/100000000000000)⟩
def e347 : ℝ := (879/50000000000000)
theorem h347 : Model (fun x => f347 ((49/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(268909652887/6250000000000),(236038090403/50000000000000),(-656720637/100000000000000),(913579/100000000000000)⟩
def e348 : ℝ := (879/50000000000000)
theorem h348 : Model (fun x => f348 ((49/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(192463046894759/50000000000000),(348437181071/20000000000000),(-3877779/160000000000),(3371541/100000000000000)⟩
def e349 : ℝ := (649/10000000000000)
theorem h349 : Model (fun x => f349 ((49/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2740640379503803/100000000000000),(348437181071/20000000000000),(-3877779/160000000000),(3371541/100000000000000)⟩
def e350 : ℝ := (6491/100000000000000)
theorem h350 : Model (fun x => f350 ((49/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(2858557924006277/100000000000000),(590202193427/4000000000000),(-1230179537/10000000000000),(5671929/100000000000000)⟩
def e351 : ℝ := (12851/12500000000000)
theorem h351 : Model (fun x => f351 ((49/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8140938876387229/100000000000000),(590202193427/4000000000000),(-1230179537/10000000000000),(5671929/100000000000000)⟩
def e352 : ℝ := (102809/100000000000000)
theorem h352 : Model (fun x => f352 ((49/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(339648288159/4000000000),(10764266486589/20000000000000),(3360786883/100000000000000),(-37341731/50000000000000)⟩
def e353 : ℝ := (123403/25000000000000)
theorem h353 : Model (fun x => f353 ((49/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(13760254823022619/100000000000000),(10764266486589/20000000000000),(3360786883/100000000000000),(-37341731/50000000000000)⟩
def e354 : ℝ := (493613/100000000000000)
theorem h354 : Model (fun x => f354 ((49/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(14352297278717927/100000000000000),(121095910002237/100000000000000),(3344332881/2000000000000),(-72444071/25000000000000)⟩
def e355 : ℝ := (877627/100000000000000)
theorem h355 : Model (fun x => f355 ((49/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(4172002891108053/25000000000000),(121095910002237/100000000000000),(3344332881/2000000000000),(-72444071/25000000000000)⟩
def e356 : ℝ := (219407/25000000000000)
theorem h356 : Model (fun x => f356 ((49/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(696240893919149/4000000000000),(20508625510803/10000000000000),(127296512481/20000000000000),(-77828891/50000000000000)⟩
def e357 : ℝ := (2578283/100000000000000)
theorem h357 : Model (fun x => f357 ((49/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(17808403300359677/100000000000000),(20508625510803/10000000000000),(127296512481/20000000000000),(-77828891/50000000000000)⟩
def e358 : ℝ := (644571/25000000000000)
theorem h358 : Model (fun x => f358 ((49/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(3714923909671021/20000000000000),(18623714566161/6250000000000),(1515079472071/100000000000000),(1658177601/100000000000000)⟩
def e359 : ℝ := (1516511/25000000000000)
theorem h359 : Model (fun x => f359 ((49/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(18557000500736057/100000000000000),(18623714566161/6250000000000),(1515079472071/100000000000000),(1658177601/100000000000000)⟩
def e360 : ℝ := (1213209/20000000000000)
theorem h360 : Model (fun x => f360 ((49/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(19355425550860347/100000000000000),(996008349101/250000000000),(2865088866533/100000000000000),(7094491331/100000000000000)⟩
def e361 : ℝ := (7290483/100000000000000)
theorem h361 : Model (fun x => f361 ((49/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(241984486052421/1250000000000),(996008349101/250000000000),(2865088866533/100000000000000),(7094491331/100000000000000)⟩
def e362 : ℝ := (1822621/25000000000000)
theorem h362 : Model (fun x => f362 ((49/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(832921141099463/100000000000000),(108529610195419/100000000000000),(469226578433/25000000000000),(2278221411/20000000000000)⟩
def e363 : ℝ := (1903151/10000000000000)
theorem h363 : Model (fun x => f363 ((49/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(13598778580001/12500000000000),(39391001241/4000000000000),(214651601/25000000000000),(-4294671/100000000000000)⟩
def e364 : ℝ := (16637/100000000000000)
theorem h364 : Model (fun x => f364 ((49/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(12768909652887/6250000000000),(236038090403/50000000000000),(-656720637/100000000000000),(913579/100000000000000)⟩
def e365 : ℝ := (879/50000000000000)
theorem h365 : Model (fun x => f365 ((49/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(52174417191549/12500000000000),(1928927392637/100000000000000),(-45483487/10000000000000),(-2467513/100000000000000)⟩
def e366 : ℝ := (20153/100000000000000)
theorem h366 : Model (fun x => f366 ((49/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(426374668358991/50000000000000),(2955635952427/50000000000000),(1358911547/25000000000000),(-4010697/25000000000000)⟩
def e367 : ℝ := (11523/20000000000000)
theorem h367 : Model (fun x => f367 ((49/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(435547169484449/25000000000000),(16102506002503/100000000000000),(16705344891/50000000000000),(-38145439/100000000000000)⟩
def e368 : ℝ := (190661/100000000000000)
theorem h368 : Model (fun x => f368 ((49/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(94766552303443/5000000000000),(34674592190569/100000000000000),(52469891961/25000000000000),(43869687/12500000000000)⟩
def e369 : ℝ := (1283929/100000000000000)
theorem h369 : Model (fun x => f369 ((49/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(6518909652887/781250000000),(236038090403/6250000000000),(-656720637/12500000000000),(913579/12500000000000)⟩
def e370 : ℝ := (879/6250000000000)
theorem h370 : Model (fun x => f370 ((49/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(117901333026193/12500000000000),(4761384477473/100000000000000),(-1098789673/25000000000000),(3013961/100000000000000)⟩
def e371 : ℝ := (30701/100000000000000)
theorem h371 : Model (fun x => f371 ((49/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(130401333026193/12500000000000),(4761384477473/100000000000000),(-1098789673/25000000000000),(3013961/100000000000000)⟩
def e372 : ℝ := (30701/100000000000000)
theorem h372 : Model (fun x => f372 ((49/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(4943073898666163/25000000000000),(225986520863717/50000000000000),(46964673459/1250000000000),(97500163/800000000000)⟩
def e373 : ℝ := (22587957/100000000000000)
theorem h373 : Model (fun x => f373 ((49/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(252879084073/50000000000000),(-2312215661/20000000000000),(168168351/100000000000000),(-195903/10000000000000)⟩
def e374 : ℝ := (4261/20000000000000)
theorem h374 : Model (fun x => f374 ((49/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (9658276584476083/50000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(168502668213/4000000000000),(226301351539/50000000000000),(-1653876481/100000000000000),(3408063/50000000000000)⟩
def e375 : ℝ := (604003/100000000000000)
theorem h375 : Model (fun x => f375 ((49/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(21721021778477/10000000000000),(944152361613/50000000000000),(-656720637/25000000000000),(913579/25000000000000)⟩
def e376 : ℝ := (3513/50000000000000)
theorem h376 : Model (fun x => f376 ((49/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(9587492898037/20000000000000),(-27120782509/12500000000000),(320956007/25000000000000),(-7596589/100000000000000)⟩
def e377 : ℝ := (9089/20000000000000)
theorem h377 : Model (fun x => f377 ((49/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (207659641258827/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(104125071019627/100000000000000),(433932520141/100000000000000),(-2567648059/100000000000000),(15193177/100000000000000)⟩
def e378 : ℝ := (288303/100000000000000)
theorem h378 : Model (fun x => f378 ((49/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(4125071019627/100000000000000),(433932520141/100000000000000),(-2567648059/100000000000000),(15193177/100000000000000)⟩
def e379 : ℝ := (288303/100000000000000)
theorem h379 : Model (fun x => f379 ((49/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(15370843817183/4000000000000),(1601417633853/100000000000000),(-2368961007/25000000000000),(56070057/100000000000000)⟩
def e380 : ℝ := (1063979/100000000000000)
theorem h380 : Model (fun x => f380 ((49/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(136999269057193/5000000000000),(1601417633853/100000000000000),(-2368961007/25000000000000),(56070057/100000000000000)⟩
def e381 : ℝ := (53199/5000000000000)
theorem h381 : Model (fun x => f381 ((49/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(2853011724043441/100000000000000),(6778582432231/50000000000000),(-18317709721/25000000000000),(392436277/100000000000000)⟩
def e382 : ℝ := (9749429/100000000000000)
theorem h382 : Model (fun x => f382 ((49/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8135392676424393/100000000000000),(6778582432231/50000000000000),(-18317709721/25000000000000),(392436277/100000000000000)⟩
def e383 : ℝ := (974943/10000000000000)
theorem h383 : Model (fun x => f383 ((49/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(529436462628277/6250000000000),(49418522007543/100000000000000),(-226352618017/100000000000000),(489301441/50000000000000)⟩
def e384 : ℝ := (39353319/100000000000000)
theorem h384 : Model (fun x => f384 ((49/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(13740031021100051/100000000000000),(49418522007543/100000000000000),(-226352618017/100000000000000),(489301441/50000000000000)⟩
def e385 : ℝ := (983833/2500000000000)
theorem h385 : Model (fun x => f385 ((49/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1788352132354901/12500000000000),(55539767007609/50000000000000),(-374042426121/100000000000000),(855406837/100000000000000)⟩
def e386 : ℝ := (24632709/25000000000000)
theorem h386 : Model (fun x => f386 ((49/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(16642531344553493/100000000000000),(55539767007609/50000000000000),(-374042426121/100000000000000),(855406837/100000000000000)⟩
def e387 : ℝ := (98530837/100000000000000)
theorem h387 : Model (fun x => f387 ((49/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(2166130947747501/12500000000000),(187878999360293/100000000000000),(-167391676783/50000000000000),(-211200201/20000000000000)⟩
def e388 : ℝ := (181599067/100000000000000)
theorem h388 : Model (fun x => f388 ((49/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(27705357084939/156250000000),(187878999360293/100000000000000),(-167391676783/50000000000000),(-211200201/20000000000000)⟩
def e389 : ℝ := (45399767/25000000000000)
theorem h389 : Model (fun x => f389 ((49/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(4615715638549439/25000000000000),(136285788105511/50000000000000),(11393991481/100000000000000),(-4682399799/100000000000000)⟩
def e390 : ℝ := (54825633/20000000000000)
theorem h390 : Model (fun x => f390 ((49/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(4611310876644677/25000000000000),(136285788105511/50000000000000),(11393991481/100000000000000),(-4682399799/100000000000000)⟩
def e391 : ℝ := (137064083/50000000000000)
theorem h391 : Model (fun x => f391 ((49/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(19206122900968217/100000000000000),(90963814325821/25000000000000),(721031774687/100000000000000),(-4511185087/50000000000000)⟩
def e392 : ℝ := (36152077/10000000000000)
theorem h392 : Model (fun x => f392 ((49/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(384189124686031/2000000000000),(90963814325821/25000000000000),(721031774687/100000000000000),(-4511185087/50000000000000)⟩
def e393 : ℝ := (361520771/100000000000000)
theorem h393 : Model (fun x => f393 ((49/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(158480742429821/20000000000000),(49182682657647/50000000000000),(1115398130317/100000000000000),(-458422949/12500000000000)⟩
def e394 : ℝ := (37824799/50000000000000)
theorem h394 : Model (fun x => f394 ((49/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(108420304148423/100000000000000),(225916272387/25000000000000),(-346415641/10000000000000),(2339023/25000000000000)⟩
def e395 : ℝ := (400739/50000000000000)
theorem h395 : Model (fun x => f395 ((49/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(204125071019627/100000000000000),(433932520141/100000000000000),(-2567648059/100000000000000),(15193177/100000000000000)⟩
def e396 : ℝ := (288303/100000000000000)
theorem h396 : Model (fun x => f396 ((49/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(416670446187677/100000000000000),(177153012983/10000000000000),(-537465783/6250000000000),(19871223/50000000000000)⟩
def e397 : ℝ := (344521/25000000000000)
theorem h397 : Model (fun x => f397 ((49/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(106316105524799/12500000000000),(2712102851737/50000000000000),(-20565023867/100000000000000),(30813647/50000000000000)⟩
def e398 : ℝ := (2345091/50000000000000)
theorem h398 : Model (fun x => f398 ((49/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(86807130363119/5000000000000),(14762884992623/100000000000000),(-40279564427/100000000000000),(26506271/100000000000000)⟩
def e399 : ℝ := (6843197/50000000000000)
theorem h399 : Model (fun x => f399 ((49/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1882331095244233/100000000000000),(15847439728341/50000000000000),(2959311621/10000000000000),(-68422851/10000000000000)⟩
def e400 : ℝ := (16008613/50000000000000)
theorem h400 : Model (fun x => f400 ((49/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(104125071019627/12500000000000),(433932520141/12500000000000),(-2567648059/12500000000000),(15193177/12500000000000)⟩
def e401 : ℝ := (288303/12500000000000)
theorem h401 : Model (fun x => f401 ((49/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(941420872305439/100000000000000),(1093781312669/25000000000000),(-12002670441/50000000000000),(32725377/25000000000000)⟩
def e402 : ℝ := (1553951/50000000000000)
theorem h402 : Model (fun x => f402 ((49/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1041420872305439/100000000000000),(1093781312669/25000000000000),(-12002670441/50000000000000),(32725377/25000000000000)⟩
def e403 : ℝ := (1553951/50000000000000)
theorem h403 : Model (fun x => f403 ((49/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(3920597782353803/20000000000000),(412431433163291/100000000000000),(248603913463/20000000000000),(-2195085337/20000000000000)⟩
def e404 : ℝ := (39898277/10000000000000)
theorem h404 : Model (fun x => f404 ((49/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(510126289669/100000000000000),(-10732654989/100000000000000),(193459647/100000000000000),(-388009/12500000000000)⟩
def e405 : ℝ := (29597/50000000000000)
theorem h405 : Model (fun x => f405 ((49/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (9594651542314477/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(808451931197/20000000000000),(416741631857/100000000000000),(-3334294767/100000000000000),(5456077/20000000000000)⟩
def e406 : ℝ := (732917/50000000000000)
theorem h406 : Model (fun x => f406 ((49/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(825482636131/10000000000000),(173868866987/20000000000000),(-311760703/6250000000000),(34096511/100000000000000)⟩
def e407 : ℝ := (2069837/100000000000000)
theorem h407 : Model (fun x => f407 ((49/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(25020257737291/50000000000000),(5311815047317/100000000000000),(-6284528591/25000000000000),(251093953/100000000000000)⟩
def e408 : ℝ := (14722389/100000000000000)
theorem h408 : Model (fun x => f408 ((49/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(40849400387413/100000000000000),(3502514316433/100000000000000),(-46000396847/50000000000000),(2082541873/100000000000000)⟩
def e409 : ℝ := (70122207/100000000000000)
theorem h409 : Model (fun x => f409 ((49/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-2829433713509/100000000000000),(-8763686151/5000000000000),(5779850621/50000000000000),(-85329421/25000000000000)⟩
def e410 : ℝ := (103747589/25000000000000)
theorem h410 : Model (fun x => f410 ((49/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(250521137207031/50000000000000),(11632774658203/25000000000000),(175273/10240000),(637/2048000)⟩
def e411 : ℝ := (69824219/25000000000000)
theorem h411 : Model (fun x => f411 ((49/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(28561/1600),(169/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((49/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(4826809/64000),(85683/64000),(507/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((49/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(37788052492535377/100000000000000),(4180117669677573/100000000000000),(97677828653167/50000000000000),(1002757433911/20000000000000)⟩
def e414 : ℝ := (38820923159/50000000000000)
theorem h414 : Model (fun x => f414 ((49/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(264633907819/100000000000000),(-14636913007/50000000000000),(935087967/50000000000000),(-90652093/100000000000000)⟩
def e415 : ℝ := (5750771/100000000000000)
theorem h415 : Model (fun x => f415 ((49/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (33407487736535597/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1571166470679/50000000000000),(23522203859/10000000000000),(-9600680459/100000000000000),(268310277/100000000000000)⟩
def e416 : ℝ := (16150239/10000000000000)
theorem h416 : Model (fun x => f416 ((49/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(312899227849/100000000000000),(5994831557/10000000000000),(1959020783/100000000000000),(-73007407/100000000000000)⟩
def e417 : ℝ := (288246373/50000000000000)
theorem h417 : Model (fun x => f417 ((49/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((49/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((234731806523/1500000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (6/5) (5/4) ∧
    SigmaActualBlockSeparable.endpointCellMass (6/5) (5/4) ≤ (117798272821/750000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(49/40)-(1/40)) (by norm_num : ((49/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel4


noncomputable section
namespace Hf4Quad.Panel5
open Hf4Quad.Dag

def p0 : Cubic := ⟨(51/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((51/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((51/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((51/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((51/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(223428571428571/100000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((51/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-223428571428571/100000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((51/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-33/25),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((51/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((51/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(2601/1600),(51/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((51/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(98397619047619/50000000000000),(385873015873/5000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/100000000000000)
theorem h9 : Model (fun x => f9 ((51/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-98397619047619/50000000000000),(-385873015873/5000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/100000000000000)
theorem h10 : Model (fun x => f10 ((51/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-164397619047619/50000000000000),(-3024603174603/25000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (3/100000000000000)
theorem h11 : Model (fun x => f11 ((51/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((51/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(132651/64000),(7803/64000),(153/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((51/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(25847293/1280000),(1520429/1280000),(1164544270833/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((51/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-25847293/1280000),(-1520429/1280000),(-1164544270833/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((51/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-1174057501860119/50000000000000),(-32720482080853/25000000000000),(-2404749917327/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/20000000000000)
theorem h16 : Model (fun x => f16 ((51/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((51/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(6765201/2560000),(132651/640000),(7803/1280000),(51/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((51/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(738265982142857/100000000000000),(28951607142857/50000000000000),(340607142857/20000000000000),(22261904761/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((51/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1609849021577381/100000000000000),(-36489357018849/50000000000000),(-350857101521/50000000000000),(1759775959/25000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((51/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((51/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(336938721679687/100000000000000),(8258302001953/25000000000000),(132651/10240000),(2601/10240000)⟩
def e22 : ℝ := (250000001/100000000000000)
theorem h22 : Model (fun x => f22 ((51/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(219509337568359/10000000000000),(26900654113769/12500000000000),(8439420898437/100000000000000),(33095768229/20000000000000)⟩
def e23 : ℝ := (814351857/50000000000000)
theorem h23 : Model (fun x => f23 ((51/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(585244354106209/100000000000000),(71113259436227/50000000000000),(1547541339079/20000000000000),(172517944981/100000000000000)⟩
def e24 : ℝ := (868915353/50000000000000)
theorem h24 : Model (fun x => f24 ((51/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((51/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(536996087677/125000000000),(3158800515747/6250000000000),(495498120117/20000000000000),(64770996093/100000000000000)⟩
def e26 : ℝ := (96000977/10000000000000)
theorem h26 : Model (fun x => f26 ((51/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(964660908402619/100000000000000),(283723796589/250000000000),(5563211697821/100000000000000),(72721721539/50000000000000)⟩
def e27 : ℝ := (13473153/625000000000)
theorem h27 : Model (fun x => f27 ((51/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(387476315627207/25000000000000),(127858018754027/50000000000000),(103913424947/781250000000),(317961388059/100000000000000)⟩
def e28 : ℝ := (1946767593/50000000000000)
theorem h28 : Model (fun x => f28 ((51/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((51/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(27386800471527/5000000000000),(37589726137389/50000000000000),(1105580180511/25000000000000),(144520285033/100000000000000)⟩
def e30 : ℝ := (573457521/20000000000000)
theorem h30 : Model (fun x => f30 ((51/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(16247328057513/12500000000000),(4460050839317/25000000000000),(1049423726897/100000000000000),(6858978607/20000000000000)⟩
def e31 : ℝ := (680411903/100000000000000)
theorem h31 : Model (fun x => f31 ((51/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(419970971742233/25000000000000),(136778120432661/50000000000000),(14350342120113/100000000000000),(176128140547/50000000000000)⟩
def e32 : ℝ := (4573947089/100000000000000)
theorem h32 : Model (fun x => f32 ((51/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((51/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1115829/320),(21879/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((51/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((51/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(112659/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((51/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(2918373/320),(39551/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((51/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((51/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(3647973/320),(39551/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((51/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-3647973/320),(-39551/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((51/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((51/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(91/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((51/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(8281/1600),(91/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((51/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((51/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(173901/160),(1911/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((51/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(92006371441/100000000000000),(-1011059027/50000000000000),(1041613/3125000000000),(-61047/12500000000000)⟩
def e46 : ℝ := (3461/50000000000000)
theorem h46 : Model (fun x => f46 ((51/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (85029/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-104886487138981/10000000000000),(61715043799/20000000000000),(-433588381/12500000000000),(4872507/12500000000000)⟩
def e47 : ℝ := (393309/250000000000)
theorem h47 : Model (fun x => f47 ((51/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((51/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(131/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((51/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((51/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((51/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(21833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((51/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(41833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((51/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((51/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(26145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((51/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((51/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(549062499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((51/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((51/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(1145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((51/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(50330729166651/50000000000000),(9552083333317/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (19/20000000000000)
theorem h60 : Model (fun x => f60 ((51/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(27344184027777/25000000000000),(54470486111/6250000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/10000000000000)
theorem h61 : Model (fun x => f61 ((51/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((51/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(26145833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((51/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(288802517361107/25000000000000),(1259548611109/25000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (1/2000000000000)
theorem h64 : Model (fun x => f64 ((51/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(313802517361107/25000000000000),(1259548611109/25000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (1/2000000000000)
theorem h65 : Model (fun x => f65 ((51/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1263512761049213/100000000000000),(62485115921477/50000000000000),(940628797737/100000000000000),(250334563/12500000000000)⟩
def e66 : ℝ := (158553/25000000000000)
theorem h66 : Model (fun x => f66 ((51/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(51145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((51/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(104635850694443/25000000000000),(426215277777/25000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (9/50000000000000)
theorem h68 : Model (fun x => f68 ((51/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(856270044849519/100000000000000),(5231792534713/100000000000000),(1331922743/12500000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (11/20000000000000)
theorem h69 : Model (fun x => f69 ((51/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(10819081285715491/100000000000000),(142023378319741/12500000000000),(920446124939/6250000000000),(79767521673/100000000000000)⟩
def e70 : ℝ := (109894863/50000000000000)
theorem h70 : Model (fun x => f70 ((51/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((51/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(574227864583317/3125000000000),(1143880208331/781250000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1250000000000)
theorem h72 : Model (fun x => f72 ((51/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(421100434027643/50000000000000),(41637239583263/50000000000000),(155859374999/25000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (207/25000000000000)
theorem h73 : Model (fun x => f73 ((51/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(1442302750124007/20000000000000),(37855831112481/5000000000000),(4892398132203/50000000000000),(51957153059/100000000000000)⟩
def e74 : ℝ := (136216689/100000000000000)
theorem h74 : Model (fun x => f74 ((51/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(9015297518167763/50000000000000),(473325912201887/25000000000000),(2451193426343/10000000000000),(32931168683/25000000000000)⟩
def e75 : ℝ := (71201283/20000000000000)
theorem h75 : Model (fun x => f75 ((51/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((51/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(191409288194439/3125000000000),(381293402777/781250000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1250000000000)
theorem h77 : Model (fun x => f77 ((51/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(52517361111/25000000000000),(9548611111/25000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((51/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(962818287/10000000000000),(525173611/20000000000000),(238715277/100000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((51/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(7371694519/1250000000000),(33107211887/20000000000000),(7956236513/50000000000000),(281068141/50000000000000)⟩
def e80 : ℝ := (3769799/100000000000000)
theorem h80 : Model (fun x => f80 ((51/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(1206500669609/100000000000000),(341116419767/100000000000000),(33244001313/100000000000000),(608169557/50000000000000)⟩
def e81 : ℝ := (402813/4000000000000)
theorem h81 : Model (fun x => f81 ((51/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(3606360307401027/20000000000000),(378728953045463/20000000000000),(24545178264743/100000000000000),(66470506923/50000000000000)⟩
def e82 : ℝ := (18303837/5000000000000)
theorem h82 : Model (fun x => f82 ((51/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(220645857/50000000000000),(80234857/50000000000000),(21882233/100000000000000),(265239/20000000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((51/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(2022587/10000000000000),(9193577/100000000000000),(1671559/100000000000000),(151959/100000000000000)⟩
def e84 : ℝ := (1759/25000000000000)
theorem h84 : Model (fun x => f84 ((51/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(927019/100000000000000),(252823/50000000000000),(114919/100000000000000),(13929/100000000000000)⟩
def e85 : ℝ := (247/25000000000000)
theorem h85 : Model (fun x => f85 ((51/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(5311/12500000000000),(13519/50000000000000),(7373/100000000000000),(1117/100000000000000)⟩
def e86 : ℝ := (11/10000000000000)
theorem h86 : Model (fun x => f86 ((51/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(15933/12500000000000),(40557/50000000000000),(22119/100000000000000),(3351/100000000000000)⟩
def e87 : ℝ := (33/10000000000000)
theorem h87 : Model (fun x => f87 ((51/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-15933/12500000000000),(-40557/50000000000000),(-22119/100000000000000),(-3351/100000000000000)⟩
def e88 : ℝ := (33/10000000000000)
theorem h88 : Model (fun x => f88 ((51/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(18031801536877671/100000000000000),(1893644765146201/100000000000000),(383518410041/1562500000000),(26588202099/20000000000000)⟩
def e89 : ℝ := (36607707/10000000000000)
theorem h89 : Model (fun x => f89 ((51/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(574227864583317/2500000000000),(1143880208331/625000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1000000000000)
theorem h90 : Model (fun x => f90 ((51/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(875892900043981/50000000000000),(7135583707067/50000000000000),(43598271121/100000000000000),(11839313/20000000000000)⟩
def e91 : ℝ := (30291/100000000000000)
theorem h91 : Model (fun x => f91 ((51/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(402369687676755147/100000000000000),(3242046882630561/50000000000000),(10630016360059/25000000000000),(145421143829/100000000000000)⟩
def e92 : ℝ := (17160007/6250000000000)
theorem h92 : Model (fun x => f92 ((51/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(12426383381/50000000000000),(-200248273/50000000000000),(1913807/50000000000000),(-14171/50000000000000)⟩
def e93 : ℝ := (221/100000000000000)
theorem h93 : Model (fun x => f93 ((51/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (49480366018793731/12500000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(2240700789473/50000000000000),(79681274889/20000000000000),(-396819109/50000000000000),(2107767/100000000000000)⟩
def e94 : ℝ := (53617/20000000000000)
theorem h94 : Model (fun x => f94 ((51/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(21833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((51/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(47808764940239/100000000000000),(-190473167093/100000000000000),(758857239/100000000000000),(-377917/12500000000000)⟩
def e96 : ℝ := (12097/100000000000000)
theorem h96 : Model (fun x => f96 ((51/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (208333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(652390438247/625000000000),(380946334183/100000000000000),(-18971431/1250000000000),(604667/10000000000000)⟩
def e97 : ℝ := (77009/100000000000000)
theorem h97 : Model (fun x => f97 ((51/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(13700199203187/625000000000),(7999873017843/100000000000000),(-398400051/1250000000000),(12698007/10000000000000)⟩
def e98 : ℝ := (1617189/100000000000000)
theorem h98 : Model (fun x => f98 ((51/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(27390438247/625000000000),(380946334183/100000000000000),(-18971431/1250000000000),(604667/10000000000000)⟩
def e99 : ℝ := (77009/100000000000000)
theorem h99 : Model (fun x => f99 ((51/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(96065141823101/100000000000000),(543816069191/6250000000000),(-419034319/10000000000000),(-52360333/50000000000000)⟩
def e100 : ℝ := (806587/25000000000000)
theorem h100 : Model (fun x => f100 ((51/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(27239250170631/25000000000000),(795282386899/100000000000000),(-214656829/12500000000000),(1059971/100000000000000)⟩
def e101 : ℝ := (28831/12500000000000)
theorem h101 : Model (fun x => f101 ((51/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(652390438247/62500000000),(380946334183/10000000000000),(-18971431/125000000000),(604667/1000000000000)⟩
def e102 : ℝ := (77009/10000000000000)
theorem h102 : Model (fun x => f102 ((51/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(288195425469431/25000000000000),(4604745728729/100000000000000),(-2111799929/12500000000000),(61526671/100000000000000)⟩
def e103 : ℝ := (500369/50000000000000)
theorem h103 : Model (fun x => f103 ((51/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(313195425469431/25000000000000),(4604745728729/100000000000000),(-2111799929/12500000000000),(61526671/100000000000000)⟩
def e104 : ℝ := (500369/50000000000000)
theorem h104 : Model (fun x => f104 ((51/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1203486518642693/100000000000000),(4537152272881/4000000000000),(165968036993/50000000000000),(-58315233/2000000000000)⟩
def e105 : ℝ := (42871153/100000000000000)
theorem h105 : Model (fun x => f105 ((51/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(1277390438247/625000000000),(380946334183/100000000000000),(-18971431/1250000000000),(604667/10000000000000)⟩
def e106 : ℝ := (77009/100000000000000)
theorem h106 : Model (fun x => f106 ((51/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(104430485230391/25000000000000),(311435011053/20000000000000),(-594085449/12500000000000),(13153311/100000000000000)⟩
def e107 : ℝ := (192333/50000000000000)
theorem h107 : Model (fun x => f107 ((51/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(426875210543347/50000000000000),(2386944631527/50000000000000),(-316296163/3125000000000),(10402683/100000000000000)⟩
def e108 : ℝ := (663717/50000000000000)
theorem h108 : Model (fun x => f108 ((51/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(2054954244126717/20000000000000),(1025852029572437/100000000000000),(4063530322849/50000000000000),(-31878973/156250000000)⟩
def e109 : ℝ := (546871623/100000000000000)
theorem h109 : Model (fun x => f109 ((51/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(572024253583251/3125000000000),(16700930124879/12500000000000),(-4507793409/1562500000000),(22259391/12500000000000)⟩
def e110 : ℝ := (605451/1562500000000)
theorem h110 : Model (fun x => f110 ((51/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(160440268734037/20000000000000),(15117335953691/20000000000000),(54628759577/25000000000000),(-2012171503/100000000000000)⟩
def e111 : ℝ := (14600859/50000000000000)
theorem h111 : Model (fun x => f111 ((51/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(6848797349547321/100000000000000),(683617800622181/100000000000000),(5392802823231/100000000000000),(-14314294837/100000000000000)⟩
def e112 : ℝ := (372901143/100000000000000)
theorem h112 : Model (fun x => f112 ((51/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(8561784285090453/50000000000000),(854734915097309/50000000000000),(13519863468929/100000000000000),(-34716837557/100000000000000)⟩
def e113 : ℝ := (459886383/50000000000000)
theorem h113 : Model (fun x => f113 ((51/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(190674751194417/3125000000000),(5566976708293/12500000000000),(-1502597803/1562500000000),(7419797/12500000000000)⟩
def e114 : ℝ := (201817/1562500000000)
theorem h114 : Model (fun x => f114 ((51/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(48015110871/25000000000000),(33389718533/100000000000000),(164771791/12500000000000),(-11033369/100000000000000)⟩
def e115 : ℝ := (7663/10000000000000)
theorem h115 : Model (fun x => f115 ((51/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(8416991547/100000000000000),(274367707/12500000000000),(7282023/4000000000000),(808571/20000000000000)⟩
def e116 : ℝ := (32047/50000000000000)
theorem h116 : Model (fun x => f116 ((51/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(513570486089/100000000000000),(137674960997/100000000000000),(12077424209/100000000000000),(162825213/50000000000000)⟩
def e117 : ℝ := (5571291/100000000000000)
theorem h117 : Model (fun x => f117 ((51/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(1049648045273/100000000000000),(283339913961/100000000000000),(6300202777/25000000000000),(70952243/10000000000000)⟩
def e118 : ℝ := (6239187/50000000000000)
theorem h118 : Model (fun x => f118 ((51/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(17124618218226179/100000000000000),(1709753170108579/100000000000000),(13545064280037/100000000000000),(-34007315127/100000000000000)⟩
def e119 : ℝ := (46612557/5000000000000)
theorem h119 : Model (fun x => f119 ((51/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(368872139/100000000000000),(64128441/50000000000000),(3242423/20000000000000),(837887/100000000000000)⟩
def e120 : ℝ := (993/6250000000000)
theorem h120 : Model (fun x => f120 ((51/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(16165711/100000000000000),(878253/12500000000000),(596741/50000000000000),(19311/20000000000000)⟩
def e121 : ℝ := (149/4000000000000)
theorem h121 : Model (fun x => f121 ((51/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(708457/100000000000000),(46187/12500000000000),(9853/12500000000000),(271/3125000000000)⟩
def e122 : ℝ := (53/10000000000000)
theorem h122 : Model (fun x => f122 ((51/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(31047/100000000000000),(18891/100000000000000),(4851/100000000000000),(337/50000000000000)⟩
def e123 : ℝ := (61/100000000000000)
theorem h123 : Model (fun x => f123 ((51/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(93141/100000000000000),(56673/100000000000000),(14553/100000000000000),(1011/50000000000000)⟩
def e124 : ℝ := (183/100000000000000)
theorem h124 : Model (fun x => f124 ((51/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-93141/100000000000000),(-56673/100000000000000),(-14553/100000000000000),(-1011/50000000000000)⟩
def e125 : ℝ := (183/100000000000000)
theorem h125 : Model (fun x => f125 ((51/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(8562309109066519/50000000000000),(854876585025953/50000000000000),(3386266066371/25000000000000),(-34007317149/100000000000000)⟩
def e126 : ℝ := (932251323/100000000000000)
theorem h126 : Model (fun x => f126 ((51/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(572024253583251/2500000000000),(16700930124879/10000000000000),(-4507793409/1250000000000),(22259391/10000000000000)⟩
def e127 : ℝ := (605451/1250000000000)
theorem h127 : Model (fun x => f127 ((51/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(436229049818197/25000000000000),(6504661864401/50000000000000),(-3091612553/20000000000000),(-19063337/50000000000000)⟩
def e128 : ℝ := (772389/20000000000000)
theorem h128 : Model (fun x => f128 ((51/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(199626877290867963/50000000000000),(5890831830018763/100000000000000),(11897248536797/100000000000000),(-1939268833/2500000000000)⟩
def e129 : ℝ := (1762723391/100000000000000)
theorem h129 : Model (fun x => f129 ((51/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(12523363757/50000000000000),(-92388649/25000000000000),(147071/3125000000000),(-53561/100000000000000)⟩
def e130 : ℝ := (141/20000000000000)
theorem h130 : Model (fun x => f130 ((51/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (78670189233940731/20000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(1072289115727/25000000000000),(45619050499/12500000000000),(-211994497/10000000000000),(1271939/10000000000000)⟩
def e131 : ℝ := (531359/100000000000000)
theorem h131 : Model (fun x => f131 ((51/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(4385279020927/50000000000000),(763358778437/100000000000000),(-728395797/25000000000000),(14827157/100000000000000)⟩
def e132 : ℝ := (199861/25000000000000)
theorem h132 : Model (fun x => f132 ((51/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-91991302325861/100000000000000),(-1994884575253/25000000000000),(16305430807/50000000000000),(-187567349/100000000000000)⟩
def e133 : ℝ := (953493/4000000000000)
theorem h133 : Model (fun x => f133 ((51/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(78431372549019/100000000000000),(-1537870049981/100000000000000),(6030862941/20000000000000),(-591261073/100000000000000)⟩
def e134 : ℝ := (1478153/12500000000000)
theorem h134 : Model (fun x => f134 ((51/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (5/4))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-72150041039891/100000000000000),(-2421877362751/50000000000000),(120552729217/100000000000000),(-2510890651/100000000000000)⟩
def e135 : ℝ := (91044029/100000000000000)
theorem h135 : Model (fun x => f135 ((51/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(6765201/256000),(132651/64000),(7803/128000),(51/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((51/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((51/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(1193859/32000),(70227/32000),(1377/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((51/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(16316073/256000),(54621/12800),(13311/128000),(69/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((51/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-2601/1600),(-51/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((51/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(15899913/256000),(10761/2560),(13231/128000),(69/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((51/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((51/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(153/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((51/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-153/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((51/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(13941513/256000),(10377/2560),(13231/128000),(69/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((51/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(14709513/256000),(10377/2560),(13231/128000),(69/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((51/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((51/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(14709513/4000),(10377/40),(13231/2000),(69/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((51/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((51/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(1278622989/512000),(25071039/128000),(1474767/256000),(9639/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((51/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(2502692371/6250000000000),(-785158391/25000000000000),(1231621/800000000000),(-3018679/50000000000000)⟩
def e151 : ℝ := (249077/100000000000000)
theorem h151 : Model (fun x => f151 ((51/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (587675277/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(147253543864901/100000000000000),(-1161122065927/100000000000000),(325763089/2000000000000),(-138189111/50000000000000)⟩
def e152 : ℝ := (1787273801/100000000000000)
theorem h152 : Model (fun x => f152 ((51/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(171/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((51/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(22401/1600),(151/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((51/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(273/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((51/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(7326007326007/100000000000000),(-20126393753/25000000000000),(110584581/12500000000000),(-4860861/50000000000000)⟩
def e156 : ℝ := (54011/50000000000000)
theorem h156 : Model (fun x => f156 ((51/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (27/2))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(25642170329669/25000000000000),(255655516631/100000000000000),(176935329/10000000000000),(-4860863/25000000000000)⟩
def e157 : ℝ := (2820963/100000000000000)
theorem h157 : Model (fun x => f157 ((51/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(50642170329669/25000000000000),(255655516631/100000000000000),(176935329/10000000000000),(-4860863/25000000000000)⟩
def e158 : ℝ := (2820963/100000000000000)
theorem h158 : Model (fun x => f158 ((51/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(50642170329669/50000000000000),(25565551663/20000000000000),(176935329/20000000000000),(-4860863/50000000000000)⟩
def e159 : ℝ := (705241/50000000000000)
theorem h159 : Model (fun x => f159 ((51/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(642170329669/50000000000000),(25565551663/20000000000000),(176935329/20000000000000),(-4860863/50000000000000)⟩
def e160 : ℝ := (705241/50000000000000)
theorem h160 : Model (fun x => f160 ((51/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((51/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((51/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(186893723835683/50000000000000),(471745298543/100000000000000),(1632439047/50000000000000),(-35877799/100000000000000)⟩
def e163 : ℝ := (5205353/100000000000000)
theorem h163 : Model (fun x => f163 ((51/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(2729501733385651/100000000000000),(471745298543/100000000000000),(1632439047/50000000000000),(-35877799/100000000000000)⟩
def e164 : ℝ := (2602677/50000000000000)
theorem h164 : Model (fun x => f164 ((51/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((51/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1382278916972429/50000000000000),(30991132767/781250000000),(28057096051/100000000000000),(-293346431/100000000000000)⟩
def e166 : ℝ := (2192411/5000000000000)
theorem h166 : Model (fun x => f166 ((51/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(804693878632581/10000000000000),(30991132767/781250000000),(28057096051/100000000000000),(-293346431/100000000000000)⟩
def e167 : ℝ := (43848221/100000000000000)
theorem h167 : Model (fun x => f167 ((51/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((51/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(1018786111623829/12500000000000),(14304034517737/100000000000000),(5233879371/5000000000000),(-504228327/50000000000000)⟩
def e169 : ℝ := (31708513/20000000000000)
theorem h169 : Model (fun x => f169 ((51/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13419336512038251/100000000000000),(14304034517737/100000000000000),(5233879371/5000000000000),(-504228327/50000000000000)⟩
def e170 : ℝ := (79271283/50000000000000)
theorem h170 : Model (fun x => f170 ((51/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((51/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(3397921626768937/25000000000000),(15820692046529/50000000000000),(48604853389/20000000000000),(-1032824167/50000000000000)⟩
def e172 : ℝ := (352036273/100000000000000)
theorem h172 : Model (fun x => f172 ((51/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(15927400792790033/100000000000000),(15820692046529/50000000000000),(48604853389/20000000000000),(-1032824167/50000000000000)⟩
def e173 : ℝ := (176018137/50000000000000)
theorem h173 : Model (fun x => f173 ((51/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((51/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(8065981438573779/50000000000000),(52407406645411/100000000000000),(106874498343/25000000000000),(-381252519/12500000000000)⟩
def e175 : ℝ := (146430583/25000000000000)
theorem h175 : Model (fun x => f175 ((51/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(1653434382952851/10000000000000),(52407406645411/100000000000000),(106874498343/25000000000000),(-381252519/12500000000000)⟩
def e176 : ℝ := (585722333/100000000000000)
theorem h176 : Model (fun x => f176 ((51/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((51/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(32708400644699/195312500000),(74215977346843/100000000000000),(80781901911/12500000000000),(-230407451/6250000000000)⟩
def e178 : ℝ := (833238723/100000000000000)
theorem h178 : Model (fun x => f178 ((51/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(418227052061671/2500000000000),(74215977346843/100000000000000),(80781901911/12500000000000),(-230407451/6250000000000)⟩
def e179 : ℝ := (208309681/25000000000000)
theorem h179 : Model (fun x => f179 ((51/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((51/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(16943940485585989/100000000000000),(96553573932327/100000000000000),(897422236041/100000000000000),(-3877557231/100000000000000)⟩
def e181 : ℝ := (544167793/50000000000000)
theorem h181 : Model (fun x => f181 ((51/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(8473636909459661/50000000000000),(96553573932327/100000000000000),(897422236041/100000000000000),(-3877557231/100000000000000)⟩
def e182 : ℝ := (1088335587/100000000000000)
theorem h182 : Model (fun x => f182 ((51/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(54415182076431/25000000000000),(11451698513143/50000000000000),(142438400617/50000000000000),(75993269/25000000000000)⟩
def e183 : ℝ := (131158811/50000000000000)
theorem h183 : Model (fun x => f183 ((51/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(400723346203/390625000000),(258939004377/100000000000000),(1955477171/100000000000000),(-2178931/12500000000000)⟩
def e184 : ℝ := (2878029/100000000000000)
theorem h184 : Model (fun x => f184 ((51/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(100642170329669/50000000000000),(25565551663/20000000000000),(176935329/20000000000000),(-4860863/50000000000000)⟩
def e185 : ℝ := (705241/50000000000000)
theorem h185 : Model (fun x => f185 ((51/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(101288464486661/25000000000000),(514594521007/100000000000000),(3724830461/100000000000000),(-368749/1000000000000)⟩
def e186 : ℝ := (5698993/100000000000000)
theorem h186 : Model (fun x => f186 ((51/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(815511271623773/100000000000000),(1553697283017/100000000000000),(1467449579/12500000000000),(-104297483/100000000000000)⟩
def e187 : ℝ := (4316339/25000000000000)
theorem h187 : Model (fun x => f187 ((51/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(820748243045247/50000000000000),(833959821857/20000000000000),(16415331921/50000000000000),(-260464613/100000000000000)⟩
def e188 : ℝ := (46481991/100000000000000)
theorem h188 : Model (fun x => f188 ((51/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1683932069597821/100000000000000),(8528070439257/100000000000000),(19143929959/25000000000000),(-193391913/50000000000000)⟩
def e189 : ℝ := (19187757/20000000000000)
theorem h189 : Model (fun x => f189 ((51/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((51/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(50642170329669/6250000000000),(25565551663/2500000000000),(176935329/2500000000000),(-4860863/6250000000000)⟩
def e191 : ℝ := (705241/6250000000000)
theorem h191 : Model (fun x => f191 ((51/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(57053743868917/6250000000000),(1281561070897/100000000000000),(9032890331/100000000000000),(-11900657/12500000000000)⟩
def e192 : ℝ := (2832377/20000000000000)
theorem h192 : Model (fun x => f192 ((51/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(63303743868917/6250000000000),(1281561070897/100000000000000),(9032890331/100000000000000),(-11900657/12500000000000)⟩
def e193 : ℝ := (2832377/20000000000000)
theorem h193 : Model (fun x => f193 ((51/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(4263968177059031/25000000000000),(21591604749913/20000000000000),(207400985751/20000000000000),(-1884537127/50000000000000)⟩
def e194 : ℝ := (1218926181/100000000000000)
theorem h194 : Model (fun x => f194 ((51/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(293154157839/50000000000000),(-3711137399/100000000000000),(-6078773/50000000000000),(108039/25000000000000)⟩
def e195 : ℝ := (22653/50000000000000)
theorem h195 : Model (fun x => f195 ((51/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (16946872691557369/100000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(1276162950021/100000000000000),(63103416323/50000000000000),(793817639/100000000000000),(-664613/6250000000000)⟩
def e196 : ℝ := (1711139/100000000000000)
theorem h196 : Model (fun x => f196 ((51/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(25642170329669/12500000000000),(255655516631/50000000000000),(176935329/5000000000000),(-4860863/12500000000000)⟩
def e197 : ℝ := (2820963/50000000000000)
theorem h197 : Model (fun x => f197 ((51/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(49365972740219/100000000000000),(-31151615301/50000000000000),(-352560333/100000000000000),(1145503/20000000000000)⟩
def e198 : ℝ := (349723/50000000000000)
theorem h198 : Model (fun x => f198 ((51/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (10115561709217/5000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(101268054519559/100000000000000),(124606461203/100000000000000),(88140083/12500000000000),(-5727517/50000000000000)⟩
def e199 : ℝ := (853707/20000000000000)
theorem h199 : Model (fun x => f199 ((51/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1268054519559/100000000000000),(124606461203/100000000000000),(88140083/12500000000000),(-5727517/50000000000000)⟩
def e200 : ℝ := (853707/20000000000000)
theorem h200 : Model (fun x => f200 ((51/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(373727344060277/100000000000000),(459857178249/100000000000000),(2602231021/100000000000000),(-42274531/100000000000000)⟩
def e201 : ℝ := (15752929/100000000000000)
theorem h201 : Model (fun x => f201 ((51/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1364720814887281/50000000000000),(459857178249/100000000000000),(2602231021/100000000000000),(-42274531/100000000000000)⟩
def e202 : ℝ := (1575293/10000000000000)
theorem h202 : Model (fun x => f202 ((51/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2764052437719643/100000000000000),(966687260861/25000000000000),(5613524357/25000000000000),(-174491983/50000000000000)⟩
def e203 : ℝ := (2651739/2000000000000)
theorem h203 : Model (fun x => f203 ((51/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(1609286678020119/20000000000000),(966687260861/25000000000000),(5613524357/25000000000000),(-174491983/50000000000000)⟩
def e204 : ℝ := (132586951/100000000000000)
theorem h204 : Model (fun x => f204 ((51/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(814846655236707/10000000000000),(1394215742991/10000000000000),(2107352783/2500000000000),(-1219886451/100000000000000)⟩
def e205 : ℝ := (239394893/50000000000000)
theorem h205 : Model (fun x => f205 ((51/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13417514171414689/100000000000000),(1394215742991/10000000000000),(2107352783/2500000000000),(-1219886451/100000000000000)⟩
def e206 : ℝ := (478789787/100000000000000)
theorem h206 : Model (fun x => f206 ((51/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(6793827783138891/50000000000000),(15419020588867/50000000000000),(98672750307/50000000000000),(-513798229/20000000000000)⟩
def e207 : ℝ := (1061332383/100000000000000)
theorem h207 : Model (fun x => f207 ((51/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(15923369851992067/100000000000000),(15419020588867/50000000000000),(98672750307/50000000000000),(-513798229/20000000000000)⟩
def e208 : ℝ := (33166637/3125000000000)
theorem h208 : Model (fun x => f208 ((51/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(16125286863066347/100000000000000),(6383829003683/12500000000000),(350553112201/100000000000000),(-3962244139/100000000000000)⟩
def e209 : ℝ := (110157713/6250000000000)
theorem h209 : Model (fun x => f209 ((51/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16527667815447299/100000000000000),(6383829003683/12500000000000),(350553112201/100000000000000),(-3962244139/100000000000000)⟩
def e210 : ℝ := (1762523409/100000000000000)
theorem h210 : Model (fun x => f210 ((51/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(2092155956769847/12500000000000),(72312777471297/100000000000000),(535175625113/100000000000000),(-1277204029/25000000000000)⟩
def e211 : ℝ := (100126023/4000000000000)
theorem h211 : Model (fun x => f211 ((51/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(1044976787908733/6250000000000),(72312777471297/100000000000000),(535175625113/100000000000000),(-1277204029/25000000000000)⟩
def e212 : ℝ := (156446911/6250000000000)
theorem h212 : Model (fun x => f212 ((51/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(8465821306369217/50000000000000),(47031740223567/50000000000000),(187490473267/25000000000000),(-5912082087/100000000000000)⟩
def e213 : ℝ := (3265795627/100000000000000)
theorem h213 : Model (fun x => f213 ((51/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(16934975946071767/100000000000000),(47031740223567/50000000000000),(187490473267/25000000000000),(-5912082087/100000000000000)⟩
def e214 : ℝ := (816448907/25000000000000)
theorem h214 : Model (fun x => f214 ((51/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(26843090983799/12500000000000),(22294850447043/100000000000000),(61532778697/25000000000000),(-6517401/1562500000000)⟩
def e215 : ℝ := (157081951/20000000000000)
theorem h215 : Model (fun x => f215 ((51/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(102552188661763/100000000000000),(252373078131/100000000000000),(791695829/50000000000000),(-21443329/100000000000000)⟩
def e216 : ℝ := (4339883/50000000000000)
theorem h216 : Model (fun x => f216 ((51/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(201268054519559/100000000000000),(124606461203/100000000000000),(88140083/12500000000000),(-5727517/50000000000000)⟩
def e217 : ℝ := (853707/20000000000000)
theorem h217 : Model (fun x => f217 ((51/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(405088297700881/100000000000000),(501586000537/100000000000000),(1496816493/50000000000000),(-44353397/100000000000000)⟩
def e218 : ℝ := (4304209/25000000000000)
theorem h218 : Model (fun x => f218 ((51/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(407656667934481/50000000000000),(302859715507/20000000000000),(950659673/10000000000000),(-5136207/4000000000000)⟩
def e219 : ℝ := (26039361/50000000000000)
theorem h219 : Model (fun x => f219 ((51/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(1640965289341977/100000000000000),(1015933095541/25000000000000),(13384799483/50000000000000),(-20581847/6250000000000)⟩
def e220 : ℝ := (4375579/3125000000000)
theorem h220 : Model (fun x => f220 ((51/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1682845819400029/100000000000000),(8308801111039/100000000000000),(63691483637/100000000000000),(-557687679/100000000000000)⟩
def e221 : ℝ := (72006091/25000000000000)
theorem h221 : Model (fun x => f221 ((51/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(101268054519559/12500000000000),(124606461203/12500000000000),(88140083/1562500000000),(-5727517/6250000000000)⟩
def e222 : ℝ := (853707/2500000000000)
theorem h222 : Model (fun x => f222 ((51/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(182539324963647/20000000000000),(249844953551/20000000000000),(722435697/10000000000000),(-113083601/100000000000000)⟩
def e223 : ℝ := (21414023/50000000000000)
theorem h223 : Model (fun x => f223 ((51/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(202539324963647/20000000000000),(249844953551/20000000000000),(722435697/10000000000000),(-113083601/100000000000000)⟩
def e224 : ℝ := (21414023/50000000000000)
theorem h224 : Model (fun x => f224 ((51/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(1065132675872429/6250000000000),(52582737596713/50000000000000),(870371895719/100000000000000),(-3077399857/50000000000000)⟩
def e225 : ℝ := (457077831/12500000000000)
theorem h225 : Model (fun x => f225 ((51/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(586781359879/100000000000000),(-3620977341/100000000000000),(-7623241/100000000000000),(443889/100000000000000)⟩
def e226 : ℝ := (65591/50000000000000)
theorem h226 : Model (fun x => f226 ((51/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (16936077155447357/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(630041017233/50000000000000),(61523084349/50000000000000),(620589511/100000000000000),(-605313/5000000000000)⟩
def e227 : ℝ := (5044853/100000000000000)
theorem h227 : Model (fun x => f227 ((51/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(2536244984487/100000000000000),(1947289073/781250000000),(28288143/2000000000000),(-5685017/25000000000000)⟩
def e228 : ℝ := (844499/12500000000000)
theorem h228 : Model (fun x => f228 ((51/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(233419413797/6250000000000),(337584977507/100000000000000),(-199129723/50000000000000),(-3263893/20000000000000)⟩
def e229 : ℝ := (7505053/12500000000000)
theorem h229 : Model (fun x => f229 ((51/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(2929184800589/100000000000000),(25917191911/12500000000000),(-4377802219/100000000000000),(36519839/50000000000000)⟩
def e230 : ℝ := (50381741/100000000000000)
theorem h230 : Model (fun x => f230 ((51/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-34610428119651/50000000000000),(-2318208595107/50000000000000),(58087463499/50000000000000),(-2437850973/100000000000000)⟩
def e231 : ℝ := (14142577/10000000000000)
theorem h231 : Model (fun x => f231 ((51/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((51/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2601/320),(-51/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((51/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1071/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((51/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(5967/320),(33/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((51/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((51/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(14287/320),(33/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((51/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((51/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(357175/32),(825/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((51/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(9639/1600),(69/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((51/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(19239/1600),(69/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((51/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((51/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3636171/1600),(13041/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((51/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(44002331023/100000000000000),(-7890641/2500000000000),(2275551/50000000000000),(-49051/100000000000000)⟩
def e244 : ℝ := (299/50000000000000)
theorem h244 : Model (fun x => f244 ((51/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (36099/16))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(785826629157/160000000000),(-313513607649/25000000000000),(286821/195312500000),(-66244739/100000000000000)⟩
def e245 : ℝ := (6414537/50000000000000)
theorem h245 : Model (fun x => f245 ((51/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(459/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((51/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(39321/1600),(411/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((51/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(72921/1600),(411/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((51/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(17161/1600),(131/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((51/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1251397281/2560000),(8302911/640000),(152723/1280000),(271/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((51/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((51/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(74529/160),(819/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((51/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(107340766681/50000000000000),(-4718275459/100000000000000),(77773771/100000000000000),(-1139543/100000000000000)⟩
def e253 : ℝ := (323/2000000000000)
theorem h253 : Model (fun x => f253 ((51/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (36441/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(52471071705101/50000000000000),(478706866793/100000000000000),(2421022017/100000000000000),(-5028301/25000000000000)⟩
def e254 : ℝ := (15797221/100000000000000)
theorem h254 : Model (fun x => f254 ((51/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(102471071705101/50000000000000),(478706866793/100000000000000),(2421022017/100000000000000),(-5028301/25000000000000)⟩
def e255 : ℝ := (15797221/100000000000000)
theorem h255 : Model (fun x => f255 ((51/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(102471071705101/100000000000000),(59838358349/25000000000000),(37828469/3125000000000),(-5028301/50000000000000)⟩
def e256 : ℝ := (1974653/25000000000000)
theorem h256 : Model (fun x => f256 ((51/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(2471071705101/100000000000000),(59838358349/25000000000000),(37828469/3125000000000),(-5028301/50000000000000)⟩
def e257 : ℝ := (1974653/25000000000000)
theorem h257 : Model (fun x => f257 ((51/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(378167050340253/100000000000000),(55208009191/6250000000000),(4467362053/100000000000000),(-37113651/100000000000000)⟩
def e258 : ℝ := (14574821/50000000000000)
theorem h258 : Model (fun x => f258 ((51/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1366940668027269/50000000000000),(55208009191/6250000000000),(4467362053/100000000000000),(-37113651/100000000000000)⟩
def e259 : ℝ := (29149643/100000000000000)
theorem h259 : Model (fun x => f259 ((51/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1400718752100409/50000000000000),(372439733089/5000000000000),(39785964539/100000000000000),(-291580753/100000000000000)⟩
def e260 : ℝ := (246073379/100000000000000)
theorem h260 : Model (fun x => f260 ((51/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(808381845658177/10000000000000),(372439733089/5000000000000),(39785964539/100000000000000),(-291580753/100000000000000)⟩
def e261 : ℝ := (12303669/5000000000000)
theorem h261 : Model (fun x => f261 ((51/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4141787703577047/50000000000000),(13490878372183/50000000000000),(2444586911/1562500000000),(-46317291/5000000000000)⟩
def e262 : ℝ := (446409981/50000000000000)
theorem h262 : Model (fun x => f262 ((51/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(13552623026201713/100000000000000),(13490878372183/50000000000000),(2444586911/1562500000000),(-46317291/5000000000000)⟩
def e263 : ℝ := (892819963/100000000000000)
theorem h263 : Model (fun x => f263 ((51/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(6943759029550593/50000000000000),(12017432765849/20000000000000),(48619674597/12500000000000),(-80553787/5000000000000)⟩
def e264 : ℝ := (498176679/25000000000000)
theorem h264 : Model (fun x => f264 ((51/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(16223232344815471/100000000000000),(12017432765849/20000000000000),(48619674597/12500000000000),(-80553787/5000000000000)⟩
def e265 : ℝ := (1992706717/100000000000000)
theorem h265 : Model (fun x => f265 ((51/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(16624120048940999/100000000000000),(100402824358153/100000000000000),(147754703199/20000000000000),(-162404787/10000000000000)⟩
def e266 : ℝ := (1669089201/50000000000000)
theorem h266 : Model (fun x => f266 ((51/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(17026501001321951/100000000000000),(100402824358153/100000000000000),(147754703199/20000000000000),(-162404787/10000000000000)⟩
def e267 : ℝ := (3338178403/100000000000000)
theorem h267 : Model (fun x => f267 ((51/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(4361809512483589/25000000000000),(143637364875857/100000000000000),(1203454415539/100000000000000),(-392799681/100000000000000)⟩
def e268 : ℝ := (598334989/12500000000000)
theorem h268 : Model (fun x => f268 ((51/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(4357404750578827/25000000000000),(143637364875857/100000000000000),(1203454415539/100000000000000),(-392799681/100000000000000)⟩
def e269 : ℝ := (4786679913/100000000000000)
theorem h269 : Model (fun x => f269 ((51/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(4465079346447107/25000000000000),(9445256933357/5000000000000),(178798105823/10000000000000),(61598053/2500000000000)⟩
def e270 : ℝ := (788194951/12500000000000)
theorem h270 : Model (fun x => f270 ((51/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(17863650719121761/100000000000000),(9445256933357/5000000000000),(178798105823/10000000000000),(61598053/2500000000000)⟩
def e271 : ℝ := (6305559609/100000000000000)
theorem h271 : Model (fun x => f271 ((51/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(441423618418289/100000000000000),(11856310689293/25000000000000),(712574687669/100000000000000),(75480009/1562500000000)⟩
def e272 : ℝ := (401430421/25000000000000)
theorem h272 : Model (fun x => f272 ((51/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(105003205363919/100000000000000),(490536056727/100000000000000),(1526873933/50000000000000),(-14815417/100000000000000)⟩
def e273 : ℝ := (650373/4000000000000)
theorem h273 : Model (fun x => f273 ((51/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(202471071705101/100000000000000),(59838358349/25000000000000),(37828469/3125000000000),(-5028301/50000000000000)⟩
def e274 : ℝ := (1974653/25000000000000)
theorem h274 : Model (fun x => f274 ((51/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(409945348774121/100000000000000),(969242923519/100000000000000),(2737384941/50000000000000),(-34928621/100000000000000)⟩
def e275 : ℝ := (32056549/100000000000000)
theorem h275 : Model (fun x => f275 ((51/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(51876296316761/6250000000000),(735913700503/25000000000000),(9183587521/50000000000000),(-21777521/25000000000000)⟩
def e276 : ℝ := (12194391/12500000000000)
theorem h276 : Model (fun x => f276 ((51/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1680551889815357/100000000000000),(7946732566577/100000000000000),(26504613/48828125000),(-90124437/50000000000000)⟩
def e277 : ℝ := (131917403/50000000000000)
theorem h277 : Model (fun x => f277 ((51/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1764633352110041/100000000000000),(3317607377631/20000000000000),(36824666439/25000000000000),(35347691/50000000000000)⟩
def e278 : ℝ := (138325541/25000000000000)
theorem h278 : Model (fun x => f278 ((51/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(102471071705101/12500000000000),(59838358349/3125000000000),(37828469/390625000000),(-5028301/6250000000000)⟩
def e279 : ℝ := (1974653/3125000000000)
theorem h279 : Model (fun x => f279 ((51/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(924771779004727/100000000000000),(481072704779/20000000000000),(1273783593/10000000000000),(-95268233/100000000000000)⟩
def e280 : ℝ := (79448221/100000000000000)
theorem h280 : Model (fun x => f280 ((51/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1024771779004727/100000000000000),(481072704779/20000000000000),(1273783593/10000000000000),(-95268233/100000000000000)⟩
def e281 : ℝ := (79448221/100000000000000)
theorem h281 : Model (fun x => f281 ((51/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(3616692919065763/20000000000000),(106217683851423/50000000000000),(2133253847313/100000000000000),(469935661/10000000000000)⟩
def e282 : ℝ := (7103521999/100000000000000)
theorem h282 : Model (fun x => f282 ((51/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(552991377691/100000000000000),(-3248131077/50000000000000),(11080003/100000000000000),(123119/25000000000000)⟩
def e283 : ℝ := (45591/20000000000000)
theorem h283 : Model (fun x => f283 ((51/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (17868884170900047/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(152564659309/6250000000000),(116790733917/50000000000000),(181703647/20000000000000),(-3037157/25000000000000)⟩
def e284 : ℝ := (1010537/10000000000000)
theorem h284 : Model (fun x => f284 ((51/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(52471071705101/25000000000000),(478706866793/50000000000000),(2421022017/50000000000000),(-5028301/12500000000000)⟩
def e285 : ℝ := (15797221/50000000000000)
theorem h285 : Model (fun x => f285 ((51/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(2439712943761/5000000000000),(-113974346101/100000000000000),(-310193267/100000000000000),(6859667/100000000000000)⟩
def e286 : ℝ := (950631/25000000000000)
theorem h286 : Model (fun x => f286 ((51/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (204460979610967/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(102411482249557/100000000000000),(1139743461/500000000000),(155096633/25000000000000),(-1714917/12500000000000)⟩
def e287 : ℝ := (11783421/50000000000000)
theorem h287 : Model (fun x => f287 ((51/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(2411482249557/100000000000000),(1139743461/500000000000),(155096633/25000000000000),(-1714917/12500000000000)⟩
def e288 : ℝ := (11783421/50000000000000)
theorem h288 : Model (fun x => f288 ((51/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(75589427374673/20000000000000),(420619610607/50000000000000),(91580869/4000000000000),(-50630883/100000000000000)⟩
def e289 : ℝ := (86972871/100000000000000)
theorem h289 : Model (fun x => f289 ((51/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(54673228451753/2000000000000),(420619610607/50000000000000),(91580869/4000000000000),(-50630883/100000000000000)⟩
def e290 : ℝ := (10871609/12500000000000)
theorem h290 : Model (fun x => f290 ((51/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1399791591278169/50000000000000),(3546435508837/50000000000000),(10610797117/50000000000000),(-104113541/25000000000000)⟩
def e291 : ℝ := (183480691/25000000000000)
theorem h291 : Model (fun x => f291 ((51/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(808196413493729/10000000000000),(3546435508837/50000000000000),(10610797117/50000000000000),(-104113541/25000000000000)⟩
def e292 : ℝ := (146784553/20000000000000)
theorem h292 : Model (fun x => f292 ((51/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(1655371853093373/20000000000000),(25686645892911/100000000000000),(1760817459/2000000000000),(-288582227/20000000000000)⟩
def e293 : ℝ := (332679457/12500000000000)
theorem h293 : Model (fun x => f293 ((51/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(3386476721128621/25000000000000),(25686645892911/100000000000000),(1760817459/2000000000000),(-288582227/20000000000000)⟩
def e294 : ℝ := (2661435657/100000000000000)
theorem h294 : Model (fun x => f294 ((51/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(1387256402457607/10000000000000),(11436758477801/20000000000000),(46550663661/20000000000000),(-2976070651/100000000000000)⟩
def e295 : ℝ := (5936405181/100000000000000)
theorem h295 : Model (fun x => f295 ((51/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(3241655662058071/20000000000000),(11436758477801/20000000000000),(46550663661/20000000000000),(-2976070651/100000000000000)⟩
def e296 : ℝ := (2968202591/50000000000000)
theorem h296 : Model (fun x => f296 ((51/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(4149784516175451/25000000000000),(23877331957133/25000000000000),(117317451467/25000000000000),(-4386187537/100000000000000)⟩
def e297 : ℝ := (4969839417/50000000000000)
theorem h297 : Model (fun x => f297 ((51/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(4250379754270689/25000000000000),(23877331957133/25000000000000),(117317451467/25000000000000),(-4386187537/100000000000000)⟩
def e298 : ℝ := (1987935767/20000000000000)
theorem h298 : Model (fun x => f298 ((51/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(4352876907583691/25000000000000),(68283629284681/50000000000000),(80377356187/10000000000000),(-2581116899/50000000000000)⟩
def e299 : ℝ := (14251718859/100000000000000)
theorem h299 : Model (fun x => f299 ((51/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(4348472145678929/25000000000000),(68283629284681/50000000000000),(80377356187/10000000000000),(-2581116899/50000000000000)⟩
def e300 : ℝ := (712585943/5000000000000)
theorem h300 : Model (fun x => f300 ((51/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(17813339118395627/100000000000000),(89754847657747/50000000000000),(1242369040681/100000000000000),(-4993609967/100000000000000)⟩
def e301 : ℝ := (18785202209/100000000000000)
theorem h301 : Model (fun x => f301 ((51/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(55677101411653/312500000000),(89754847657747/50000000000000),(1242369040681/100000000000000),(-4993609967/100000000000000)⟩
def e302 : ℝ := (1878520221/10000000000000)
theorem h302 : Model (fun x => f302 ((51/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(85929178727031/20000000000000),(1123542907151/2500000000000),(274840874037/50000000000000),(690434389/50000000000000)⟩
def e303 : ℝ := (4765876791/100000000000000)
theorem h303 : Model (fun x => f303 ((51/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(104881116965513/100000000000000),(466891268901/100000000000000),(447575037/25000000000000),(-1010881/4000000000000)⟩
def e304 : ℝ := (48436921/100000000000000)
theorem h304 : Model (fun x => f304 ((51/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(202411482249557/100000000000000),(1139743461/500000000000),(155096633/25000000000000),(-1714917/12500000000000)⟩
def e305 : ℝ := (11783421/50000000000000)
theorem h305 : Model (fun x => f305 ((51/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(409704081464627/100000000000000),(922788653301/100000000000000),(757768303/25000000000000),(-52710697/100000000000000)⟩
def e306 : ℝ := (19114121/20000000000000)
theorem h306 : Model (fun x => f306 ((51/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(207322026032371/25000000000000),(560349057353/20000000000000),(431218953/4000000000000),(-30053407/20000000000000)⟩
def e307 : ℝ := (145332787/50000000000000)
theorem h307 : Model (fun x => f307 ((51/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(839287171843869/50000000000000),(7561405551731/100000000000000),(4169031289/12500000000000),(-75194991/20000000000000)⟩
def e308 : ℝ := (392883659/50000000000000)
theorem h308 : Model (fun x => f308 ((51/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(440126880189057/25000000000000),(7883801826819/50000000000000),(50167636973/50000000000000),(-527445861/100000000000000)⟩
def e309 : ℝ := (164761791/10000000000000)
theorem h309 : Model (fun x => f309 ((51/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(102411482249557/12500000000000),(1139743461/62500000000),(155096633/3125000000000),(-1714917/1562500000000)⟩
def e310 : ℝ := (11783421/6250000000000)
theorem h310 : Model (fun x => f310 ((51/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(924172974961969/100000000000000),(2290480806501/100000000000000),(1688348101/25000000000000),(-135026713/100000000000000)⟩
def e311 : ℝ := (236971657/100000000000000)
theorem h311 : Model (fun x => f311 ((51/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1024172974961969/100000000000000),(2290480806501/100000000000000),(1688348101/25000000000000),(-135026713/100000000000000)⟩
def e312 : ℝ := (236971657/100000000000000)
theorem h312 : Model (fun x => f312 ((51/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(2253830281219783/12500000000000),(50452905569901/25000000000000),(1507654676619/100000000000000),(-552013133/12500000000000)⟩
def e313 : ℝ := (21148588049/100000000000000)
theorem h313 : Model (fun x => f313 ((51/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(277305707181/50000000000000),(-6207600801/100000000000000),(4621061/20000000000000),(198141/50000000000000)⟩
def e314 : ℝ := (673337/100000000000000)
theorem h314 : Model (fun x => f314 ((51/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (139275761000851/781250000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1191432583719/50000000000000),(222581186397/100000000000000),(358066371/100000000000000),(-14377063/100000000000000)⟩
def e315 : ℝ := (7537567/25000000000000)
theorem h315 : Model (fun x => f315 ((51/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(2411949858191/50000000000000),(456162654231/100000000000000),(633292303/50000000000000),(-26525691/100000000000000)⟩
def e316 : ℝ := (20127819/50000000000000)
theorem h316 : Model (fun x => f316 ((51/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(11846090167237/50000000000000),(2179910427639/100000000000000),(3170503/625000000000),(-14868807/10000000000000)⟩
def e317 : ℝ := (198927891/100000000000000)
theorem h317 : Model (fun x => f317 ((51/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(4645525555779/25000000000000),(269075744637/20000000000000),(-12991053961/50000000000000),(196417501/50000000000000)⟩
def e318 : ℝ := (34539981/20000000000000)
theorem h318 : Model (fun x => f318 ((51/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-25319377008093/50000000000000),(-3291038467029/100000000000000),(22548204769/25000000000000),(-2045015971/100000000000000)⟩
def e319 : ℝ := (12565027/4000000000000)
theorem h319 : Model (fun x => f319 ((51/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((51/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-28611/1600),(-561/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((51/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((51/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(4947/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((51/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(169269/1600),(1379/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((51/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((51/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(342069/1600),(1379/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((51/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1710345/32),(6895/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((51/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((51/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(880176857935166967/100000000000000),(12626893954473/200000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (57227/50000000000000)
theorem h329 : Model (fun x => f329 ((51/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(1420169127/12500000000000),(-8149419/10000000000000),(1175089/100000000000000),(-2533/20000000000000)⟩
def e330 : ℝ := (39/25000000000000)
theorem h330 : Model (fun x => f330 ((51/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (109227207667754867/12500000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(607244791379703/100000000000000),(540308677971/100000000000000),(4080129683/50000000000000),(-7616107/25000000000000)⟩
def e331 : ℝ := (3180941/20000000000000)
theorem h331 : Model (fun x => f331 ((51/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((51/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(411/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((51/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((51/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((51/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(505806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((51/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((51/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((51/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(2244007042020577/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1017/100000000000000)
theorem h339 : Model (fun x => f339 ((51/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3604193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((51/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((51/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((51/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(507748239494791/25000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1017/100000000000000)
theorem h343 : Model (fun x => f343 ((51/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2461849993303/50000000000000),(-1707628977/25000000000000),(947579/10000000000000),(-6573/50000000000000)⟩
def e344 : ℝ := (23/100000000000000)
theorem h344 : Model (fun x => f344 ((51/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1014087708171833/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(27622043606851/25000000000000),(93892044159/10000000000000),(-1302538953/100000000000000),(903483/50000000000000)⟩
def e345 : ℝ := (3489/100000000000000)
theorem h345 : Model (fun x => f345 ((51/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(52622043606851/25000000000000),(93892044159/10000000000000),(-1302538953/100000000000000),(903483/50000000000000)⟩
def e346 : ℝ := (3489/100000000000000)
theorem h346 : Model (fun x => f346 ((51/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(52622043606851/50000000000000),(93892044159/20000000000000),(-651269477/100000000000000),(903483/100000000000000)⟩
def e347 : ℝ := (349/20000000000000)
theorem h347 : Model (fun x => f347 ((51/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(2622043606851/50000000000000),(93892044159/20000000000000),(-651269477/100000000000000),(903483/100000000000000)⟩
def e348 : ℝ := (349/20000000000000)
theorem h348 : Model (fun x => f348 ((51/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(194200399025283/50000000000000),(1732531767219/100000000000000),(-2403494499/100000000000000),(1667141/50000000000000)⟩
def e349 : ℝ := (6443/100000000000000)
theorem h349 : Model (fun x => f349 ((51/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(2744115083764851/100000000000000),(1732531767219/100000000000000),(-2403494499/100000000000000),(1667141/50000000000000)⟩
def e350 : ℝ := (1611/25000000000000)
theorem h350 : Model (fun x => f350 ((51/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(2888018872001831/100000000000000),(1838239496901/12500000000000),(-6133786171/50000000000000),(2867423/50000000000000)⟩
def e351 : ℝ := (101733/100000000000000)
theorem h351 : Model (fun x => f351 ((51/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8170399824382783/100000000000000),(1838239496901/12500000000000),(-6133786171/50000000000000),(2867423/50000000000000)⟩
def e352 : ℝ := (50867/50000000000000)
theorem h352 : Model (fun x => f352 ((51/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(8598862716881571/100000000000000),(53833884089903/100000000000000),(2916210867/100000000000000),(-14702551/20000000000000)⟩
def e353 : ℝ := (490211/100000000000000)
theorem h353 : Model (fun x => f353 ((51/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(1386791033592919/10000000000000),(53833884089903/100000000000000),(2916210867/100000000000000),(-14702551/20000000000000)⟩
def e354 : ℝ := (122553/25000000000000)
theorem h354 : Model (fun x => f354 ((51/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(1459515564866331/10000000000000),(60880651202403/50000000000000),(165480343503/100000000000000),(-144493411/50000000000000)⟩
def e355 : ℝ := (441971/50000000000000)
theorem h355 : Model (fun x => f355 ((51/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(3386173986875519/20000000000000),(60880651202403/50000000000000),(165480343503/100000000000000),(-144493411/50000000000000)⟩
def e356 : ℝ := (883943/100000000000000)
theorem h356 : Model (fun x => f356 ((51/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(8909369759887403/50000000000000),(25953783833987/12500000000000),(635513568077/100000000000000),(-167303823/100000000000000)⟩
def e357 : ℝ := (513943/20000000000000)
theorem h357 : Model (fun x => f357 ((51/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(9110560236077879/50000000000000),(25953783833987/12500000000000),(635513568077/100000000000000),(-167303823/100000000000000)⟩
def e358 : ℝ := (642429/25000000000000)
theorem h358 : Model (fun x => f358 ((51/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(3835330384205863/20000000000000),(304059495547881/100000000000000),(381228346243/25000000000000),(809899083/50000000000000)⟩
def e359 : ℝ := (6093409/100000000000000)
theorem h359 : Model (fun x => f359 ((51/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(19159032873410267/100000000000000),(304059495547881/100000000000000),(381228346243/25000000000000),(809899083/50000000000000)⟩
def e360 : ℝ := (609341/10000000000000)
theorem h360 : Model (fun x => f360 ((51/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(20163749266593737/100000000000000),(102487169676413/25000000000000),(2907542618767/100000000000000),(7056455457/100000000000000)⟩
def e361 : ℝ := (7204641/100000000000000)
theorem h361 : Model (fun x => f361 ((51/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(2016708259992707/10000000000000),(102487169676413/25000000000000),(2907542618767/100000000000000),(7056455457/100000000000000)⟩
def e362 : ℝ := (3602321/50000000000000)
theorem h362 : Model (fun x => f362 ((51/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(132197424999937/12500000000000),(116174496744271/100000000000000),(972838994763/50000000000000),(11532138223/100000000000000)⟩
def e363 : ℝ := (18685691/100000000000000)
theorem h363 : Model (fun x => f363 ((51/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(110763178934453/100000000000000),(494079124207/50000000000000),(208270939/25000000000000),(-2106589/50000000000000)⟩
def e364 : ℝ := (4107/25000000000000)
theorem h364 : Model (fun x => f364 ((51/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(102622043606851/50000000000000),(93892044159/20000000000000),(-651269477/100000000000000),(903483/100000000000000)⟩
def e365 : ℝ := (349/20000000000000)
theorem h365 : Model (fun x => f365 ((51/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(421251353361857/100000000000000),(481769672501/25000000000000),(-234727599/50000000000000),(-601553/25000000000000)⟩
def e366 : ℝ := (9959/50000000000000)
theorem h366 : Model (fun x => f366 ((51/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(864593495082909/100000000000000),(2966411300391/50000000000000),(5339857351/100000000000000),(-3177411/20000000000000)⟩
def e367 : ℝ := (11509/20000000000000)
theorem h367 : Model (fun x => f367 ((51/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(44363175677299/2500000000000),(8117845061989/50000000000000),(1327246001/4000000000000),(-38365943/100000000000000)⟩
def e368 : ℝ := (94741/50000000000000)
theorem h368 : Model (fun x => f368 ((51/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(122845159141131/6250000000000),(3551830169181/10000000000000),(21197010413/10000000000000),(345879847/100000000000000)⟩
def e369 : ℝ := (161799/12500000000000)
theorem h369 : Model (fun x => f369 ((51/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(52622043606851/6250000000000),(93892044159/2500000000000),(-651269477/12500000000000),(903483/12500000000000)⟩
def e370 : ℝ := (349/2500000000000)
theorem h370 : Model (fun x => f370 ((51/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(952715876644069/100000000000000),(2371920007387/50000000000000),(-218853603/5000000000000),(1507343/50000000000000)⟩
def e371 : ℝ := (7597/25000000000000)
theorem h371 : Model (fun x => f371 ((51/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1052715876644069/100000000000000),(2371920007387/50000000000000),(-218853603/5000000000000),(1507343/50000000000000)⟩
def e372 : ℝ := (7597/25000000000000)
theorem h372 : Model (fun x => f372 ((51/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(20691367903477741/100000000000000),(467148046072819/100000000000000),(1915171004967/50000000000000),(3050311839/25000000000000)⟩
def e373 : ℝ := (22505301/100000000000000)
theorem h373 : Model (fun x => f373 ((51/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(15102916417/3125000000000),(-5455645409/50000000000000),(15687747/10000000000000),(-112933/6250000000000)⟩
def e374 : ℝ := (19413/100000000000000)
theorem h374 : Model (fun x => f374 ((51/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (20220377291642331/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(511121065041/10000000000000),(446068024551/100000000000000),(-322740307/20000000000000),(6577383/100000000000000)⟩
def e375 : ℝ := (321529/50000000000000)
theorem h375 : Model (fun x => f375 ((51/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(27622043606851/12500000000000),(93892044159/5000000000000),(-1302538953/50000000000000),(903483/25000000000000)⟩
def e376 : ℝ := (3489/50000000000000)
theorem h376 : Model (fun x => f376 ((51/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(11877151801049/25000000000000),(-4238414113/2000000000000),(309825593/25000000000000),(-362369/5000000000000)⟩
def e377 : ℝ := (21429/50000000000000)
theorem h377 : Model (fun x => f377 ((51/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (104773974818203/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(26245696397901/25000000000000),(423841411297/100000000000000),(-619651187/25000000000000),(14494759/100000000000000)⟩
def e378 : ℝ := (55023/20000000000000)
theorem h378 : Model (fun x => f378 ((51/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1245696397901/25000000000000),(423841411297/100000000000000),(-619651187/25000000000000),(14494759/100000000000000)⟩
def e379 : ℝ := (55023/20000000000000)
theorem h379 : Model (fun x => f379 ((51/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(387436470635681/100000000000000),(1564176636929/100000000000000),(-9147231809/100000000000000),(26746281/50000000000000)⟩
def e380 : ℝ := (1015309/100000000000000)
theorem h380 : Model (fun x => f380 ((51/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(1371575378174983/50000000000000),(1564176636929/100000000000000),(-9147231809/100000000000000),(26746281/50000000000000)⟩
def e381 : ℝ := (101531/10000000000000)
theorem h381 : Model (fun x => f381 ((51/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(719959019248337/25000000000000),(13268725084739/100000000000000),(-70965255317/100000000000000),(9405789/2500000000000)⟩
def e382 : ℝ := (9304209/100000000000000)
theorem h382 : Model (fun x => f382 ((51/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(81622170293743/1000000000000),(13268725084739/100000000000000),(-70965255317/100000000000000),(9405789/2500000000000)⟩
def e383 : ℝ := (930421/10000000000000)
theorem h383 : Model (fun x => f383 ((51/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(856892280346941/10000000000000),(77639572891/160000000000),(-110286024503/50000000000000),(948412669/100000000000000)⟩
def e384 : ℝ := (37596181/100000000000000)
theorem h384 : Model (fun x => f384 ((51/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(13837970422517029/100000000000000),(77639572891/160000000000),(-110286024503/50000000000000),(948412669/100000000000000)⟩
def e385 : ℝ := (18798091/50000000000000)
theorem h385 : Model (fun x => f385 ((51/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(1452748681890063/10000000000000),(54796832798827/50000000000000),(-184441679893/50000000000000),(863838479/100000000000000)⟩
def e386 : ℝ := (47205141/50000000000000)
theorem h386 : Model (fun x => f386 ((51/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(3372640220922983/20000000000000),(54796832798827/50000000000000),(-184441679893/50000000000000),(863838479/100000000000000)⟩
def e387 : ℝ := (94410283/100000000000000)
theorem h387 : Model (fun x => f387 ((51/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(17703458259538873/100000000000000),(37305542505603/20000000000000),(-34073279097/10000000000000),(-46435609/5000000000000)⟩
def e388 : ℝ := (87488791/50000000000000)
theorem h388 : Model (fun x => f388 ((51/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(724233568476793/4000000000000),(37305542505603/20000000000000),(-34073279097/10000000000000),(-46435609/5000000000000)⟩
def e389 : ℝ := (174977583/100000000000000)
theorem h389 : Model (fun x => f389 ((51/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(19008014359410353/100000000000000),(34070254119397/12500000000000),(-7950638259/50000000000000),(-138063799/3125000000000)⟩
def e390 : ℝ := (266340717/100000000000000)
theorem h390 : Model (fun x => f390 ((51/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(3798079062358261/20000000000000),(34070254119397/12500000000000),(-7950638259/50000000000000),(-138063799/3125000000000)⟩
def e391 : ℝ := (133170359/50000000000000)
theorem h391 : Model (fun x => f391 ((51/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(19936645993175883/100000000000000),(14665294966473/4000000000000),(667840324241/100000000000000),(-4354351379/50000000000000)⟩
def e392 : ℝ := (177513221/50000000000000)
theorem h392 : Model (fun x => f392 ((51/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(623124353953413/3125000000000),(14665294966473/4000000000000),(667840324241/100000000000000),(-4354351379/50000000000000)⟩
def e393 : ℝ := (355026443/100000000000000)
theorem h393 : Model (fun x => f393 ((51/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(993566416850117/100000000000000),(102782394903697/100000000000000),(1092983606033/100000000000000),(-3800467617/100000000000000)⟩
def e394 : ℝ := (75707857/100000000000000)
theorem h394 : Model (fun x => f394 ((51/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(55106926352863/50000000000000),(44496052007/5000000000000),(-1703900599/50000000000000),(147239/1562500000000)⟩
def e395 : ℝ := (765021/100000000000000)
theorem h395 : Model (fun x => f395 ((51/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(51245696397901/25000000000000),(423841411297/100000000000000),(-619651187/25000000000000),(14494759/100000000000000)⟩
def e396 : ℝ := (55023/20000000000000)
theorem h396 : Model (fun x => f396 ((51/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(210089711944467/50000000000000),(868801931367/50000000000000),(-4182505347/50000000000000),(19206407/50000000000000)⟩
def e397 : ℝ := (1315251/100000000000000)
theorem h397 : Model (fun x => f397 ((51/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(86129548757029/10000000000000),(5342683200569/100000000000000),(-1262295897/6250000000000),(61120939/100000000000000)⟩
def e398 : ℝ := (897321/20000000000000)
theorem h398 : Model (fun x => f398 ((51/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1765507482596367/100000000000000),(1825263474977/12500000000000),(-8020687129/20000000000000),(6420797/20000000000000)⟩
def e399 : ℝ := (13138719/100000000000000)
theorem h399 : Model (fun x => f399 ((51/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(1945833816377331/100000000000000),(31805168135291/100000000000000),(1279135149/5000000000000),(-326373841/50000000000000)⟩
def e400 : ℝ := (7812451/25000000000000)
theorem h400 : Model (fun x => f400 ((51/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(26245696397901/3125000000000),(423841411297/12500000000000),(-619651187/3125000000000),(14494759/12500000000000)⟩
def e401 : ℝ := (55023/2500000000000)
theorem h401 : Model (fun x => f401 ((51/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(475038068719279/50000000000000),(1070163082629/25000000000000),(-11618319591/50000000000000),(15672671/12500000000000)⟩
def e402 : ℝ := (2965941/100000000000000)
theorem h402 : Model (fun x => f402 ((51/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(525038068719279/50000000000000),(1070163082629/25000000000000),(-11618319591/50000000000000),(15672671/12500000000000)⟩
def e403 : ℝ := (2965941/100000000000000)
theorem h403 : Model (fun x => f403 ((51/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(510818414499709/2500000000000),(417272861669627/100000000000000),(1177960147319/100000000000000),(-5354990089/50000000000000)⟩
def e404 : ℝ := (49290503/12500000000000)
theorem h404 : Model (fun x => f404 ((51/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(12235267607/2500000000000),(-9994637983/100000000000000),(175893467/100000000000000),(-2759333/100000000000000)⟩
def e405 : ℝ := (12983/25000000000000)
theorem h405 : Model (fun x => f405 ((51/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (5003568663466803/25000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(972524079639/20000000000000),(403724676289/100000000000000),(-31759311/1000000000000),(25532061/100000000000000)⟩
def e406 : ℝ := (9493/625000000000)
theorem h406 : Model (fun x => f406 ((51/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(1994766209721/20000000000000),(21244817521/2500000000000),(-957926527/20000000000000),(8027361/25000000000000)⟩
def e407 : ℝ := (1080969/50000000000000)
theorem h407 : Model (fun x => f407 ((51/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(12113113908733/20000000000000),(5214211388057/100000000000000),(-23679400513/100000000000000),(235410943/100000000000000)⟩
def e408 : ℝ := (15342679/100000000000000)
theorem h408 : Model (fun x => f408 ((51/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(47502407485227/100000000000000),(3158157804647/100000000000000),(-80496741671/100000000000000),(1763003517/100000000000000)⟩
def e409 : ℝ := (61858243/100000000000000)
theorem h409 : Model (fun x => f409 ((51/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3136346530959/100000000000000),(-66440331191/50000000000000),(1939215481/20000000000000),(-141006227/50000000000000)⟩
def e410 : ℝ := (187991959/50000000000000)
theorem h410 : Model (fun x => f410 ((51/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(601204385742187/100000000000000),(13439981689453/25000000000000),(7803/409600),(3417/10240000)⟩
def e411 : ℝ := (289062501/100000000000000)
theorem h411 : Model (fun x => f411 ((51/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(29241/1600),(171/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((51/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(5000211/64000),(87723/64000),(513/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((51/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(46971074731817603/100000000000000),(2512112730188029/50000000000000),(2841786787191/1250000000000),(707319679367/12500000000000)⟩
def e414 : ℝ := (85128396123/100000000000000)
theorem h414 : Model (fun x => f414 ((51/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(212896980899/100000000000000),(-22772364439/100000000000000),(175674251/12500000000000),(-65754719/100000000000000)⟩
def e415 : ℝ := (4010063/100000000000000)
theorem h415 : Model (fun x => f415 ((51/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (20856881321317603/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(715284415593/20000000000000),(19984369697/10000000000000),(-1626958301/20000000000000),(221970869/100000000000000)⟩
def e416 : ℝ := (152902067/100000000000000)
theorem h416 : Model (fun x => f416 ((51/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(220037773503/50000000000000),(16740758647/25000000000000),(15612859/1000000000000),(-12008317/20000000000000)⟩
def e417 : ℝ := (105777197/20000000000000)
theorem h417 : Model (fun x => f417 ((51/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((51/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((1320201268963/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (5/4) (13/10) ∧
    SigmaActualBlockSeparable.endpointCellMass (5/4) (13/10) ≤ (1323374584873/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(51/40)-(1/40)) (by norm_num : ((51/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel5


noncomputable section
namespace Hf4Quad.Panel6
open Hf4Quad.Dag

def p0 : Cubic := ⟨(53/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((53/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((53/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((53/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((53/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(58047619047619/25000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((53/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-58047619047619/25000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((53/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-28152380952381/20000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((53/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((53/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(2809/1600),(53/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((53/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(53133201058201/25000000000000),(1604021164021/20000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((53/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-53133201058201/25000000000000),(-1604021164021/20000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((53/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-353294708994709/100000000000000),(-12401058201057/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((53/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((53/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(148877/64000),(8427/64000),(159/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((53/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1133162466724537/50000000000000),(128282543402777/100000000000000),(1210212673611/50000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((53/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1133162466724537/50000000000000),(-128282543402777/100000000000000),(-1210212673611/50000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((53/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-2619619642443783/100000000000000),(-70341800801917/50000000000000),(-2496086722883/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((53/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((53/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(7890481/2560000),(148877/640000),(8427/1280000),(53/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((53/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(861064394841269/100000000000000),(16246498015873/25000000000000),(459806547619/25000000000000),(11567460317/50000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((53/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-879277623801257/50000000000000),(-37848804770171/50000000000000),(-656860532407/100000000000000),(7912119709/100000000000000)⟩
def e20 : ℝ := (109126993/100000000000000)
theorem h20 : Model (fun x => f20 ((53/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((53/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(102098509033203/25000000000000),(9631934814453/25000000000000),(148877/10240000),(2809/10240000)⟩
def e22 : ℝ := (129882813/50000000000000)
theorem h22 : Model (fun x => f22 ((53/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(133030575844003/5000000000000),(50200217299623/20000000000000),(591983694571/6250000000000),(89356029369/50000000000000)⟩
def e23 : ℝ := (1692324951/100000000000000)
theorem h23 : Model (fun x => f23 ((53/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(451028134638773/50000000000000),(175303476957773/100000000000000),(8814878580729/100000000000000),(186624178447/100000000000000)⟩
def e24 : ℝ := (225181493/12500000000000)
theorem h24 : Model (fun x => f24 ((53/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((53/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(21644883915039/4000000000000),(61259105419921/100000000000000),(577916088867/20000000000000),(9086730957/12500000000000)⟩
def e26 : ℝ := (1036474613/100000000000000)
theorem h26 : Model (fun x => f26 ((53/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(1215091102320443/100000000000000),(68778741640779/50000000000000),(3244280266073/50000000000000),(163234227223/100000000000000)⟩
def e27 : ℝ := (290925811/12500000000000)
theorem h27 : Model (fun x => f27 ((53/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(2117147371597989/100000000000000),(312860960239331/100000000000000),(122427512903/800000000000),(34985840567/10000000000000)⟩
def e28 : ℝ := (64513413/1562500000000)
theorem h28 : Model (fun x => f28 ((53/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((53/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(358493389842833/50000000000000),(47348183564147/50000000000000),(5360171724241/100000000000000),(42139714813/25000000000000)⟩
def e30 : ℝ := (1608293461/50000000000000)
theorem h30 : Model (fun x => f30 ((53/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(85071050446831/50000000000000),(11235799115619/50000000000000),(1271977258371/100000000000000),(19999642427/50000000000000)⟩
def e31 : ℝ := (11926581/1562500000000)
theorem h31 : Model (fun x => f31 ((53/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(2287289472491651/100000000000000),(335332558470569/100000000000000),(8287708185623/50000000000000),(97464422631/25000000000000)⟩
def e32 : ℝ := (38219997/781250000000)
theorem h32 : Model (fun x => f32 ((53/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((53/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(1205061/320),(22737/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((53/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((53/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(117077/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((53/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(3078293/320),(40409/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((53/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((53/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(3807893/320),(40409/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((53/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-3807893/320),(-40409/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((53/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((53/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(93/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((53/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(8649/1600),(93/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((53/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((53/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(181629/160),(1953/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((53/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(88091659371/100000000000000),(-7400173/390625000000),(30555553/100000000000000),(-438073/100000000000000)⟩
def e46 : ℝ := (759/12500000000000)
theorem h46 : Model (fun x => f46 ((53/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (88851/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-524130645433149/50000000000000),(147577212687/50000000000000),(-3244999321/100000000000000),(3566571/10000000000000)⟩
def e47 : ℝ := (144058261/100000000000000)
theorem h47 : Model (fun x => f47 ((53/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((53/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(133/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((53/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((53/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((53/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(27708333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/25000000000000)
theorem h52 : Model (fun x => f52 ((53/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(52708333333333/25000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/25000000000000)
theorem h53 : Model (fun x => f53 ((53/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((53/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(52708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (3/100000000000000)
theorem h55 : Model (fun x => f55 ((53/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((53/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(1106874999999993/50000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (63/100000000000000)
theorem h57 : Model (fun x => f57 ((53/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((53/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(2708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (3/100000000000000)
theorem h59 : Model (fun x => f59 ((53/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(119911458333317/100000000000000),(9697916666651/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (9/12500000000000)
theorem h60 : Model (fun x => f60 ((53/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(111126736111109/100000000000000),(43923611111/5000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (1/12500000000000)
theorem h61 : Model (fun x => f61 ((53/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((53/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(52708333333333/5000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (3/10000000000000)
theorem h63 : Model (fun x => f63 ((53/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1165293402777769/100000000000000),(63064236111/1250000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (19/50000000000000)
theorem h64 : Model (fun x => f64 ((53/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1265293402777769/100000000000000),(63064236111/1250000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (19/50000000000000)
theorem h65 : Model (fun x => f65 ((53/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(1517231771466073/100000000000000),(64378399703309/50000000000000),(952660047737/100000000000000),(1003870081/50000000000000)⟩
def e66 : ℝ := (316961/50000000000000)
theorem h66 : Model (fun x => f66 ((53/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(102708333333333/50000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (3/100000000000000)
theorem h67 : Model (fun x => f67 ((53/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(421960069444441/100000000000000),(53493923611/3125000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (7/50000000000000)
theorem h68 : Model (fun x => f68 ((53/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(866776309317119/100000000000000),(1054900173609/20000000000000),(10698784721/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (11/25000000000000)
theorem h69 : Model (fun x => f69 ((53/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(3287751388125093/25000000000000),(598029918423881/50000000000000),(1521103546543/10000000000000),(81535844797/100000000000000)⟩
def e70 : ℝ := (27868513/12500000000000)
theorem h70 : Model (fun x => f70 ((53/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((53/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(2333661458333289/12500000000000),(922395833331/625000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (21/1562500000000)
theorem h72 : Model (fun x => f72 ((53/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1011253298610967/100000000000000),(21445703124963/25000000000000),(630729166663/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (323/50000000000000)
theorem h73 : Model (fun x => f73 ((53/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(2191326004886941/25000000000000),(79688366022801/10000000000000),(1262477249491/12500000000000),(53052425671/100000000000000)⟩
def e74 : ℝ := (137967399/100000000000000)
theorem h74 : Model (fun x => f74 ((53/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(2739538696506017/12500000000000),(498235874268943/25000000000000),(12655426730679/50000000000000),(33647067617/25000000000000)⟩
def e75 : ℝ := (360915503/100000000000000)
theorem h75 : Model (fun x => f75 ((53/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((53/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(777887152777763/12500000000000),(307465277777/625000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (7/1562500000000)
theorem h77 : Model (fun x => f77 ((53/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(293402777777/100000000000000),(5642361111/12500000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/50000000000000)
theorem h78 : Model (fun x => f78 ((53/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(7946325231/50000000000000),(1833767361/50000000000000),(56423611/20000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((53/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(494507544719/50000000000000),(236052552511/100000000000000),(19376155363/100000000000000),(296259113/50000000000000)⟩
def e80 : ℝ := (384013/10000000000000)
theorem h80 : Model (fun x => f80 ((53/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(2031601829553/100000000000000),(97802436231/20000000000000),(5098175597/12500000000000),(1297865169/100000000000000)⟩
def e81 : ℝ := (10373097/100000000000000)
theorem h81 : Model (fun x => f81 ((53/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(21918341173877689/100000000000000),(1993432509256927/100000000000000),(12675819433067/50000000000000),(135886135637/100000000000000)⟩
def e82 : ℝ := (1856443/500000000000)
theorem h82 : Model (fun x => f82 ((53/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(8608519/1000000000000),(264877507/100000000000000),(30562789/100000000000000),(783661/50000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((53/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(46629477/100000000000000),(8967207/50000000000000),(137957/5000000000000),(212241/100000000000000)⟩
def e84 : ℝ := (2073/25000000000000)
theorem h84 : Model (fun x => f84 ((53/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(2525763/100000000000000),(145717/12500000000000),(11209/5000000000000),(1437/6250000000000)⟩
def e85 : ℝ := (1371/100000000000000)
theorem h85 : Model (fun x => f85 ((53/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(34203/25000000000000),(18417/25000000000000),(17/100000000000),(2179/100000000000000)⟩
def e86 : ℝ := (177/100000000000000)
theorem h86 : Model (fun x => f86 ((53/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(102609/25000000000000),(55251/25000000000000),(51/100000000000),(6537/100000000000000)⟩
def e87 : ℝ := (531/100000000000000)
theorem h87 : Model (fun x => f87 ((53/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-102609/25000000000000),(-55251/25000000000000),(-51/100000000000),(-6537/100000000000000)⟩
def e88 : ℝ := (531/100000000000000)
theorem h88 : Model (fun x => f88 ((53/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(21918341173467253/100000000000000),(1993432509035923/100000000000000),(12675819407567/50000000000000),(1358861291/1000000000000)⟩
def e89 : ℝ := (371289131/100000000000000)
theorem h89 : Model (fun x => f89 ((53/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(2333661458333289/10000000000000),(922395833331/500000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (21/1250000000000)
theorem h90 : Model (fun x => f90 ((53/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(222562875256947/12500000000000),(3611567955481/25000000000000),(43954173897/100000000000000),(14859423/25000000000000)⟩
def e91 : ℝ := (1513/5000000000000)
theorem h91 : Model (fun x => f91 ((53/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(83101824646876291/20000000000000),(3327963938700913/50000000000000),(43399195221629/100000000000000),(73812869083/50000000000000)⟩
def e92 : ℝ := (138632101/50000000000000)
theorem h92 : Model (fun x => f92 ((53/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(12033430123/50000000000000),(-385520503/100000000000000),(3661807/100000000000000),(-13471/50000000000000)⟩
def e93 : ℝ := (21/10000000000000)
theorem h93 : Model (fun x => f93 ((53/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (25550603016172227/6250000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(5275056538459/100000000000000),(197628458453/50000000000000),(-781140201/100000000000000),(205817/10000000000000)⟩
def e94 : ℝ := (275577/100000000000000)
theorem h94 : Model (fun x => f94 ((53/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(27708333333333/12500000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/12500000000000)
theorem h95 : Model (fun x => f95 ((53/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(1897233201581/4000000000000),(-4686840913/2500000000000),(148200503/20000000000000),(-91527/3125000000000)⟩
def e96 : ℝ := (5813/50000000000000)
theorem h96 : Model (fun x => f96 ((53/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (41999999999999/20000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(21027667984189/20000000000000),(374947273039/100000000000000),(-741002517/50000000000000),(2928863/50000000000000)⟩
def e97 : ℝ := (14957/20000000000000)
theorem h97 : Model (fun x => f97 ((53/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(441581027667969/20000000000000),(7873892733819/100000000000000),(-15561052857/50000000000000),(61506123/50000000000000)⟩
def e98 : ℝ := (314097/20000000000000)
theorem h98 : Model (fun x => f98 ((53/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1027667984189/20000000000000),(374947273039/100000000000000),(-741002517/50000000000000),(2928863/50000000000000)⟩
def e99 : ℝ := (14957/20000000000000)
theorem h99 : Model (fun x => f99 ((53/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(14181208892489/12500000000000),(8683067481167/100000000000000),(-4797478791/100000000000000),(-97729153/100000000000000)⟩
def e100 : ℝ := (3131051/100000000000000)
theorem h100 : Model (fun x => f100 ((53/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(110540705213321/100000000000000),(98553334613/12500000000000),(-342091281/20000000000000),(300989/25000000000000)⟩
def e101 : ℝ := (44777/20000000000000)
theorem h101 : Model (fun x => f101 ((53/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(21027667984189/2000000000000),(374947273039/10000000000000),(-741002517/5000000000000),(2928863/5000000000000)⟩
def e102 : ℝ := (14957/2000000000000)
theorem h102 : Model (fun x => f102 ((53/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1161924104422771/100000000000000),(2268949703647/50000000000000),(-3306101349/20000000000000),(1868163/3125000000000)⟩
def e103 : ℝ := (194347/20000000000000)
theorem h103 : Model (fun x => f103 ((53/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1261924104422771/100000000000000),(2268949703647/50000000000000),(-3306101349/20000000000000),(1868163/3125000000000)⟩
def e104 : ℝ := (194347/20000000000000)
theorem h104 : Model (fun x => f104 ((53/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(1431648746502913/100000000000000),(14340244187797/12500000000000),(157367260477/50000000000000),(-704626491/25000000000000)⟩
def e105 : ℝ := (21201667/50000000000000)
theorem h105 : Model (fun x => f105 ((53/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(41027667984189/20000000000000),(374947273039/100000000000000),(-741002517/50000000000000),(2928863/50000000000000)⟩
def e106 : ℝ := (14957/20000000000000)
theorem h106 : Model (fun x => f106 ((53/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(420817385055211/100000000000000),(769160611491/50000000000000),(-4674466473/100000000000000),(807463/6250000000000)⟩
def e107 : ℝ := (74691/20000000000000)
theorem h107 : Model (fun x => f107 ((53/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(86325779780099/10000000000000),(946705985843/20000000000000),(-5028882139/50000000000000),(2165641/20000000000000)⟩
def e108 : ℝ := (80729/6250000000000)
theorem h108 : Model (fun x => f108 ((53/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(3089704860326631/25000000000000),(1058113731295833/100000000000000),(8003376442709/100000000000000),(-20816361567/100000000000000)⟩
def e109 : ℝ := (270502583/50000000000000)
theorem h109 : Model (fun x => f109 ((53/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(2321354809479741/12500000000000),(2069620026873/1562500000000),(-7183916901/2500000000000),(6320769/3125000000000)⟩
def e110 : ℝ := (940317/2500000000000)
theorem h110 : Model (fun x => f110 ((53/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(477116403529097/50000000000000),(76436875617003/100000000000000),(8266113709/4000000000000),(-388442803/20000000000000)⟩
def e111 : ℝ := (28857489/100000000000000)
theorem h111 : Model (fun x => f111 ((53/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(1647497823221027/20000000000000),(70501618467571/10000000000000),(5306134677091/100000000000000),(-7284427131/50000000000000)⟩
def e112 : ℝ := (18423001/5000000000000)
theorem h112 : Model (fun x => f112 ((53/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(20596308557411659/100000000000000),(1763129915971543/100000000000000),(66547555599/500000000000),(-35385215829/100000000000000)⟩
def e113 : ℝ := (454732593/50000000000000)
theorem h113 : Model (fun x => f113 ((53/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(773784936493247/12500000000000),(689873342291/1562500000000),(-2394638967/2500000000000),(2106923/3125000000000)⟩
def e114 : ℝ := (313439/2500000000000)
theorem h114 : Model (fun x => f114 ((53/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(264025371431/100000000000000),(19266065413/50000000000000),(1253553663/100000000000000),(-1313937/12500000000000)⟩
def e115 : ℝ := (14863/20000000000000)
theorem h115 : Model (fun x => f115 ((53/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(13566521061/100000000000000),(296986779/10000000000000),(25621769/12500000000000),(1802233/50000000000000)⟩
def e116 : ℝ := (15073/25000000000000)
theorem h116 : Model (fun x => f116 ((53/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(839805571009/100000000000000),(189832992727/100000000000000),(6993365501/50000000000000),(77697733/25000000000000)⟩
def e117 : ℝ := (5161447/100000000000000)
theorem h117 : Model (fun x => f117 ((53/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(1722763206931/100000000000000),(392569077989/100000000000000),(5878295091/20000000000000),(171807521/25000000000000)⟩
def e118 : ℝ := (5790631/50000000000000)
theorem h118 : Model (fun x => f118 ((53/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(2059803132061859/10000000000000),(440880621262383/25000000000000),(2667780519051/20000000000000),(-6939597149/20000000000000)⟩
def e119 : ℝ := (57565403/6250000000000)
theorem h119 : Model (fun x => f119 ((53/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(697093967/100000000000000),(203469203/100000000000000),(429333/2000000000000),(182107/20000000000000)⟩
def e120 : ℝ := (14033/100000000000000)
theorem h120 : Model (fun x => f120 ((53/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(35819057/100000000000000),(6534337/50000000000000),(4639/250000000000),(1243/1000000000000)⟩
def e121 : ℝ := (3897/100000000000000)
theorem h121 : Model (fun x => f121 ((53/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(230063/12500000000000),(161163/20000000000000),(17977/12500000000000),(411/3125000000000)⟩
def e122 : ℝ := (33/5000000000000)
theorem h122 : Model (fun x => f122 ((53/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(94571/100000000000000),(24153/50000000000000),(10383/100000000000000),(1203/100000000000000)⟩
def e123 : ℝ := (43/50000000000000)
theorem h123 : Model (fun x => f123 ((53/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(283713/100000000000000),(72459/50000000000000),(31149/100000000000000),(3609/100000000000000)⟩
def e124 : ℝ := (129/50000000000000)
theorem h124 : Model (fun x => f124 ((53/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-283713/100000000000000),(-72459/50000000000000),(-31149/100000000000000),(-3609/100000000000000)⟩
def e125 : ℝ := (129/50000000000000)
theorem h125 : Model (fun x => f125 ((53/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(20598031320334877/100000000000000),(881761242452307/50000000000000),(6669451282053/50000000000000),(-17348994677/50000000000000)⟩
def e126 : ℝ := (460523353/50000000000000)
theorem h126 : Model (fun x => f126 ((53/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(2321354809479741/10000000000000),(2069620026873/1250000000000),(-7183916901/2000000000000),(6320769/2500000000000)⟩
def e127 : ℝ := (940317/2000000000000)
theorem h127 : Model (fun x => f127 ((53/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(885436357823529/50000000000000),(3236761572151/25000000000000),(-3135522661/20000000000000),(-35082389/100000000000000)⟩
def e128 : ℝ := (1885691/50000000000000)
theorem h128 : Model (fun x => f128 ((53/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(102770597386093697/25000000000000),(5937495726937673/100000000000000),(2859035377449/25000000000000),(-76129170599/100000000000000)⟩
def e129 : ℝ := (218932869/12500000000000)
theorem h129 : Model (fun x => f129 ((53/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(24326023819/100000000000000),(-351354537/100000000000000),(549759/12500000000000),(-9849/20000000000000)⟩
def e130 : ℝ := (161/25000000000000)
theorem h130 : Model (fun x => f130 ((53/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (50641672474411721/12500000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(5010682005229/100000000000000),(178311391077/50000000000000),(-2045475399/100000000000000),(12110007/100000000000000)⟩
def e131 : ℝ := (539419/100000000000000)
theorem h131 : Model (fun x => f131 ((53/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(1285717317961/12500000000000),(37593984953/5000000000000),(-7066539/250000000000),(14168177/100000000000000)⟩
def e132 : ℝ := (203749/25000000000000)
theorem h132 : Model (fun x => f132 ((53/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-107821415633197/100000000000000),(-3925652513317/50000000000000),(6303150247/20000000000000),(-88796203/50000000000000)⟩
def e133 : ℝ := (4970719/20000000000000)
theorem h133 : Model (fun x => f133 ((53/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(75471698113207/100000000000000),(-1423994304023/100000000000000),(26867817057/100000000000000),(-101387989/20000000000000)⟩
def e134 : ℝ := (9748847/100000000000000)
theorem h134 : Model (fun x => f134 ((53/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (13/10))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-81374653308073/100000000000000),(-878028482103/20000000000000),(1066183483/1000000000000),(-1072849477/50000000000000)⟩
def e135 : ℝ := (40702141/50000000000000)
theorem h135 : Model (fun x => f135 ((53/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(7890481/256000),(148877/64000),(8427/128000),(53/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((53/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((53/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(1339893/32000),(75843/32000),(1431/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((53/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(148877/2048),(300563/64000),(14151/128000),(71/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((53/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-2809/1600),(-53/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((53/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(3632037/51200),(296323/64000),(14071/128000),(71/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((53/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((53/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(159/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((53/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-159/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((53/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(3224997/51200),(286723/64000),(14071/128000),(71/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((53/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(3378597/51200),(286723/64000),(14071/128000),(71/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((53/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((53/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(3378597/800),(286723/1000),(14071/2000),(71/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((53/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((53/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(1491300909/512000),(28137753/128000),(1592703/256000),(10017/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((53/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(34332440683/100000000000000),(-2591127599/100000000000000),(122222999/100000000000000),(-4612189/100000000000000)⟩
def e151 : ℝ := (91087/50000000000000)
theorem h151 : Model (fun x => f151 ((53/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (687762117/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(144994351367827/100000000000000),(-1099069525797/100000000000000),(14787830047/100000000000000),(-226539891/100000000000000)⟩
def e152 : ℝ := (1502745911/100000000000000)
theorem h152 : Model (fun x => f152 ((53/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(173/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((53/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(23009/1600),(153/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((53/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(279/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((53/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(3584229390681/50000000000000),(-77080201951/100000000000000),(1326111/160000000000),(-8912037/100000000000000)⟩
def e156 : ℝ := (96873/100000000000000)
theorem h156 : Model (fun x => f156 ((53/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (69/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(103086917562723/100000000000000),(262506262753/100000000000000),(1657638739/100000000000000),(-17824083/100000000000000)⟩
def e157 : ℝ := (260367/10000000000000)
theorem h157 : Model (fun x => f157 ((53/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(203086917562723/100000000000000),(262506262753/100000000000000),(1657638739/100000000000000),(-17824083/100000000000000)⟩
def e158 : ℝ := (260367/10000000000000)
theorem h158 : Model (fun x => f158 ((53/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(101543458781361/100000000000000),(8203320711/6250000000000),(828819369/100000000000000),(-4456021/50000000000000)⟩
def e159 : ℝ := (1301837/100000000000000)
theorem h159 : Model (fun x => f159 ((53/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(1543458781361/100000000000000),(8203320711/6250000000000),(828819369/100000000000000),(-4456021/50000000000000)⟩
def e160 : ℝ := (1301837/100000000000000)
theorem h160 : Model (fun x => f160 ((53/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((53/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((53/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(374743716931213/100000000000000),(121096639067/25000000000000),(3058738147/100000000000000),(-32889679/100000000000000)⟩
def e163 : ℝ := (12011/250000000000)
theorem h163 : Model (fun x => f163 ((53/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(1365229001322749/50000000000000),(121096639067/25000000000000),(3058738147/100000000000000),(-32889679/100000000000000)⟩
def e164 : ℝ := (4804401/100000000000000)
theorem h164 : Model (fun x => f164 ((53/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((53/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(173287593528669/6250000000000),(815134898497/20000000000000),(1318614291/5000000000000),(-268707503/100000000000000)⟩
def e166 : ℝ := (2531181/6250000000000)
theorem h166 : Model (fun x => f166 ((53/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(1006872806104957/12500000000000),(815134898497/20000000000000),(1318614291/5000000000000),(-268707503/100000000000000)⟩
def e167 : ℝ := (40498897/100000000000000)
theorem h167 : Model (fun x => f167 ((53/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((53/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4089653891391679/50000000000000),(3677749386057/25000000000000),(49445018141/50000000000000),(-922323881/100000000000000)⟩
def e169 : ℝ := (73297781/50000000000000)
theorem h169 : Model (fun x => f169 ((53/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(13448355401830977/100000000000000),(3677749386057/25000000000000),(49445018141/50000000000000),(-922323881/100000000000000)⟩
def e170 : ℝ := (146595563/100000000000000)
theorem h170 : Model (fun x => f170 ((53/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((53/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(13655925224229173/100000000000000),(16294721655563/50000000000000),(115593791273/50000000000000),(-941679393/50000000000000)⟩
def e172 : ℝ := (163019439/50000000000000)
theorem h172 : Model (fun x => f172 ((53/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(7995819754971729/50000000000000),(16294721655563/50000000000000),(115593791273/50000000000000),(-941679393/50000000000000)⟩
def e173 : ℝ := (326038879/100000000000000)
theorem h173 : Model (fun x => f173 ((53/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((53/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(649538554969731/4000000000000),(5408197555087/10000000000000),(410072338113/100000000000000),(-2764060723/100000000000000)⟩
def e175 : ℝ := (54361081/10000000000000)
theorem h175 : Model (fun x => f175 ((53/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(16640844826624227/100000000000000),(5408197555087/10000000000000),(410072338113/100000000000000),(-2764060723/100000000000000)⟩
def e176 : ℝ := (543610811/100000000000000)
theorem h176 : Model (fun x => f176 ((53/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((53/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2112211175924177/12500000000000),(9594792309251/12500000000000),(312654233567/50000000000000),(-825821817/25000000000000)⟩
def e178 : ℝ := (155034813/20000000000000)
theorem h178 : Model (fun x => f178 ((53/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(527502198742949/3125000000000),(9594792309251/12500000000000),(312654233567/50000000000000),(-825821817/25000000000000)⟩
def e179 : ℝ := (387587033/50000000000000)
theorem h179 : Model (fun x => f179 ((53/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((53/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(857030364402111/5000000000000),(100098692715287/100000000000000),(437806430531/50000000000000),(-1700853093/50000000000000)⟩
def e181 : ℝ := (507499043/50000000000000)
theorem h181 : Model (fun x => f181 ((53/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(17143940621375553/100000000000000),(100098692715287/100000000000000),(437806430531/50000000000000),(-1700853093/50000000000000)⟩
def e182 : ℝ := (1014998087/100000000000000)
theorem h182 : Model (fun x => f182 ((53/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(4134525890499/1562500000000),(24046940969539/100000000000000),(286989692729/100000000000000),(39852753/10000000000000)⟩
def e183 : ℝ := (247742507/100000000000000)
theorem h183 : Model (fun x => f183 ((53/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(103110740212819/100000000000000),(66639484679/25000000000000),(1855497553/100000000000000),(-15923489/100000000000000)⟩
def e184 : ℝ := (332997/12500000000000)
theorem h184 : Model (fun x => f184 ((53/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(201543458781361/100000000000000),(8203320711/6250000000000),(828819369/100000000000000),(-4456021/50000000000000)⟩
def e185 : ℝ := (1301837/100000000000000)
theorem h185 : Model (fun x => f185 ((53/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(406197657775541/100000000000000),(132266050367/25000000000000),(3513136291/100000000000000),(-33747573/100000000000000)⟩
def e186 : ℝ := (105353/2000000000000)
theorem h186 : Model (fun x => f186 ((53/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(818664808969701/100000000000000),(799720718109/50000000000000),(2785388647/25000000000000),(-23805111/25000000000000)⟩
def e187 : ℝ := (15981453/100000000000000)
theorem h187 : Model (fun x => f187 ((53/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(1649965371823357/100000000000000),(2149046394491/50000000000000),(1958727747/6250000000000),(-236990209/100000000000000)⟩
def e188 : ℝ := (8617261/20000000000000)
theorem h188 : Model (fun x => f188 ((53/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(850645754071127/50000000000000),(8829908974413/100000000000000),(148773027/200000000000),(-171902549/50000000000000)⟩
def e189 : ℝ := (89356333/100000000000000)
theorem h189 : Model (fun x => f189 ((53/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((53/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(101543458781361/12500000000000),(8203320711/781250000000),(828819369/12500000000000),(-4456021/6250000000000)⟩
def e191 : ℝ := (1301837/12500000000000)
theorem h191 : Model (fun x => f191 ((53/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(915458410463707/100000000000000),(329145747431/25000000000000),(1697210501/20000000000000),(-3488793/4000000000000)⟩
def e192 : ℝ := (817417/6250000000000)
theorem h192 : Model (fun x => f192 ((53/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1015458410463707/100000000000000),(329145747431/25000000000000),(1697210501/20000000000000),(-3488793/4000000000000)⟩
def e193 : ℝ := (817417/6250000000000)
theorem h193 : Model (fun x => f193 ((53/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(6748401447631/39062500000),(56031483959393/50000000000000),(203197935559/20000000000000),(-649278073/20000000000000)⟩
def e194 : ℝ := (142280157/12500000000000)
theorem h194 : Model (fun x => f194 ((53/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(144710196567/25000000000000),(-469343041/12500000000000),(-1937131/20000000000000),(78483/20000000000000)⟩
def e195 : ℝ := (8273/20000000000000)
theorem h195 : Model (fun x => f195 ((53/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (8581412181853579/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(1531668619073/100000000000000),(64629043047/50000000000000),(732683063/100000000000000),(-4879813/50000000000000)⟩
def e196 : ℝ := (807789/50000000000000)
theorem h196 : Model (fun x => f196 ((53/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(103086917562723/50000000000000),(262506262753/50000000000000),(1657638739/50000000000000),(-17824083/50000000000000)⟩
def e197 : ℝ := (260367/5000000000000)
theorem h197 : Model (fun x => f197 ((53/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(49240000882437/100000000000000),(-12729336547/20000000000000),(-159819453/50000000000000),(1313561/25000000000000)⟩
def e198 : ℝ := (321389/50000000000000)
theorem h198 : Model (fun x => f198 ((53/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (101411366616739/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(101519998235123/100000000000000),(127293365467/100000000000000),(639277811/100000000000000),(-1050849/10000000000000)⟩
def e199 : ℝ := (123001/3125000000000)
theorem h199 : Model (fun x => f199 ((53/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(1519998235123/100000000000000),(127293365467/100000000000000),(639277811/100000000000000),(-1050849/10000000000000)⟩
def e200 : ℝ := (123001/3125000000000)
theorem h200 : Model (fun x => f200 ((53/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(187328568171953/50000000000000),(469773134461/100000000000000),(117961977/5000000000000),(-38781333/100000000000000)⟩
def e201 : ℝ := (2905167/20000000000000)
theorem h201 : Model (fun x => f201 ((53/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2730371422058191/100000000000000),(469773134461/100000000000000),(117961977/5000000000000),(-38781333/100000000000000)⟩
def e202 : ℝ := (3631459/25000000000000)
theorem h202 : Model (fun x => f202 ((53/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(1385936509742889/50000000000000),(39524953507/1000000000000),(20447748631/100000000000000),(-160142653/50000000000000)⟩
def e203 : ℝ := (30584061/25000000000000)
theorem h203 : Model (fun x => f203 ((53/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(805425397186673/10000000000000),(39524953507/1000000000000),(20447748631/100000000000000),(-160142653/50000000000000)⟩
def e204 : ℝ := (24467249/20000000000000)
theorem h204 : Model (fun x => f204 ((53/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(2044169622522857/25000000000000),(7132552077161/50000000000000),(19319719221/25000000000000),(-560119029/50000000000000)⟩
def e205 : ℝ := (442223247/100000000000000)
theorem h205 : Model (fun x => f205 ((53/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(13445726109139047/100000000000000),(7132552077161/50000000000000),(19319719221/25000000000000),(-560119029/50000000000000)⟩
def e206 : ℝ := (27638953/6250000000000)
theorem h206 : Model (fun x => f206 ((53/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(1706262613587179/12500000000000),(987420336297/3125000000000),(182567589157/100000000000000),(-295080489/12500000000000)⟩
def e207 : ℝ := (196349981/20000000000000)
theorem h207 : Model (fun x => f207 ((53/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(15985815194411717/100000000000000),(987420336297/3125000000000),(182567589157/100000000000000),(-295080489/12500000000000)⟩
def e208 : ℝ := (490874953/50000000000000)
theorem h208 : Model (fun x => f208 ((53/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(16228799303236799/100000000000000),(13106653403431/25000000000000),(327757841211/100000000000000),(-3642001529/100000000000000)⟩
def e209 : ℝ := (204197393/12500000000000)
theorem h209 : Model (fun x => f209 ((53/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(16631180255617751/100000000000000),(13106653403431/25000000000000),(327757841211/100000000000000),(-3642001529/100000000000000)⟩
def e210 : ℝ := (326715829/20000000000000)
theorem h210 : Model (fun x => f210 ((53/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(3376794780396653/20000000000000),(37196943139823/50000000000000),(505794800563/100000000000000),(-1173170027/25000000000000)⟩
def e211 : ℝ := (581323221/25000000000000)
theorem h211 : Model (fun x => f211 ((53/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(16866354854364217/100000000000000),(37196943139823/50000000000000),(505794800563/100000000000000),(-1173170027/25000000000000)⟩
def e212 : ℝ := (465058577/20000000000000)
theorem h212 : Model (fun x => f212 ((53/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(3424544630096027/20000000000000),(48497211381931/50000000000000),(35800210913/5000000000000),(-1083396229/20000000000000)⟩
def e213 : ℝ := (1520533591/50000000000000)
theorem h213 : Model (fun x => f213 ((53/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(4281514120953367/25000000000000),(48497211381931/50000000000000),(35800210913/5000000000000),(-1083396229/20000000000000)⟩
def e214 : ℝ := (3041067183/100000000000000)
theorem h214 : Model (fun x => f214 ((53/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(65078939075033/25000000000000),(23274647184203/100000000000000),(60958448883/25000000000000),(-175269131/50000000000000)⟩
def e215 : ℝ := (740669609/100000000000000)
theorem h215 : Model (fun x => f215 ((53/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(103063100416593/100000000000000),(258456444751/100000000000000),(1460025653/100000000000000),(-9854461/50000000000000)⟩
def e216 : ℝ := (2006149/25000000000000)
theorem h216 : Model (fun x => f216 ((53/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(201519998235123/100000000000000),(127293365467/100000000000000),(639277811/100000000000000),(-1050849/10000000000000)⟩
def e217 : ℝ := (123001/3125000000000)
theorem h217 : Model (fun x => f217 ((53/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(406103096886839/100000000000000),(102608635137/20000000000000),(109543251/4000000000000),(-20362951/50000000000000)⟩
def e218 : ℝ := (794833/5000000000000)
theorem h218 : Model (fun x => f218 ((53/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(818378953679137/100000000000000),(775413448939/50000000000000),(8767985849/100000000000000),(-117980337/100000000000000)⟩
def e219 : ℝ := (24074371/50000000000000)
theorem h219 : Model (fun x => f219 ((53/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(824598626505407/50000000000000),(833393689929/20000000000000),(24875059739/100000000000000),(-37834761/12500000000000)⟩
def e220 : ℝ := (129622787/100000000000000)
theorem h220 : Model (fun x => f220 ((53/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(424928455234557/25000000000000),(1069632933081/12500000000000),(15121377317/25000000000000),(-511858419/100000000000000)⟩
def e221 : ℝ := (267857787/100000000000000)
theorem h221 : Model (fun x => f221 ((53/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(101519998235123/12500000000000),(127293365467/12500000000000),(639277811/12500000000000),(-1050849/1250000000000)⟩
def e222 : ℝ := (123001/390625000000)
theorem h222 : Model (fun x => f222 ((53/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(915223086297577/100000000000000),(1276803368487/100000000000000),(6574248141/100000000000000),(-51888421/50000000000000)⟩
def e223 : ℝ := (9878213/25000000000000)
theorem h223 : Model (fun x => f223 ((53/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(1015223086297577/100000000000000),(1276803368487/100000000000000),(6574248141/100000000000000),(-51888421/50000000000000)⟩
def e224 : ℝ := (9878213/25000000000000)
theorem h224 : Model (fun x => f224 ((53/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(17255887111155549/100000000000000),(5428764356131/5000000000000),(208765783197/25000000000000),(-4394977/78125000000)⟩
def e225 : ℝ := (1704669457/50000000000000)
theorem h225 : Model (fun x => f225 ((53/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(579512367899/100000000000000),(-729266729/20000000000000),(-2550657/50000000000000),(9937/2500000000000)⟩
def e226 : ℝ := (29861/25000000000000)
theorem h226 : Model (fun x => f226 ((53/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (17146467725990667/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(1508562003349/100000000000000),(31346869503/25000000000000),(551096187/100000000000000),(-11075017/100000000000000)⟩
def e227 : ℝ := (475219/10000000000000)
theorem h227 : Model (fun x => f227 ((53/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(1520115311211/50000000000000),(127322782053/50000000000000),(5135117/400000000000),(-20834643/100000000000000)⟩
def e228 : ℝ := (795971/12500000000000)
theorem h228 : Model (fun x => f228 ((53/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(2204081335533/50000000000000),(335807435677/100000000000000),(-24387013/5000000000000),(-1693683/12500000000000)⟩
def e229 : ℝ := (29500623/50000000000000)
theorem h229 : Model (fun x => f229 ((53/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(1663457611723/50000000000000),(190667588747/100000000000000),(-991401883/25000000000000),(64596773/100000000000000)⟩
def e230 : ℝ := (11872447/25000000000000)
theorem h230 : Model (fun x => f230 ((53/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-78047738084627/100000000000000),(-524934352721/12500000000000),(3207898149/3125000000000),(-2081102181/100000000000000)⟩
def e231 : ℝ := (12889407/10000000000000)
theorem h231 : Model (fun x => f231 ((53/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((53/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-2809/320),(-53/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((53/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(1113/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((53/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(1219/64),(31/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((53/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((53/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(2883/64),(31/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((53/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((53/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(360375/32),(775/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((53/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(9911/1600),(67/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((53/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(19511/1600),(67/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((53/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((53/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(3687579/1600),(12663/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((53/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(10847225239/25000000000000),(-29799153/10000000000000),(4270399/100000000000000),(-22301/50000000000000)⟩
def e244 : ℝ := (267/50000000000000)
theorem h244 : Model (fun x => f244 ((53/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (228879/100))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(244316799719039/50000000000000),(-627123455343/50000000000000),(-119755559/50000000000000),(-31320923/50000000000000)⟩
def e245 : ℝ := (5785773/50000000000000)
theorem h245 : Model (fun x => f245 ((53/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(477/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((53/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(40969/1600),(413/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((53/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(74569/1600),(413/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((53/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(17689/1600),(133/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((53/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(1319051041/2560000),(8611617/640000),(155987/1280000),(273/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((53/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((53/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(77841/160),(837/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((53/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(513868013/250000000000),(-884074001/20000000000000),(7129629/10000000000000),(-102217/10000000000000)⟩
def e253 : ℝ := (7083/50000000000000)
theorem h253 : Model (fun x => f253 ((53/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (38079/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(52954541990957/50000000000000),(7627450987/1562500000000),(461148079/20000000000000),(-4587109/25000000000000)⟩
def e254 : ℝ := (7309547/50000000000000)
theorem h254 : Model (fun x => f254 ((53/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(102954541990957/50000000000000),(7627450987/1562500000000),(461148079/20000000000000),(-4587109/25000000000000)⟩
def e255 : ℝ := (7309547/50000000000000)
theorem h255 : Model (fun x => f255 ((53/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(102954541990957/100000000000000),(7627450987/3125000000000),(1152870197/100000000000000),(-4587109/50000000000000)⟩
def e256 : ℝ := (1827387/25000000000000)
theorem h256 : Model (fun x => f256 ((53/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(2954541990957/100000000000000),(7627450987/3125000000000),(1152870197/100000000000000),(-4587109/50000000000000)⟩
def e257 : ℝ := (1827387/25000000000000)
theorem h257 : Model (fun x => f257 ((53/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(379951285919007/100000000000000),(900765640369/100000000000000),(1063660003/25000000000000),(-16928617/50000000000000)⟩
def e258 : ℝ := (6743929/25000000000000)
theorem h258 : Model (fun x => f258 ((53/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(683916392908323/25000000000000),(900765640369/100000000000000),(1063660003/25000000000000),(-16928617/50000000000000)⟩
def e259 : ℝ := (26975717/100000000000000)
theorem h259 : Model (fun x => f259 ((53/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(2816491959679351/100000000000000),(7604548760079/100000000000000),(38117592849/100000000000000),(-265064167/100000000000000)⟩
def e260 : ℝ := (5699671/2500000000000)
theorem h260 : Model (fun x => f260 ((53/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(8098872912060303/100000000000000),(7604548760079/100000000000000),(38117592849/100000000000000),(-265064167/100000000000000)⟩
def e261 : ℝ := (227986841/100000000000000)
theorem h261 : Model (fun x => f261 ((53/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4169078756520683/50000000000000),(6899207581539/25000000000000),(75587174287/50000000000000),(-835196457/100000000000000)⟩
def e262 : ℝ := (828743363/100000000000000)
theorem h262 : Model (fun x => f262 ((53/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(2721441026417797/20000000000000),(6899207581539/25000000000000),(75587174287/50000000000000),(-835196457/100000000000000)⟩
def e263 : ℝ := (207185841/25000000000000)
theorem h263 : Model (fun x => f263 ((53/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(14009235721512209/100000000000000),(12324888627027/20000000000000),(379872181421/100000000000000),(-1421087739/100000000000000)⟩
def e264 : ℝ := (231845747/12500000000000)
theorem h264 : Model (fun x => f264 ((53/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(8172475003613247/50000000000000),(12324888627027/20000000000000),(379872181421/100000000000000),(-1421087739/100000000000000)⟩
def e265 : ℝ := (1854765977/100000000000000)
theorem h265 : Model (fun x => f265 ((53/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(16827868418590929/100000000000000),(103339660805083/100000000000000),(729943696157/100000000000000),(-662479909/50000000000000)⟩
def e266 : ℝ := (1559091479/50000000000000)
theorem h266 : Model (fun x => f266 ((53/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(17230249370971881/100000000000000),(103339660805083/100000000000000),(729943696157/100000000000000),(-662479909/50000000000000)⟩
def e267 : ℝ := (3118182959/100000000000000)
theorem h267 : Model (fun x => f267 ((53/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(17739324323783849/100000000000000),(148448196899561/100000000000000),(601191211167/50000000000000),(7040081/25000000000000)⟩
def e268 : ℝ := (4489400331/100000000000000)
theorem h268 : Model (fun x => f268 ((53/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(17721705276164801/100000000000000),(148448196899561/100000000000000),(601191211167/50000000000000),(7040081/25000000000000)⟩
def e269 : ℝ := (1122350083/25000000000000)
theorem h269 : Model (fun x => f269 ((53/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(4561325125015683/25000000000000),(196089021499779/100000000000000),(180454560513/10000000000000),(609867127/20000000000000)⟩
def e270 : ℝ := (593978871/10000000000000)
theorem h270 : Model (fun x => f270 ((53/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(3649726766679213/20000000000000),(196089021499779/100000000000000),(180454560513/10000000000000),(609867127/20000000000000)⟩
def e271 : ℝ := (5939788711/100000000000000)
theorem h271 : Model (fun x => f271 ((53/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(67395443672959/12500000000000),(50334511725927/100000000000000),(742310126659/100000000000000),(101621659/2000000000000)⟩
def e272 : ℝ := (309761327/20000000000000)
theorem h272 : Model (fun x => f272 ((53/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(105996377165677/100000000000000),(31411228917/6250000000000),(2969607269/100000000000000),(-6631367/50000000000000)⟩
def e273 : ℝ := (1889823/12500000000000)
theorem h273 : Model (fun x => f273 ((53/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(202954541990957/100000000000000),(7627450987/3125000000000),(1152870197/100000000000000),(-4587109/50000000000000)⟩
def e274 : ℝ := (1827387/25000000000000)
theorem h274 : Model (fun x => f274 ((53/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(411905461147591/100000000000000),(12384206573/1250000000000),(5275347663/100000000000000),(-3161117/10000000000000)⟩
def e275 : ℝ := (371721/1250000000000)
theorem h275 : Model (fun x => f275 ((53/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(104497605263479/12500000000000),(3016117167533/100000000000000),(8936733581/50000000000000),(-77647519/100000000000000)⟩
def e276 : ℝ := (45358111/50000000000000)
theorem h276 : Model (fun x => f276 ((53/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(339332217846419/20000000000000),(2040448927759/25000000000000),(426195831/800000000000),(-77943339/50000000000000)⟩
def e277 : ℝ := (245926083/100000000000000)
theorem h277 : Model (fun x => f277 ((53/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(359679857473147/20000000000000),(17178281344311/100000000000000),(2957454279/2000000000000),(7491381/6250000000000)⟩
def e278 : ℝ := (10399297/2000000000000)
theorem h278 : Model (fun x => f278 ((53/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(102954541990957/12500000000000),(7627450987/390625000000),(1152870197/12500000000000),(-4587109/6250000000000)⟩
def e279 : ℝ := (1827387/3125000000000)
theorem h279 : Model (fun x => f279 ((53/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(929632713093333/100000000000000),(153450444709/6250000000000),(2438513769/20000000000000),(-43328239/50000000000000)⟩
def e280 : ℝ := (9199371/12500000000000)
theorem h280 : Model (fun x => f280 ((53/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1029632713093333/100000000000000),(153450444709/6250000000000),(2438513769/20000000000000),(-43328239/50000000000000)⟩
def e281 : ℝ := (9199371/12500000000000)
theorem h281 : Model (fun x => f281 ((53/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(18516907374754983/100000000000000),(110513815766967/50000000000000),(2163579293647/100000000000000),(2700382521/50000000000000)⟩
def e282 : ℝ := (6709041167/100000000000000)
theorem h282 : Model (fun x => f282 ((53/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(540046985039/100000000000000),(-1611571841/25000000000000),(6922677/50000000000000),(430427/100000000000000)⟩
def e283 : ℝ := (10271/5000000000000)
theorem h283 : Model (fun x => f283 ((53/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (18293704054121193/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(23293891943/800000000000),(118536990627/50000000000000),(838765291/100000000000000),(-1390189/12500000000000)⟩
def e284 : ℝ := (4844433/50000000000000)
theorem h284 : Model (fun x => f284 ((53/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(52954541990957/25000000000000),(7627450987/781250000000),(461148079/10000000000000),(-4587109/12500000000000)⟩
def e285 : ℝ := (7309547/25000000000000)
theorem h285 : Model (fun x => f285 ((53/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(48565123046627/100000000000000),(-11513527071/10000000000000),(-135434757/50000000000000),(3129519/50000000000000)⟩
def e286 : ℝ := (3486679/100000000000000)
theorem h286 : Model (fun x => f286 ((53/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (205418588410821/100000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(12858719238343/12500000000000),(115135270709/50000000000000),(270869513/50000000000000),(-12518079/100000000000000)⟩
def e287 : ℝ := (21744189/100000000000000)
theorem h287 : Model (fun x => f287 ((53/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(358719238343/12500000000000),(115135270709/50000000000000),(270869513/50000000000000),(-12518079/100000000000000)⟩
def e288 : ℝ := (21744189/100000000000000)
theorem h288 : Model (fun x => f288 ((53/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(379638377512983/100000000000000),(849807950471/100000000000000),(62477343/3125000000000),(-46197673/100000000000000)⟩
def e289 : ℝ := (16049283/20000000000000)
theorem h289 : Model (fun x => f289 ((53/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(683838165806817/25000000000000),(849807950471/100000000000000),(62477343/3125000000000),(-46197673/100000000000000)⟩
def e290 : ℝ := (5015401/6250000000000)
theorem h290 : Model (fun x => f290 ((53/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(1406925276571729/50000000000000),(3586453367317/50000000000000),(18831979491/100000000000000),(-190364779/50000000000000)⟩
def e291 : ℝ := (84737807/12500000000000)
theorem h291 : Model (fun x => f291 ((53/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(809623150552441/10000000000000),(3586453367317/50000000000000),(18831979491/100000000000000),(-190364779/50000000000000)⟩
def e292 : ℝ := (677902457/100000000000000)
theorem h292 : Model (fun x => f292 ((53/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(1665714685090647/20000000000000),(3252748453513/12500000000000),(9968743479/12500000000000),(-8268283/625000000000)⟩
def e293 : ℝ := (30782779/1250000000000)
theorem h293 : Model (fun x => f293 ((53/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(6798810522250427/50000000000000),(3252748453513/12500000000000),(9968743479/12500000000000),(-8268283/625000000000)⟩
def e294 : ℝ := (2462622321/100000000000000)
theorem h294 : Model (fun x => f294 ((53/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(13987839305649661/100000000000000),(58080070233813/100000000000000),(5390579167/2500000000000),(-1369219513/50000000000000)⟩
def e295 : ℝ := (68840447/1250000000000)
theorem h295 : Model (fun x => f295 ((53/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(8161776795681973/50000000000000),(58080070233813/100000000000000),(5390579167/2500000000000),(-1369219513/50000000000000)⟩
def e296 : ℝ := (5507235761/100000000000000)
theorem h296 : Model (fun x => f296 ((53/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(16791999408271563/100000000000000),(48667580275939/50000000000000),(443983373347/100000000000000),(-4049261781/100000000000000)⟩
def e297 : ℝ := (2313136097/25000000000000)
theorem h297 : Model (fun x => f297 ((53/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(3438876072130503/20000000000000),(48667580275939/50000000000000),(443983373347/100000000000000),(-4049261781/100000000000000)⟩
def e298 : ℝ := (9252544389/100000000000000)
theorem h298 : Model (fun x => f298 ((53/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(17687816762792763/100000000000000),(27944406574879/20000000000000),(387003736717/50000000000000),(-2384103139/50000000000000)⟩
def e299 : ℝ := (13318651089/100000000000000)
theorem h299 : Model (fun x => f299 ((53/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(3534039543034743/20000000000000),(27944406574879/20000000000000),(387003736717/50000000000000),(-2384103139/50000000000000)⟩
def e300 : ℝ := (1331865109/10000000000000)
theorem h300 : Model (fun x => f300 ((53/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(18177288904434301/100000000000000),(184420971319751/100000000000000),(242736924343/20000000000000),(-2288885697/50000000000000)⟩
def e301 : ℝ := (3525760341/20000000000000)
theorem h301 : Model (fun x => f301 ((53/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(9090311118883817/50000000000000),(184420971319751/100000000000000),(242736924343/20000000000000),(-2288885697/50000000000000)⟩
def e302 : ℝ := (8814400853/50000000000000)
theorem h302 : Model (fun x => f302 ((53/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(104347823387741/20000000000000),(11789261322343/25000000000000),(22319538273/4000000000000),(277320619/20000000000000)⟩
def e303 : ℝ := (913484567/20000000000000)
theorem h303 : Model (fun x => f303 ((53/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(5291093134417/5000000000000),(59219684819/12500000000000),(411204107/25000000000000),(-2907463/12500000000000)⟩
def e304 : ℝ := (4489163/10000000000000)
theorem h304 : Model (fun x => f304 ((53/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(25358719238343/12500000000000),(115135270709/50000000000000),(270869513/50000000000000),(-12518079/100000000000000)⟩
def e305 : ℝ := (21744189/100000000000000)
theorem h305 : Model (fun x => f305 ((53/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(102890342625457/25000000000000),(233574640347/25000000000000),(34103681/1250000000000),(-24147931/50000000000000)⟩
def e306 : ℝ := (11047501/12500000000000)
theorem h306 : Model (fun x => f306 ((53/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(834933539512281/100000000000000),(2843113788363/100000000000000),(9915887213/100000000000000),(-34538339/25000000000000)⟩
def e307 : ℝ := (269408767/100000000000000)
theorem h307 : Model (fun x => f307 ((53/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1693827616893431/100000000000000),(961302990957/12500000000000),(7796587581/25000000000000),(-34655339/10000000000000)⟩
def e308 : ℝ := (72996307/10000000000000)
theorem h308 : Model (fun x => f308 ((53/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(448109983731537/25000000000000),(16162784857687/100000000000000),(97296290211/100000000000000),(-1520211/312500000000)⟩
def e309 : ℝ := (771357643/50000000000000)
theorem h309 : Model (fun x => f309 ((53/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(12858719238343/1562500000000),(115135270709/6250000000000),(270869513/6250000000000),(-12518079/12500000000000)⟩
def e310 : ℝ := (21744189/12500000000000)
theorem h310 : Model (fun x => f310 ((53/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(232194973485573/25000000000000),(289490226237/12500000000000),(1494682159/25000000000000),(-7712771/6250000000000)⟩
def e311 : ℝ := (109422571/50000000000000)
theorem h311 : Model (fun x => f311 ((53/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(257194973485573/25000000000000),(289490226237/12500000000000),(1494682159/25000000000000),(-7712771/6250000000000)⟩
def e312 : ℝ := (109422571/50000000000000)
theorem h312 : Model (fun x => f312 ((53/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(18440261661512513/100000000000000),(207790988299273/100000000000000),(37061181263/2500000000000),(-799398717/20000000000000)⟩
def e313 : ℝ := (248634599/1250000000000)
theorem h313 : Model (fun x => f313 ((53/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(542291654183/100000000000000),(-3055361167/50000000000000),(25261803/100000000000000),(324137/100000000000000)⟩
def e314 : ℝ := (60547/10000000000000)
theorem h314 : Model (fun x => f314 ((53/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (3646192867640243/20000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1414673843883/50000000000000),(223846692219/100000000000000),(138044721/50000000000000),(-12973823/100000000000000)⟩
def e315 : ℝ := (28708179/100000000000000)
theorem h315 : Model (fun x => f315 ((53/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(5741084180641/100000000000000),(460920673473/100000000000000),(1114854733/100000000000000),(-4819067/20000000000000)⟩
def e316 : ℝ := (7679409/20000000000000)
theorem h316 : Model (fun x => f316 ((53/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(7013216569659/25000000000000),(2180205906369/100000000000000),(-347279033/100000000000000),(-34105303/25000000000000)⟩
def e317 : ℝ := (188831851/100000000000000)
theorem h317 : Model (fun x => f317 ((53/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(21171974549913/100000000000000),(622983600989/50000000000000),(-5942728129/25000000000000),(345548377/100000000000000)⟩
def e318 : ℝ := (157441291/100000000000000)
theorem h318 : Model (fun x => f318 ((53/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-28437881767357/50000000000000),(-295350761979/10000000000000),(19720457063/25000000000000),(-433888451/25000000000000)⟩
def e319 : ℝ := (286335361/100000000000000)
theorem h319 : Model (fun x => f319 ((53/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((53/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-30899/1600),(-583/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((53/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((53/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(5141/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((53/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(174741/1600),(1357/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((53/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((53/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(347541/1600),(1357/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((53/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(1737705/32),(6785/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((53/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((53/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(178524150685306333/20000000000000),(1532612128532049/25000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (29009/25000000000000)
theorem h329 : Model (fun x => f329 ((53/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(5601483027/50000000000000),(-76941083/100000000000000),(275653/25000000000000),(-11517/100000000000000)⟩
def e330 : ℝ := (7/5000000000000)
theorem h330 : Model (fun x => f330 ((53/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (221611138824127589/25000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(152089454116141/25000000000000),(114520904489/20000000000000),(799252363/10000000000000),(-25592003/100000000000000)⟩
def e331 : ℝ := (14460909/100000000000000)
theorem h331 : Model (fun x => f331 ((53/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((53/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(413/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((53/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((53/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((53/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(515806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((53/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((53/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((53/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1144185979375807/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (51/5000000000000)
theorem h339 : Model (fun x => f339 ((53/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3614193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((53/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((53/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((53/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2036628041248127/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1019/100000000000000)
theorem h343 : Model (fun x => f343 ((53/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2455038376539/50000000000000),(-849096239/12500000000000),(1174669/12500000000000),(-13001/100000000000000)⟩
def e344 : ℝ := (23/100000000000000)
theorem h344 : Model (fun x => f344 ((53/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2033810499612627/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(56180409785309/50000000000000),(933731889577/100000000000000),(-129175699/10000000000000),(446763/25000000000000)⟩
def e345 : ℝ := (867/25000000000000)
theorem h345 : Model (fun x => f345 ((53/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(106180409785309/50000000000000),(933731889577/100000000000000),(-129175699/10000000000000),(446763/25000000000000)⟩
def e346 : ℝ := (867/25000000000000)
theorem h346 : Model (fun x => f346 ((53/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(106180409785309/100000000000000),(116716486197/25000000000000),(-129175699/20000000000000),(446763/50000000000000)⟩
def e347 : ℝ := (347/20000000000000)
theorem h347 : Model (fun x => f347 ((53/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(6180409785309/100000000000000),(116716486197/25000000000000),(-129175699/20000000000000),(446763/50000000000000)⟩
def e348 : ℝ := (347/20000000000000)
theorem h348 : Model (fun x => f348 ((53/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(391856274207687/100000000000000),(215369706673/12500000000000),(-297949901/12500000000000),(12881/390625000000)⟩
def e349 : ℝ := (1281/20000000000000)
theorem h349 : Model (fun x => f349 ((53/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(686892639980493/25000000000000),(215369706673/12500000000000),(-297949901/12500000000000),(12881/390625000000)⟩
def e350 : ℝ := (3203/50000000000000)
theorem h350 : Model (fun x => f350 ((53/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1458690839832829/50000000000000),(14656914750087/100000000000000),(-6116490131/50000000000000),(181099/3125000000000)⟩
def e351 : ℝ := (100763/100000000000000)
theorem h351 : Model (fun x => f351 ((53/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(819976263204661/10000000000000),(14656914750087/100000000000000),(-6116490131/50000000000000),(181099/3125000000000)⟩
def e352 : ℝ := (25191/25000000000000)
theorem h352 : Model (fun x => f352 ((53/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(8706541564129729/100000000000000),(53844671426003/100000000000000),(154913217/6250000000000),(-4522321/6250000000000)⟩
def e353 : ℝ := (243581/50000000000000)
theorem h353 : Model (fun x => f353 ((53/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(3493897295794337/25000000000000),(53844671426003/100000000000000),(154913217/6250000000000),(-4522321/6250000000000)⟩
def e354 : ℝ := (487163/100000000000000)
theorem h354 : Model (fun x => f354 ((53/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(7419668932304513/50000000000000),(122419759247413/100000000000000),(32749781741/20000000000000),(-144076471/50000000000000)⟩
def e355 : ℝ := (3563/400000000000)
theorem h355 : Model (fun x => f355 ((53/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(17175052150323311/100000000000000),(122419759247413/100000000000000),(32749781741/20000000000000),(-144076471/50000000000000)⟩
def e356 : ℝ := (890751/100000000000000)
theorem h356 : Model (fun x => f356 ((53/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(2279567594256727/12500000000000),(21017027151653/10000000000000),(126895091911/20000000000000),(-44673357/25000000000000)⟩
def e357 : ℝ := (1281233/50000000000000)
theorem h357 : Model (fun x => f357 ((53/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(1164932606652173/6250000000000),(21017027151653/10000000000000),(126895091911/20000000000000),(-44673357/25000000000000)⟩
def e358 : ℝ := (2562467/100000000000000)
theorem h358 : Model (fun x => f358 ((53/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(3958176689491069/20000000000000),(31017843346619/10000000000000),(38362931993/2500000000000),(1581511459/100000000000000)⟩
def e359 : ℝ := (6120961/100000000000000)
theorem h359 : Model (fun x => f359 ((53/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(19773264399836297/100000000000000),(31017843346619/10000000000000),(38362931993/2500000000000),(1581511459/100000000000000)⟩
def e360 : ℝ := (3060481/50000000000000)
theorem h360 : Model (fun x => f360 ((53/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(52488332919197/250000000000),(421663369375777/100000000000000),(589952589449/20000000000000),(1754174351/25000000000000)⟩
def e361 : ℝ := (7123813/100000000000000)
theorem h361 : Model (fun x => f361 ((53/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(20998666501012133/100000000000000),(421663369375777/100000000000000),(589952589449/20000000000000),(1754174351/25000000000000)⟩
def e362 : ℝ := (3561907/50000000000000)
theorem h362 : Model (fun x => f362 ((53/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(324450909803239/25000000000000),(24819229378959/20000000000000),(2015284239929/100000000000000),(5834647413/50000000000000)⟩
def e363 : ℝ := (3667733/20000000000000)
theorem h363 : Model (fun x => f363 ((53/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(112742794221761/100000000000000),(991440346647/100000000000000),(404022619/50000000000000),(-165331/4000000000000)⟩
def e364 : ℝ := (1623/10000000000000)
theorem h364 : Model (fun x => f364 ((53/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(206180409785309/100000000000000),(116716486197/25000000000000),(-129175699/20000000000000),(446763/50000000000000)⟩
def e365 : ℝ := (347/20000000000000)
theorem h365 : Model (fun x => f365 ((53/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(425103613792379/100000000000000),(1925172236223/100000000000000),(-60463969/12500000000000),(-2346223/100000000000000)⟩
def e366 : ℝ := (197/1000000000000)
theorem h366 : Model (fun x => f366 ((53/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(219120093232321/25000000000000),(5953992008577/100000000000000),(2622500927/50000000000000),(-39329/250000000000)⟩
def e367 : ℝ := (57503/100000000000000)
theorem h367 : Model (fun x => f367 ((53/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(903565412296701/50000000000000),(8183976747913/50000000000000),(32950329117/100000000000000),(-9643081/25000000000000)⟩
def e368 : ℝ := (188411/100000000000000)
theorem h368 : Model (fun x => f368 ((53/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(2037409786889351/100000000000000),(18185156119913/50000000000000),(107015025601/50000000000000),(340762123/100000000000000)⟩
def e369 : ℝ := (1304627/100000000000000)
theorem h369 : Model (fun x => f369 ((53/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(106180409785309/12500000000000),(116716486197/3125000000000),(-129175699/2500000000000),(446763/6250000000000)⟩
def e370 : ℝ := (347/2500000000000)
theorem h370 : Model (fun x => f370 ((53/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(962186072504233/100000000000000),(4726367904951/100000000000000),(-2179491361/50000000000000),(3014933/100000000000000)⟩
def e371 : ℝ := (3011/10000000000000)
theorem h371 : Model (fun x => f371 ((53/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(1062186072504233/100000000000000),(4726367904951/100000000000000),(-2179491361/50000000000000),(3014933/100000000000000)⟩
def e372 : ℝ := (3011/10000000000000)
theorem h372 : Model (fun x => f372 ((53/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(1082054149808843/5000000000000),(241307936698801/50000000000000),(487947727361/12500000000000),(12211426371/100000000000000)⟩
def e373 : ℝ := (11212429/50000000000000)
theorem h373 : Model (fun x => f373 ((53/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(115521020849/25000000000000),(-515244809/5000000000000),(146458633/100000000000000),(-834061/50000000000000)⟩
def e374 : ℝ := (17707/100000000000000)
theorem h374 : Model (fun x => f374 ((53/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (21154551307109141/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(5996944050537/100000000000000),(439691225267/100000000000000),(-393731481/25000000000000),(6349577/100000000000000)⟩
def e375 : ℝ := (676541/100000000000000)
theorem h375 : Model (fun x => f375 ((53/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(56180409785309/25000000000000),(933731889577/50000000000000),(-129175699/5000000000000),(446763/12500000000000)⟩
def e376 : ℝ := (867/12500000000000)
theorem h376 : Model (fun x => f376 ((53/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(47089665693603/100000000000000),(-207049128067/100000000000000),(299203943/25000000000000),(-6918009/100000000000000)⟩
def e377 : ℝ := (20223/50000000000000)
theorem h377 : Model (fun x => f377 ((53/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (211425794133531/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(13227583576599/12500000000000),(103524564033/25000000000000),(-598407887/25000000000000),(6918007/50000000000000)⟩
def e378 : ℝ := (32833/12500000000000)
theorem h378 : Model (fun x => f378 ((53/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(727583576599/12500000000000),(103524564033/25000000000000),(-598407887/25000000000000),(6918007/50000000000000)⟩
def e379 : ℝ := (32833/12500000000000)
theorem h379 : Model (fun x => f379 ((53/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(19526432898789/5000000000000),(382054938693/25000000000000),(-8833640237/100000000000000),(1276537/2500000000000)⟩
def e380 : ℝ := (969357/100000000000000)
theorem h380 : Model (fun x => f380 ((53/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(549248588738013/20000000000000),(382054938693/25000000000000),(-8833640237/100000000000000),(1276537/2500000000000)⟩
def e381 : ℝ := (484679/50000000000000)
theorem h381 : Model (fun x => f381 ((53/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(2906092644744447/100000000000000),(12989316501341/100000000000000),(-68754423293/100000000000000),(360844257/100000000000000)⟩
def e382 : ℝ := (2221009/25000000000000)
theorem h382 : Model (fun x => f382 ((53/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8188473597125399/100000000000000),(12989316501341/100000000000000),(-68754423293/100000000000000),(360844257/100000000000000)⟩
def e383 : ℝ := (8884037/100000000000000)
theorem h383 : Model (fun x => f383 ((53/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(8665097509660037/100000000000000),(11913426984869/25000000000000),(-42993948927/20000000000000),(919178913/100000000000000)⟩
def e384 : ℝ := (7187201/20000000000000)
theorem h384 : Model (fun x => f384 ((53/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(1741768141088457/12500000000000),(11913426984869/25000000000000),(-42993948927/20000000000000),(919178913/100000000000000)⟩
def e385 : ℝ := (17968003/50000000000000)
theorem h385 : Model (fun x => f385 ((53/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(14745205540675227/100000000000000),(108128524345221/100000000000000),(-181840670637/50000000000000),(869771391/100000000000000)⟩
def e386 : ℝ := (90500253/100000000000000)
theorem h386 : Model (fun x => f386 ((53/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(2135114978298689/12500000000000),(108128524345221/100000000000000),(-181840670637/50000000000000),(869771391/100000000000000)⟩
def e387 : ℝ := (45250127/50000000000000)
theorem h387 : Model (fun x => f387 ((53/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(4518785891375083/25000000000000),(92577059277821/50000000000000),(-69189195783/20000000000000),(-202620051/25000000000000)⟩
def e388 : ℝ := (3372683/2000000000000)
theorem h388 : Model (fun x => f388 ((53/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(4619381129470321/25000000000000),(92577059277821/50000000000000),(-69189195783/20000000000000),(-202620051/25000000000000)⟩
def e389 : ℝ := (168634151/100000000000000)
theorem h389 : Model (fun x => f389 ((53/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(9776519993957273/50000000000000),(272446433024611/100000000000000),(-41646227981/100000000000000),(-260347897/6250000000000)⟩
def e390 : ℝ := (129372111/50000000000000)
theorem h390 : Model (fun x => f390 ((53/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(9767710470147749/50000000000000),(272446433024611/100000000000000),(-41646227981/100000000000000),(-260347897/6250000000000)⟩
def e391 : ℝ := (258744223/100000000000000)
theorem h391 : Model (fun x => f391 ((53/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(20672513055344073/100000000000000),(73840094896031/20000000000000),(123303922497/20000000000000),(-4199463333/50000000000000)⟩
def e392 : ℝ := (348448381/100000000000000)
theorem h392 : Model (fun x => f392 ((53/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(10337923194338703/50000000000000),(73840094896031/20000000000000),(123303922497/20000000000000),(-4199463333/50000000000000)⟩
def e393 : ℝ := (174224191/50000000000000)
theorem h393 : Model (fun x => f393 ((53/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(1203472501174833/100000000000000),(107108255472389/100000000000000),(1069834708053/100000000000000),(-978115689/25000000000000)⟩
def e394 : ℝ := (2463933/3125000000000)
theorem h394 : Model (fun x => f394 ((53/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(111980139056583/100000000000000),(175280617341/20000000000000),(-10472313/312500000000),(147793/1562500000000)⟩
def e395 : ℝ := (182661/25000000000000)
theorem h395 : Model (fun x => f395 ((53/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(25727583576599/12500000000000),(103524564033/25000000000000),(-598407887/25000000000000),(6918007/50000000000000)⟩
def e396 : ℝ := (32833/12500000000000)
theorem h396 : Model (fun x => f396 ((53/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(423621476282167/100000000000000),(1704599598969/100000000000000),(-1017300407/12500000000000),(1856539/5000000000000)⟩
def e397 : ℝ := (313993/25000000000000)
theorem h397 : Model (fun x => f397 ((53/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(108987569358917/12500000000000),(2631313718827/50000000000000),(-19831736083/100000000000000),(30266163/50000000000000)⟩
def e398 : ℝ := (4293913/100000000000000)
theorem h398 : Model (fun x => f398 ((53/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(1794551551674827/100000000000000),(14442099971707/100000000000000),(-39895450107/100000000000000),(37133537/100000000000000)⟩
def e399 : ℝ := (788587/6250000000000)
theorem h399 : Model (fun x => f399 ((53/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(2009541323007539/100000000000000),(15949894411199/50000000000000),(21758091689/100000000000000),(-311147801/50000000000000)⟩
def e400 : ℝ := (30491031/100000000000000)
theorem h400 : Model (fun x => f400 ((53/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(13227583576599/1562500000000),(103524564033/3125000000000),(-598407887/3125000000000),(6918007/6250000000000)⟩
def e401 : ℝ := (32833/1562500000000)
theorem h401 : Model (fun x => f401 ((53/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(958545487958919/100000000000000),(4189189135761/100000000000000),(-703131017/3125000000000),(7509179/6250000000000)⟩
def e402 : ℝ := (707989/25000000000000)
theorem h402 : Model (fun x => f402 ((53/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(1058545487958919/100000000000000),(4189189135761/100000000000000),(-703131017/3125000000000),(7509179/6250000000000)⟩
def e403 : ℝ := (707989/25000000000000)
theorem h403 : Model (fun x => f403 ((53/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(2127190900336627/10000000000000),(421857262029977/100000000000000),(111451111859/10000000000000),(-1043890743/10000000000000)⟩
def e404 : ℝ := (389387759/100000000000000)
theorem h404 : Model (fun x => f404 ((53/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(18804142117/4000000000000),(-9322933719/100000000000000),(160258849/100000000000000),(-2459041/100000000000000)⟩
def e405 : ℝ := (22847/50000000000000)
theorem h405 : Model (fun x => f405 ((53/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (10424463200961257/50000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(2828783493249/50000000000000),(9783019271/2500000000000),(-1513814757/50000000000000),(93453/390625000000)⟩
def e406 : ℝ := (782367/50000000000000)
theorem h406 : Model (fun x => f406 ((53/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2330902207407/20000000000000),(831011996107/100000000000000),(-2301277719/50000000000000),(6054709/20000000000000)⟩
def e407 : ℝ := (89651/4000000000000)
theorem h407 : Model (fun x => f407 ((53/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(70901128864527/100000000000000),(2561130345671/50000000000000),(-2788762993/12500000000000),(55313311/25000000000000)⟩
def e408 : ℝ := (15864967/100000000000000)
theorem h408 : Model (fun x => f408 ((53/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(53510285935491/100000000000000),(1428114544511/50000000000000),(-14145785837/20000000000000),(1501491677/100000000000000)⟩
def e409 : ℝ := (54902747/100000000000000)
theorem h409 : Model (fun x => f409 ((53/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-3365477599223/100000000000000),(-6079908173/6250000000000),(8152899067/100000000000000),(-234062127/100000000000000)⟩
def e410 : ℝ := (85309527/25000000000000)
theorem h410 : Model (fun x => f410 ((53/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(44788496887207/6250000000000),(15447442626953/25000000000000),(216293/10240000),(3657/10240000)⟩
def e411 : ℝ := (149414063/50000000000000)
theorem h411 : Model (fun x => f411 ((53/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(29929/1600),(173/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((53/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(5177717/64000),(89787/64000),(519/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((53/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(57975540434334691/100000000000000),(3002130793004557/50000000000000),(16461331784069/6250000000000),(79560177919/1250000000000)⟩
def e414 : ℝ := (23279337557/25000000000000)
theorem h414 : Model (fun x => f414 ((53/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(86243266773/50000000000000),(-3572728291/20000000000000),(266613501/25000000000000),(-48230069/100000000000000)⟩
def e415 : ℝ := (2213/78125000000)
theorem h415 : Model (fun x => f415 ((53/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (2068057584327869/4000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(3945266323263/100000000000000),(169810315553/100000000000000),(-3459677323/50000000000000),(184485271/100000000000000)⟩
def e416 : ℝ := (142766337/100000000000000)
theorem h416 : Model (fun x => f416 ((53/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(14494718101/2500000000000),(14506356957/20000000000000),(1233544421/100000000000000),(-6197107/12500000000000)⟩
def e417 : ℝ := (96800889/20000000000000)
theorem h417 : Model (fun x => f417 ((53/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((53/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((869573851603/3000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (13/10) (27/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (13/10) (27/20) ≤ (435512932469/1500000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(53/40)-(1/40)) (by norm_num : ((53/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel6

