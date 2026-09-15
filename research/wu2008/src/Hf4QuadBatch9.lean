import Hf4QuadDag


noncomputable section
namespace Hf4Quad.Panel28
open Hf4Quad.Dag

def p0 : Cubic := ⟨(97/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((97/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((97/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((97/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((97/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(21247619047619/5000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((97/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-21247619047619/5000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((97/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-333523809523809/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((97/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((97/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(9409/1600),(97/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((97/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(711897883597883/100000000000000),(7339153439153/50000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((97/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-711897883597883/100000000000000),(-7339153439153/50000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((97/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-261355423280423/25000000000000),(-9529629629629/50000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((97/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((97/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(912673/64000),(28227/64000),(291/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((97/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(1736679923683449/12500000000000),(429694001736111/100000000000000),(1107458767361/25000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (3/100000000000000)
theorem h14 : Model (fun x => f14 ((97/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-1736679923683449/12500000000000),(-429694001736111/100000000000000),(-1107458767361/25000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (3/100000000000000)
theorem h15 : Model (fun x => f15 ((97/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-3734715270647321/25000000000000),(-448753260995369/100000000000000),(-901099289021/20000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (1/12500000000000)
theorem h16 : Model (fun x => f16 ((97/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((97/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(88529281/2560000),(912673/640000),(28227/1280000),(97/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((97/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(9660933442460317/100000000000000),(398389007936507/100000000000000),(385040922619/6250000000000),(42341269841/100000000000000)⟩
def e19 : ℝ := (109126987/100000000000000)
theorem h19 : Model (fun x => f19 ((97/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-5277927640128967/100000000000000),(-25182126529431/50000000000000),(1655158316799/100000000000000),(6779617229/25000000000000)⟩
def e20 : ℝ := (21825399/20000000000000)
theorem h20 : Model (fun x => f20 ((97/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((97/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(4193037234863281/50000000000000),(108067969970703/25000000000000),(912673/10240000),(9409/10240000)⟩
def e22 : ℝ := (14831543/3125000000000)
theorem h22 : Model (fun x => f22 ((97/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(27316861096757449/50000000000000),(2816171247088393/100000000000000),(11613077307581/20000000000000),(598612232349/100000000000000)⟩
def e23 : ℝ := (772998049/25000000000000)
theorem h23 : Model (fun x => f23 ((97/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(49355794553385931/100000000000000),(2765806994029531/100000000000000),(3732534053419/6250000000000),(125146140253/20000000000000)⟩
def e24 : ℝ := (3201119191/100000000000000)
theorem h24 : Model (fun x => f24 ((97/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((97/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(317753602954483/1562500000000),(1257911170458983/100000000000000),(3242039099121/10000000000000),(445641113281/100000000000000)⟩
def e26 : ℝ := (1729956057/50000000000000)
theorem h26 : Model (fun x => f26 ((97/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(45665059587346483/100000000000000),(112985714442919/4000000000000),(4550004608687/6250000000000),(1000688298817/100000000000000)⟩
def e27 : ℝ := (485577613/6250000000000)
theorem h27 : Model (fun x => f27 ((97/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(47510427070366207/50000000000000),(2795224927551253/50000000000000),(4141269331053/3125000000000),(813209500041/50000000000000)⟩
def e28 : ℝ := (10970360999/100000000000000)
theorem h28 : Model (fun x => f28 ((97/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((97/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(49315359178535761/100000000000000),(1779420176545103/50000000000000),(55033613707579/50000000000000),(945594737243/50000000000000)⟩
def e30 : ℝ := (9808906257/50000000000000)
theorem h30 : Model (fun x => f30 ((97/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(5851306505707219/50000000000000),(844518464741247/100000000000000),(26119127775501/100000000000000),(448782264183/100000000000000)⟩
def e31 : ℝ := (1163834513/25000000000000)
theorem h31 : Model (fun x => f31 ((97/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(26680866788036713/25000000000000),(6434968319843753/100000000000000),(158639746369197/100000000000000),(415040252853/20000000000000)⟩
def e32 : ℝ := (15625699051/100000000000000)
theorem h32 : Model (fun x => f32 ((97/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((97/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(4036461/320),(41613/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((97/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((97/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(214273/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((97/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(7464829/320),(11857/32),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((97/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((97/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(8194429/320),(11857/32),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((97/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-8194429/320),(-11857/32),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((97/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((97/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(137/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((97/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(18769/1600),(137/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((97/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((97/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(394149/160),(2877/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((97/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(20296892799/50000000000000),(-592610009/100000000000000),(648843/10000000000000),(-15787/25000000000000)⟩
def e46 : ℝ := (591/100000000000000)
theorem h46 : Model (fun x => f46 ((97/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (194187/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-207901808702521/20000000000000),(13404839089/10000000000000),(-49678783/5000000000000),(7369847/100000000000000)⟩
def e47 : ℝ := (30138279/100000000000000)
theorem h47 : Model (fun x => f47 ((97/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((97/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(177/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((97/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((97/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((97/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(73749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((97/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(123749999999999/50000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((97/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((97/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(123749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((97/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((97/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(2598749999999979/100000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((97/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((97/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(23749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((97/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(617203124999969/100000000000000),(12906249999979/100000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (63/50000000000000)
theorem h60 : Model (fun x => f60 ((97/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(153140624999997/100000000000000),(515624999999/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((97/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((97/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(123749999999999/10000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((97/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1390640624999987/100000000000000),(2598958333329/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((97/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1490640624999987/100000000000000),(2598958333329/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((97/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(2300070130004747/25000000000000),(44893501953051/20000000000000),(1225034179679/100000000000000),(132446289/6250000000000)⟩
def e66 : ℝ := (635167/100000000000000)
theorem h66 : Model (fun x => f66 ((97/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(223749999999999/100000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((97/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(100128124999999/20000000000000),(186458333333/10000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((97/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1120183398437483/100000000000000),(6258007812489/100000000000000),(11653645833/100000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (13/20000000000000)
theorem h69 : Model (fun x => f69 ((97/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(103060014994930433/100000000000000),(1545101026495057/50000000000000),(28841991911003/100000000000000),(31806293563/25000000000000)⟩
def e70 : ℝ := (149555683/50000000000000)
theorem h70 : Model (fun x => f70 ((97/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((97/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3215953124999937/12500000000000),(10828124999979/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((97/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(6110310937499623/100000000000000),(4635791015617/3125000000000),(395572916663/50000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (297/20000000000000)
theorem h73 : Model (fun x => f73 ((97/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(8555836089347563/12500000000000),(15969713272019/781250000000),(9428909761997/50000000000000),(80852952717/100000000000000)⟩
def e74 : ℝ := (716801/400000000000)
theorem h74 : Model (fun x => f74 ((97/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(171506703709710937/100000000000000),(2567162675904273/50000000000000),(47699811434997/100000000000000),(208078126969/100000000000000)⟩
def e75 : ℝ := (7473619/1562500000000)
theorem h75 : Model (fun x => f75 ((97/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((97/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1071984374999979/12500000000000),(3609374999993/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((97/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(5640624999999/100000000000000),(98958333333/50000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((97/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1339648437499/100000000000000),(70507812499/100000000000000),(618489583/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((97/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(22977315087873/20000000000000),(3410154418901/50000000000000),(148102484751/100000000000000),(1403266033/100000000000000)⟩
def e80 : ℝ := (1346881/25000000000000)
theorem h80 : Model (fun x => f80 ((97/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(128529356272789/50000000000000),(15739135088911/100000000000000),(359797263121/100000000000000),(751380287/20000000000000)⟩
def e81 : ℝ := (17923981/100000000000000)
theorem h81 : Model (fun x => f81 ((97/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(34352752484451303/20000000000000),(5150064486897457/100000000000000),(24029804349059/50000000000000),(52958757101/25000000000000)⟩
def e82 : ℝ := (496235597/100000000000000)
theorem h82 : Model (fun x => f82 ((97/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(63633300781/20000000000000),(11163736979/50000000000000),(36722819/6250000000000),(3436053/50000000000000)⟩
def e83 : ℝ := (471/1562500000000)
theorem h83 : Model (fun x => f83 ((97/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(75564544677/100000000000000),(6628468831/100000000000000),(232577853/100000000000000),(4080313/100000000000000)⟩
def e84 : ℝ := (35921/100000000000000)
theorem h84 : Model (fun x => f84 ((97/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(112166121/625000000000),(118069601/6250000000000),(4142793/5000000000000),(484537/25000000000000)⟩
def e85 : ℝ := (5137/20000000000000)
theorem h85 : Model (fun x => f85 ((97/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(4262312597/100000000000000),(523441897/100000000000000),(27549573/100000000000000),(402771/50000000000000)⟩
def e86 : ℝ := (14287/100000000000000)
theorem h86 : Model (fun x => f86 ((97/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(12786937791/100000000000000),(1570325691/100000000000000),(82648719/100000000000000),(1208313/50000000000000)⟩
def e87 : ℝ := (42861/100000000000000)
theorem h87 : Model (fun x => f87 ((97/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-12786937791/100000000000000),(-1570325691/100000000000000),(-82648719/100000000000000),(-1208313/50000000000000)⟩
def e88 : ℝ := (42861/100000000000000)
theorem h88 : Model (fun x => f88 ((97/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(42940937408829681/25000000000000),(2575031458285883/50000000000000),(48059526049399/100000000000000),(105916305889/50000000000000)⟩
def e89 : ℝ := (248139229/50000000000000)
theorem h89 : Model (fun x => f89 ((97/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3215953124999937/10000000000000),(10828124999979/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((97/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(2506410354003857/100000000000000),(18669723307259/100000000000000),(52150065103/100000000000000),(16185619/25000000000000)⟩
def e91 : ℝ := (30333/100000000000000)
theorem h91 : Model (fun x => f91 ((97/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(806049821049090227/100000000000000),(11432040424165449/100000000000000),(4146299402247/6250000000000),(201825061093/100000000000000)⟩
def e92 : ℝ := (68090699/20000000000000)
theorem h92 : Model (fun x => f92 ((97/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(12406181031/100000000000000),(-175954339/100000000000000),(1474451/100000000000000),(-9537/100000000000000)⟩
def e93 : ℝ := (67/100000000000000)
theorem h93 : Model (fun x => f93 ((97/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (397275618834487119/50000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(21309321725391/100000000000000),(336700358327/100000000000000),(-113367007/20000000000000),(1271561/100000000000000)⟩
def e94 : ℝ := (337773/100000000000000)
theorem h94 : Model (fun x => f94 ((97/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(73749999999999/25000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((97/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(1010101010101/2500000000000),(-136040540081/100000000000000),(114512239/25000000000000),(-1542253/100000000000000)⟩
def e96 : ℝ := (2607/50000000000000)
theorem h96 : Model (fun x => f96 ((97/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (246666666666659/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(29797979797979/25000000000000),(272081080161/100000000000000),(-183219583/20000000000000),(1542251/50000000000000)⟩
def e97 : ℝ := (2059/5000000000000)
theorem h97 : Model (fun x => f97 ((97/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(625757575757559/25000000000000),(5713702683381/100000000000000),(-3847611243/20000000000000),(32387271/50000000000000)⟩
def e98 : ℝ := (43239/5000000000000)
theorem h98 : Model (fun x => f98 ((97/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(4797979797979/25000000000000),(272081080161/100000000000000),(-183219583/20000000000000),(1542251/50000000000000)⟩
def e99 : ℝ := (2059/5000000000000)
theorem h99 : Model (fun x => f99 ((97/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(480379553106733/100000000000000),(3953420543551/50000000000000),(-11076456643/100000000000000),(-601949/4000000000000)⟩
def e100 : ℝ := (865673/50000000000000)
theorem h100 : Model (fun x => f100 ((97/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(71033568003261/50000000000000),(648597322403/100000000000000),(-180443529/12500000000000),(295987/12500000000000)⟩
def e101 : ℝ := (30907/25000000000000)
theorem h101 : Model (fun x => f101 ((97/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(29797979797979/2500000000000),(272081080161/10000000000000),(-183219583/2000000000000),(1542251/5000000000000)⟩
def e102 : ℝ := (2059/500000000000)
theorem h102 : Model (fun x => f102 ((97/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(666993163962841/50000000000000),(3369408124013/100000000000000),(-5302263691/50000000000000),(8303229/25000000000000)⟩
def e103 : ℝ := (133857/25000000000000)
theorem h103 : Model (fun x => f103 ((97/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(716993163962841/50000000000000),(3369408124013/100000000000000),(-5302263691/50000000000000),(8303229/25000000000000)⟩
def e104 : ℝ := (133857/25000000000000)
theorem h104 : Model (fun x => f104 ((97/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(6888577113701041/100000000000000),(16196120981041/12500000000000),(11327378163/20000000000000),(-31698569/2500000000000)⟩
def e105 : ℝ := (30796003/100000000000000)
theorem h105 : Model (fun x => f105 ((97/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(54797979797979/25000000000000),(272081080161/100000000000000),(-183219583/20000000000000),(1542251/50000000000000)⟩
def e106 : ℝ := (2059/5000000000000)
theorem h106 : Model (fun x => f106 ((97/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(240225487195177/50000000000000),(47710379309/4000000000000),(-1637872031/50000000000000),(85369/1000000000000)⟩
def e107 : ℝ := (51497/25000000000000)
theorem h107 : Model (fun x => f107 ((97/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(1053109711542477/100000000000000),(3921648602293/100000000000000),(-260509211/3125000000000),(1369219/10000000000000)⟩
def e108 : ℝ := (740623/100000000000000)
theorem h108 : Model (fun x => f108 ((97/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(1813606864286953/2500000000000),(102165573228339/6250000000000),(51034361217/1000000000000),(-10494891253/50000000000000)⟩
def e109 : ℝ := (414322893/100000000000000)
theorem h109 : Model (fun x => f109 ((97/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(1491704928068481/6250000000000),(13620543770463/12500000000000),(-3789314109/1562500000000),(6215727/1562500000000)⟩
def e110 : ℝ := (649047/3125000000000)
theorem h110 : Model (fun x => f110 ((97/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(916117774005541/20000000000000),(85850700129071/100000000000000),(31280242501/100000000000000),(-211381793/25000000000000)⟩
def e111 : ℝ := (2574059/12500000000000)
theorem h111 : Model (fun x => f111 ((97/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(4823862623609557/10000000000000),(541868329942343/50000000000000),(3314326663659/100000000000000),(-887950753/6250000000000)⟩
def e112 : ℝ := (138158917/50000000000000)
theorem h112 : Model (fun x => f112 ((97/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(12078290080757369/10000000000000),(271838583153811/10000000000000),(8417762785359/100000000000000),(-17598497277/50000000000000)⟩
def e113 : ℝ := (690640727/100000000000000)
theorem h113 : Model (fun x => f113 ((97/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(497234976022827/6250000000000),(4540181256821/12500000000000),(-1263104703/1562500000000),(2071909/1562500000000)⟩
def e114 : ℝ := (216349/3125000000000)
theorem h114 : Model (fun x => f114 ((97/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(368329762269/10000000000000),(104435162081/100000000000000),(194323799/50000000000000),(-950277/25000000000000)⟩
def e115 : ℝ := (10317/25000000000000)
theorem h115 : Model (fun x => f115 ((97/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(44180968959/6250000000000),(30064667871/100000000000000),(324994637/100000000000000),(-257593/50000000000000)⟩
def e116 : ℝ := (20323/100000000000000)
theorem h116 : Model (fun x => f116 ((97/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(56238906984943/100000000000000),(132431370123/5000000000000),(9051067567/25000000000000),(13422319/25000000000000)⟩
def e117 : ℝ := (52153/2500000000000)
theorem h117 : Model (fun x => f117 ((97/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(123271139552853/100000000000000),(595859266129/10000000000000),(86048045421/100000000000000),(193658193/100000000000000)⟩
def e118 : ℝ := (4707087/100000000000000)
theorem h118 : Model (fun x => f118 ((97/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(120906171947126543/100000000000000),(13621722120997/500000000000),(425190541539/5000000000000),(-35003336361/100000000000000)⟩
def e119 : ℝ := (347673907/50000000000000)
theorem h119 : Model (fun x => f119 ((97/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(135666813773/100000000000000),(1923328921/25000000000000),(68848563/50000000000000),(531757/100000000000000)⟩
def e120 : ℝ := (7727/100000000000000)
theorem h120 : Model (fun x => f120 ((97/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(26037065269/100000000000000),(1845618661/100000000000000),(1441123/3125000000000),(51301/12500000000000)⟩
def e121 : ℝ := (1989/100000000000000)
theorem h121 : Model (fun x => f121 ((97/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(2498506263/50000000000000),(42505157/10000000000000),(13633587/100000000000000),(188133/100000000000000)⟩
def e122 : ℝ := (577/50000000000000)
theorem h122 : Model (fun x => f122 ((97/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(191804521/20000000000000),(95171479/100000000000000),(1863627/50000000000000),(3473/5000000000000)⟩
def e123 : ℝ := (79/12500000000000)
theorem h123 : Model (fun x => f123 ((97/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(575413563/20000000000000),(285514437/100000000000000),(5590881/50000000000000),(10419/5000000000000)⟩
def e124 : ℝ := (237/12500000000000)
theorem h124 : Model (fun x => f124 ((97/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-575413563/20000000000000),(-285514437/100000000000000),(-5590881/50000000000000),(-10419/5000000000000)⟩
def e125 : ℝ := (237/12500000000000)
theorem h125 : Model (fun x => f125 ((97/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(15113271133757341/12500000000000),(2724344138684963/100000000000000),(4251899824509/50000000000000),(-35003544741/100000000000000)⟩
def e126 : ℝ := (69534971/10000000000000)
theorem h126 : Model (fun x => f126 ((97/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(1491704928068481/5000000000000),(13620543770463/10000000000000),(-3789314109/1250000000000),(6215727/1250000000000)⟩
def e127 : ℝ := (649047/2500000000000)
theorem h127 : Model (fun x => f127 ((97/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(461666277585281/20000000000000),(5730624556887/50000000000000),(-1724993669/10000000000000),(1943871/50000000000000)⟩
def e128 : ℝ := (573917/25000000000000)
theorem h128 : Model (fun x => f128 ((97/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(21520933168656093/3125000000000),(6563433227565957/100000000000000),(3466887250751/100000000000000),(-9120266237/20000000000000)⟩
def e129 : ℝ := (1404969149/100000000000000)
theorem h129 : Model (fun x => f129 ((97/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(14520745803/100000000000000),(-138391341/100000000000000),(1245851/100000000000000),(-1277/12500000000000)⟩
def e130 : ℝ := (29/25000000000000)
theorem h130 : Model (fun x => f130 ((97/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (341051457137938967/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2194559683851/12500000000000),(228271418449/100000000000000),(-51456527/5000000000000),(1184549/25000000000000)⟩
def e131 : ℝ := (74121/20000000000000)
theorem h131 : Model (fun x => f131 ((97/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(38865799196199/100000000000000),(70621472097/12500000000000),(-63838623/4000000000000),(6009757/100000000000000)⟩
def e132 : ℝ := (354189/50000000000000)
theorem h132 : Model (fun x => f132 ((97/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-202006748738969/50000000000000),(-1455208433613/25000000000000),(8480690469/50000000000000),(-33680203/50000000000000)⟩
def e133 : ℝ := (19314579/100000000000000)
theorem h133 : Model (fun x => f133 ((97/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(41237113402061/100000000000000),(-212562440217/50000000000000),(2191365363/50000000000000),(-45182791/100000000000000)⟩
def e134 : ℝ := (3677/781250000000)
theorem h134 : Model (fun x => f134 ((97/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (12/5))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-166603504114611/100000000000000),(-170695477483/25000000000000),(7016686327/50000000000000),(-21556429/12500000000000)⟩
def e135 : ℝ := (13647133/100000000000000)
theorem h135 : Model (fun x => f135 ((97/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(88529281/256000),(912673/64000),(28227/128000),(97/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((97/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((97/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(8214057/32000),(254043/32000),(2619/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((97/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(154241737/256000),(1420759/64000),(38703/128000),(23/12800)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((97/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-9409/1600),(-97/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((97/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(152736297/256000),(1412999/64000),(38623/128000),(23/12800)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((97/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((97/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(291/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((97/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-291/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((97/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(149011497/256000),(1403399/64000),(38623/128000),(23/12800)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((97/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(149779497/256000),(1403399/64000),(38623/128000),(23/12800)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((97/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((97/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(149779497/4000),(1403399/1000),(38623/2000),(23/200)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((97/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((97/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(16732034109/512000),(172495197/128000),(5334903/256000),(18333/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((97/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(3059998543/100000000000000),(-126185507/100000000000000),(3252203/100000000000000),(-4191/6250000000000)⟩
def e151 : ℝ := (171/12500000000000)
theorem h151 : Model (fun x => f151 ((97/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (8015654997/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(57290630323909/50000000000000),(-21530077327/5000000000000),(756575979/20000000000000),(-7924159/25000000000000)⟩
def e152 : ℝ := (100709789/100000000000000)
theorem h152 : Model (fun x => f152 ((97/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(217/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((97/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(38409/1600),(197/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((97/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(411/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((97/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(4866180048661/100000000000000),(-35519562399/100000000000000),(129633439/50000000000000),(-1892459/100000000000000)⟩
def e156 : ℝ := (13917/100000000000000)
theorem h156 : Model (fun x => f156 ((97/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (102/5))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(116815693430637/100000000000000),(86406885467/25000000000000),(518533737/100000000000000),(-3784919/100000000000000)⟩
def e157 : ℝ := (160671/25000000000000)
theorem h157 : Model (fun x => f157 ((97/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(216815693430637/100000000000000),(86406885467/25000000000000),(518533737/100000000000000),(-3784919/100000000000000)⟩
def e158 : ℝ := (160671/25000000000000)
theorem h158 : Model (fun x => f158 ((97/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(54203923357659/50000000000000),(86406885467/50000000000000),(64816717/25000000000000),(-94623/5000000000000)⟩
def e159 : ℝ := (5021/1562500000000)
theorem h159 : Model (fun x => f159 ((97/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(4203923357659/50000000000000),(86406885467/50000000000000),(64816717/25000000000000),(-94623/5000000000000)⟩
def e160 : ℝ := (5021/1562500000000)
theorem h160 : Model (fun x => f160 ((97/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((97/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((97/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(400076577163673/100000000000000),(318882553509/50000000000000),(956818203/100000000000000),(-6984079/100000000000000)⟩
def e163 : ℝ := (237183/20000000000000)
theorem h163 : Model (fun x => f163 ((97/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(1377895431438979/50000000000000),(318882553509/50000000000000),(956818203/100000000000000),(-6984079/100000000000000)⟩
def e164 : ℝ := (296479/25000000000000)
theorem h164 : Model (fun x => f164 ((97/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((97/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(119499741376939/4000000000000),(5453773528813/100000000000000),(46421323/500000000000),(-56416503/100000000000000)⟩
def e166 : ℝ := (5083499/50000000000000)
theorem h166 : Model (fun x => f166 ((97/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8269874486804427/100000000000000),(5453773528813/100000000000000),(46421323/500000000000),(-56416503/100000000000000)⟩
def e167 : ℝ := (10166999/100000000000000)
theorem h167 : Model (fun x => f167 ((97/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((97/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4482596428602067/50000000000000),(20203800399471/100000000000000),(40930787599/100000000000000),(-46869917/25000000000000)⟩
def e169 : ℝ := (18904341/50000000000000)
theorem h169 : Model (fun x => f169 ((97/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14234240476251753/100000000000000),(20203800399471/100000000000000),(40930787599/100000000000000),(-46869917/25000000000000)⟩
def e170 : ℝ := (37808683/100000000000000)
theorem h170 : Model (fun x => f170 ((97/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((97/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15431033596584751/100000000000000),(46501232698551/100000000000000),(907748471/781250000000),(-349504181/100000000000000)⟩
def e172 : ℝ := (21865109/25000000000000)
theorem h172 : Model (fun x => f172 ((97/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(4441686970574759/25000000000000),(46501232698551/100000000000000),(907748471/781250000000),(-349504181/100000000000000)⟩
def e173 : ℝ := (87460437/100000000000000)
theorem h173 : Model (fun x => f173 ((97/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((97/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(3852109762107949/20000000000000),(20278593013079/25000000000000),(2019078861/800000000000),(-196880413/50000000000000)⟩
def e175 : ℝ := (76696703/50000000000000)
theorem h175 : Model (fun x => f175 ((97/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(19662929762920697/100000000000000),(20278593013079/25000000000000),(2019078861/800000000000),(-196880413/50000000000000)⟩
def e176 : ℝ := (153393407/100000000000000)
theorem h176 : Model (fun x => f176 ((97/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((97/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2131615875712771/10000000000000),(60957297258987/50000000000000),(464761256853/100000000000000),(-19065279/12500000000000)⟩
def e178 : ℝ := (9262803/4000000000000)
theorem h178 : Model (fun x => f178 ((97/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(10649269854754331/50000000000000),(60957297258987/50000000000000),(464761256853/100000000000000),(-19065279/12500000000000)⟩
def e179 : ℝ := (57892519/25000000000000)
theorem h179 : Model (fun x => f179 ((97/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((97/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(4617857656177057/20000000000000),(42242949093631/25000000000000),(769742935861/100000000000000),(68855399/12500000000000)⟩
def e181 : ℝ := (321650751/100000000000000)
theorem h181 : Model (fun x => f181 ((97/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(11546310807109309/50000000000000),(42242949093631/25000000000000),(769742935861/100000000000000),(68855399/12500000000000)⟩
def e182 : ℝ := (5025793/1562500000000)
theorem h182 : Model (fun x => f182 ((97/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(970796113935947/50000000000000),(2705705992517/5000000000000),(416596856077/100000000000000),(688802551/50000000000000)⟩
def e183 : ℝ := (100211/97656250000)
theorem h183 : Model (fun x => f183 ((97/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(58761306147259/50000000000000),(187343687897/50000000000000),(860777251/100000000000000),(-3207053/100000000000000)⟩
def e184 : ℝ := (351859/50000000000000)
theorem h184 : Model (fun x => f184 ((97/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(104203923357659/50000000000000),(86406885467/50000000000000),(64816717/25000000000000),(-94623/5000000000000)⟩
def e185 : ℝ := (5021/1562500000000)
theorem h185 : Model (fun x => f185 ((97/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(217169152862577/50000000000000),(360157458831/50000000000000),(1379310987/100000000000000),(-6991973/100000000000000)⟩
def e186 : ℝ := (673203/50000000000000)
theorem h186 : Model (fun x => f186 ((97/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(226298777605397/25000000000000),(2251789214203/100000000000000),(5245491021/100000000000000),(-9270161/50000000000000)⟩
def e187 : ℝ := (4228569/100000000000000)
theorem h187 : Model (fun x => f187 ((97/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(235812204775247/12500000000000),(6257207218517/100000000000000),(17170287753/100000000000000),(-10216717/25000000000000)⟩
def e188 : ℝ := (11797237/100000000000000)
theorem h188 : Model (fun x => f188 ((97/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2217061305289347/100000000000000),(14422101874877/100000000000000),(59862478741/100000000000000),(4833363/50000000000000)⟩
def e189 : ℝ := (13717703/50000000000000)
theorem h189 : Model (fun x => f189 ((97/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((97/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(54203923357659/6250000000000),(86406885467/6250000000000),(64816717/3125000000000),(-94623/625000000000)⟩
def e191 : ℝ := (5021/195312500000)
theorem h191 : Model (fun x => f191 ((97/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(492392693008531/50000000000000),(878598771633/50000000000000),(586982439/20000000000000),(-18346733/100000000000000)⟩
def e192 : ℝ := (327447/10000000000000)
theorem h192 : Model (fun x => f192 ((97/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(542392693008531/50000000000000),(878598771633/50000000000000),(586982439/20000000000000),(-18346733/100000000000000)⟩
def e193 : ℝ := (327447/10000000000000)
theorem h193 : Model (fun x => f193 ((97/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(6012589259704489/25000000000000),(195407000284403/100000000000000),(483936521771/50000000000000),(234656589/20000000000000)⟩
def e194 : ℝ := (92974827/25000000000000)
theorem h194 : Model (fun x => f194 ((97/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(51974280381/12500000000000),(-844572761/25000000000000),(10715253/100000000000000),(28609/100000000000000)⟩
def e195 : ℝ := (7043/100000000000000)
theorem h195 : Model (fun x => f195 ((97/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (11926990310153879/50000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(4036514353479/50000000000000),(39852689667/25000000000000),(112099799/100000000000000),(-1991917/100000000000000)⟩
def e196 : ℝ := (146147/25000000000000)
theorem h196 : Model (fun x => f196 ((97/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(116815693430637/50000000000000),(86406885467/12500000000000),(518533737/50000000000000),(-3784919/50000000000000)⟩
def e197 : ℝ := (160671/12500000000000)
theorem h197 : Model (fun x => f197 ((97/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(23061061313809/50000000000000),(-9190453201/12500000000000),(689947/10000000000000),(484993/50000000000000)⟩
def e198 : ℝ := (17501/12500000000000)
theorem h198 : Model (fun x => f198 ((97/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (216469542927429/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(107755754744761/100000000000000),(147047251211/100000000000000),(-13798941/100000000000000),(-77599/4000000000000)⟩
def e199 : ℝ := (93421/10000000000000)
theorem h199 : Model (fun x => f199 ((97/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(7755754744761/100000000000000),(147047251211/100000000000000),(-13798941/100000000000000),(-77599/4000000000000)⟩
def e200 : ℝ := (93421/10000000000000)
theorem h200 : Model (fun x => f200 ((97/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(99417511818083/25000000000000),(542674379469/100000000000000),(-6365583/12500000000000),(-894929/12500000000000)⟩
def e201 : ℝ := (1723841/50000000000000)
theorem h201 : Model (fun x => f201 ((97/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2753384332986617/100000000000000),(542674379469/100000000000000),(-6365583/12500000000000),(-894929/12500000000000)⟩
def e202 : ℝ := (3447683/100000000000000)
theorem h202 : Model (fun x => f202 ((97/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(741732517258433/25000000000000),(2316769425167/50000000000000),(181587811/50000000000000),(-12255887/20000000000000)⟩
def e203 : ℝ := (14734331/50000000000000)
theorem h203 : Model (fun x => f203 ((97/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(2062327755353671/25000000000000),(2316769425167/50000000000000),(181587811/50000000000000),(-12255887/20000000000000)⟩
def e204 : ℝ := (29468663/100000000000000)
theorem h204 : Model (fun x => f204 ((97/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(1777821470473629/20000000000000),(3424657972081/20000000000000),(758314573/12500000000000),(-226172029/100000000000000)⟩
def e205 : ℝ := (3408961/3125000000000)
theorem h205 : Model (fun x => f205 ((97/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(3539538742853941/25000000000000),(3424657972081/20000000000000),(758314573/12500000000000),(-226172029/100000000000000)⟩
def e206 : ℝ := (109086753/100000000000000)
theorem h206 : Model (fun x => f206 ((97/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(15256226747381957/100000000000000),(2454406745867/6250000000000),(29762672337/100000000000000),(-511820231/100000000000000)⟩
def e207 : ℝ := (50160061/20000000000000)
theorem h207 : Model (fun x => f207 ((97/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(8795970516548121/50000000000000),(2454406745867/6250000000000),(29762672337/100000000000000),(-511820231/100000000000000)⟩
def e208 : ℝ := (125400153/50000000000000)
theorem h208 : Model (fun x => f208 ((97/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(18956328834466161/100000000000000),(68184697940073/100000000000000),(43694846549/50000000000000),(-427224367/50000000000000)⟩
def e209 : ℝ := (54606563/12500000000000)
theorem h209 : Model (fun x => f209 ((97/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(19358709786847113/100000000000000),(68184697940073/100000000000000),(43694846549/50000000000000),(-427224367/50000000000000)⟩
def e210 : ℝ := (87370501/20000000000000)
theorem h210 : Model (fun x => f210 ((97/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(1043006191983251/5000000000000),(50969693248617/50000000000000),(47939962623/25000000000000),(-588588219/50000000000000)⟩
def e211 : ℝ := (655457847/100000000000000)
theorem h211 : Model (fun x => f211 ((97/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(5210626198011493/25000000000000),(50969693248617/50000000000000),(47939962623/25000000000000),(-588588219/50000000000000)⟩
def e212 : ℝ := (81932231/12500000000000)
theorem h212 : Model (fun x => f212 ((97/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(5614749586595529/25000000000000),(70246942841249/50000000000000),(353655295001/100000000000000),(-280980741/20000000000000)⟩
def e213 : ℝ := (181332607/20000000000000)
theorem h213 : Model (fun x => f213 ((97/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(22462331679715449/100000000000000),(70246942841249/50000000000000),(353655295001/100000000000000),(-280980741/20000000000000)⟩
def e214 : ℝ := (226665759/25000000000000)
theorem h214 : Model (fun x => f214 ((97/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(435530838758371/25000000000000),(21963301248919/50000000000000),(115460735221/50000000000000),(-344303/781250000000)⟩
def e215 : ℝ := (11506401/4000000000000)
theorem h215 : Model (fun x => f215 ((97/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(11611302680613/10000000000000),(316903750747/100000000000000),(93245317/50000000000000),(-1055363/25000000000000)⟩
def e216 : ℝ := (404357/20000000000000)
theorem h216 : Model (fun x => f216 ((97/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(207755754744761/100000000000000),(147047251211/100000000000000),(-13798941/100000000000000),(-77599/4000000000000)⟩
def e217 : ℝ := (93421/10000000000000)
theorem h217 : Model (fun x => f217 ((97/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(107906134073913/25000000000000),(610998253169/100000000000000),(9930797/6250000000000),(-4050701/50000000000000)⟩
def e218 : ℝ := (778041/20000000000000)
theorem h218 : Model (fun x => f218 ((97/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(448362406522303/50000000000000),(1904076048523/100000000000000),(1169005357/100000000000000),(-25055201/100000000000000)⟩
def e219 : ℝ := (12149627/100000000000000)
theorem h219 : Model (fun x => f219 ((97/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(116437337707773/6250000000000),(329652297127/6250000000000),(79762951/1562500000000),(-16998403/25000000000000)⟩
def e220 : ℝ := (16864237/50000000000000)
theorem h220 : Model (fun x => f220 ((97/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2163182674319529/100000000000000),(2405643361907/20000000000000),(163228593/625000000000),(-65790629/50000000000000)⟩
def e221 : ℝ := (9683951/12500000000000)
theorem h221 : Model (fun x => f221 ((97/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(107755754744761/12500000000000),(147047251211/12500000000000),(-13798941/12500000000000),(-77599/500000000000)⟩
def e222 : ℝ := (93421/1250000000000)
theorem h222 : Model (fun x => f222 ((97/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(489079532382109/50000000000000),(298656352087/20000000000000),(38049553/50000000000000),(-4935313/25000000000000)⟩
def e223 : ℝ := (1899093/20000000000000)
theorem h223 : Model (fun x => f223 ((97/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(539079532382109/50000000000000),(298656352087/20000000000000),(38049553/50000000000000),(-4935313/25000000000000)⟩
def e224 : ℝ := (1899093/20000000000000)
theorem h224 : Model (fun x => f224 ((97/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(23322550090585033/100000000000000),(80992861090999/50000000000000),(462839549873/100000000000000),(-144654719/10000000000000)⟩
def e225 : ℝ := (523648903/50000000000000)
theorem h225 : Model (fun x => f225 ((97/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(85753915941/20000000000000),(-1488999911/50000000000000),(6087283/50000000000000),(567/50000000000000)⟩
def e226 : ℝ := (4991/25000000000000)
theorem h226 : Model (fun x => f226 ((97/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (11580049517504083/50000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(7469694987319/100000000000000),(4264483703/3125000000000),(-105917169/100000000000000),(-67927/4000000000000)⟩
def e227 : ℝ := (12723/781250000000)
theorem h227 : Model (fun x => f227 ((97/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(15542723694277/100000000000000),(73968559291/25000000000000),(618263/10000000000000),(-922523/25000000000000)⟩
def e228 : ℝ := (553283/25000000000000)
theorem h228 : Model (fun x => f228 ((97/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(17809048747909/100000000000000),(2125697049/781250000000),(-42437021/6250000000000),(201127/10000000000000)⟩
def e229 : ℝ := (18574283/100000000000000)
theorem h229 : Model (fun x => f229 ((97/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(7343937628003/100000000000000),(36491043947/100000000000000),(-656193169/100000000000000),(7594267/100000000000000)⟩
def e230 : ℝ := (499127/6250000000000)
theorem h230 : Model (fun x => f230 ((97/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-9953722905413/6250000000000),(-129258173197/20000000000000),(2675435897/20000000000000),(-32971433/20000000000000)⟩
def e231 : ℝ := (4326633/20000000000000)
theorem h231 : Model (fun x => f231 ((97/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((97/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-9409/320),(-97/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((97/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2037/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((97/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6887/320),(-13/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((97/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((97/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15207/320),(-13/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((97/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((97/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(380175/32),(-325/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((97/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13871/1600),(23/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((97/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23471/1600),(23/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((97/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((97/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4436019/1600),(4347/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((97/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(36068375721/100000000000000),(-70689161/100000000000000),(837631/50000000000000),(-787/12500000000000)⟩
def e244 : ℝ := (87/100000000000000)
theorem h244 : Model (fun x => f244 ((97/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (69174/25))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(428509210616599/100000000000000),(-786229625029/50000000000000),(-6839647111/100000000000000),(-13400571/25000000000000)⟩
def e245 : ℝ := (2221269/100000000000000)
theorem h245 : Model (fun x => f245 ((97/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(873/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((97/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(79249/1600),(457/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((97/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(112849/1600),(457/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((97/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(31329/1600),(177/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((97/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3535446321/2560000),(17145813/640000),(233867/1280000),(317/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((97/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((97/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(168921/160),(1233/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((97/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(94718833063/100000000000000),(-86422293/6250000000000),(15139671/100000000000000),(-29469/20000000000000)⟩
def e253 : ℝ := (43/3125000000000)
theorem h253 : Model (fun x => f253 ((97/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (83223/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(65404951148827/50000000000000),(313957724937/50000000000000),(292457267/25000000000000),(-3617697/100000000000000)⟩
def e254 : ℝ := (3860631/100000000000000)
theorem h254 : Model (fun x => f254 ((97/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(115404951148827/50000000000000),(313957724937/50000000000000),(292457267/25000000000000),(-3617697/100000000000000)⟩
def e255 : ℝ := (3860631/100000000000000)
theorem h255 : Model (fun x => f255 ((97/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(115404951148827/100000000000000),(313957724937/100000000000000),(292457267/50000000000000),(-1808849/100000000000000)⟩
def e256 : ℝ := (482579/25000000000000)
theorem h256 : Model (fun x => f256 ((97/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(15404951148827/100000000000000),(313957724937/100000000000000),(292457267/50000000000000),(-1808849/100000000000000)⟩
def e257 : ℝ := (482579/25000000000000)
theorem h257 : Model (fun x => f257 ((97/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(425899224477813/100000000000000),(144831688587/12500000000000),(2158613161/100000000000000),(-1335103/20000000000000)⟩
def e258 : ℝ := (1780947/25000000000000)
theorem h258 : Model (fun x => f258 ((97/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1390806755096049/50000000000000),(144831688587/12500000000000),(2158613161/100000000000000),(-1335103/20000000000000)⟩
def e259 : ℝ := (7123789/100000000000000)
theorem h259 : Model (fun x => f259 ((97/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(1605059856293181/50000000000000),(5035117004417/50000000000000),(559972259/2500000000000),(-22232399/50000000000000)⟩
def e260 : ℝ := (30994661/50000000000000)
theorem h260 : Model (fun x => f260 ((97/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4246250332483657/50000000000000),(5035117004417/50000000000000),(559972259/2500000000000),(-22232399/50000000000000)⟩
def e261 : ℝ := (61989323/100000000000000)
theorem h261 : Model (fun x => f261 ((97/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(1225095780464917/12500000000000),(19142205258229/50000000000000),(107139576757/100000000000000),(-75705783/100000000000000)⟩
def e262 : ℝ := (236052063/100000000000000)
theorem h262 : Model (fun x => f262 ((97/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(3013962772553391/20000000000000),(19142205258229/50000000000000),(107139576757/100000000000000),(-75705783/100000000000000)⟩
def e263 : ℝ := (7376627/3125000000000)
theorem h263 : Model (fun x => f263 ((97/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(17391311326545363/100000000000000),(45747475004959/50000000000000),(33198677201/10000000000000),(200345659/100000000000000)⟩
def e264 : ℝ := (35318767/6250000000000)
theorem h264 : Model (fun x => f264 ((97/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(308234775191557/1562500000000),(45747475004959/50000000000000),(33198677201/10000000000000),(200345659/100000000000000)⟩
def e265 : ℝ := (565100273/100000000000000)
theorem h265 : Model (fun x => f265 ((97/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(22765964270944837/100000000000000),(167524223172579/100000000000000),(392885437737/50000000000000),(1451842081/100000000000000)⟩
def e266 : ℝ := (518709177/50000000000000)
theorem h266 : Model (fun x => f266 ((97/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(23168345223325789/100000000000000),(167524223172579/100000000000000),(392885437737/50000000000000),(1451842081/100000000000000)⟩
def e267 : ℝ := (207483671/20000000000000)
theorem h267 : Model (fun x => f267 ((97/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(167108859293567/625000000000),(26607005748347/10000000000000),(196036094159/12500000000000),(1175819789/25000000000000)⟩
def e268 : ℝ := (1657096273/100000000000000)
theorem h268 : Model (fun x => f268 ((97/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(3339974804918959/12500000000000),(26607005748347/10000000000000),(196036094159/12500000000000),(1175819789/25000000000000)⟩
def e269 : ℝ := (828548137/50000000000000)
theorem h269 : Model (fun x => f269 ((97/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(7708992583999709/25000000000000),(78189378229679/20000000000000),(2801518353327/100000000000000),(2856135583/25000000000000)⟩
def e270 : ℝ := (2457653979/100000000000000)
theorem h270 : Model (fun x => f270 ((97/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(30839303669332169/100000000000000),(78189378229679/20000000000000),(2801518353327/100000000000000),(2856135583/25000000000000)⟩
def e271 : ℝ := (122882699/5000000000000)
theorem h271 : Model (fun x => f271 ((97/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(4750779664899033/100000000000000),(39261888446479/25000000000000),(1839364068263/100000000000000),(12284397201/100000000000000)⟩
def e272 : ℝ := (517213559/50000000000000)
theorem h272 : Model (fun x => f272 ((97/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(133183027496631/100000000000000),(724645518183/100000000000000),(1167867597/50000000000000),(-251117/50000000000000)⟩
def e273 : ℝ := (559433/12500000000000)
theorem h273 : Model (fun x => f273 ((97/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(215404951148827/100000000000000),(313957724937/100000000000000),(292457267/50000000000000),(-1808849/100000000000000)⟩
def e274 : ℝ := (482579/25000000000000)
theorem h274 : Model (fun x => f274 ((97/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(92798585958857/20000000000000),(1352560968057/100000000000000),(1752782131/50000000000000),(-1029983/25000000000000)⟩
def e275 : ℝ := (260503/3125000000000)
theorem h275 : Model (fun x => f275 ((97/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(99946374375739/10000000000000),(4370224938751/100000000000000),(1813948839/12500000000000),(824923/50000000000000)⟩
def e276 : ℝ := (13491139/50000000000000)
theorem h276 : Model (fun x => f276 ((97/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(2152894388990843/100000000000000),(12551574525881/100000000000000),(406602819/800000000000),(282987/500000000000)⟩
def e277 : ℝ := (19398687/25000000000000)
theorem h277 : Model (fun x => f277 ((97/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(28672899260631/1000000000000),(32317419653099/100000000000000),(8357243089/4000000000000),(90755093/12500000000000)⟩
def e278 : ℝ := (202358477/100000000000000)
theorem h278 : Model (fun x => f278 ((97/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(115404951148827/12500000000000),(313957724937/12500000000000),(292457267/6250000000000),(-1808849/12500000000000)⟩
def e279 : ℝ := (482579/3125000000000)
theorem h279 : Model (fun x => f279 ((97/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1056422636687247/100000000000000),(3236307317679/100000000000000),(3507525733/50000000000000),(-7486513/50000000000000)⟩
def e280 : ℝ := (2489749/12500000000000)
theorem h280 : Model (fun x => f280 ((97/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1156422636687247/100000000000000),(3236307317679/100000000000000),(3507525733/50000000000000),(-7486513/50000000000000)⟩
def e281 : ℝ := (2489749/12500000000000)
theorem h281 : Model (fun x => f281 ((97/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(8289497441111679/25000000000000),(233260135078951/50000000000000),(732631830643/20000000000000),(16995514811/100000000000000)⟩
def e282 : ℝ := (2957602159/100000000000000)
theorem h282 : Model (fun x => f282 ((97/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(301586437267/100000000000000),(-2121603077/50000000000000),(5276451/20000000000000),(-28499/50000000000000)⟩
def e283 : ℝ := (27747/100000000000000)
theorem h283 : Model (fun x => f283 ((97/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (32687786382018629/100000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(7163853566887/50000000000000),(272048747173/100000000000000),(1367839/1000000000000),(-2275097/100000000000000)⟩
def e284 : ℝ := (93077/2000000000000)
theorem h284 : Model (fun x => f284 ((97/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(65404951148827/25000000000000),(313957724937/25000000000000),(292457267/12500000000000),(-3617697/50000000000000)⟩
def e285 : ℝ := (3860631/50000000000000)
theorem h285 : Model (fun x => f285 ((97/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(10831424367469/25000000000000),(-117867017607/100000000000000),(25266313/25000000000000),(100153/10000000000000)⟩
def e286 : ℝ := (733749/100000000000000)
theorem h286 : Model (fun x => f286 ((97/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (7193150298137/3125000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(113348605060243/100000000000000),(58933508803/25000000000000),(-50532627/25000000000000),(-2003061/100000000000000)⟩
def e287 : ℝ := (5306753/100000000000000)
theorem h287 : Model (fun x => f287 ((97/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(13348605060243/100000000000000),(58933508803/25000000000000),(-50532627/25000000000000),(-2003061/100000000000000)⟩
def e288 : ℝ := (5306753/100000000000000)
theorem h288 : Model (fun x => f288 ((97/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(83662065639703/20000000000000),(434985422117/50000000000000),(-186489457/25000000000000),(-7392249/100000000000000)⟩
def e289 : ℝ := (19584449/100000000000000)
theorem h289 : Model (fun x => f289 ((97/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(3467530767391/125000000000),(434985422117/50000000000000),(-186489457/25000000000000),(-7392249/100000000000000)⟩
def e290 : ℝ := (391689/2000000000000)
theorem h290 : Model (fun x => f290 ((97/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(62886364077959/2000000000000),(188135499413/2500000000000),(-4401865461/100000000000000),(-6746137/10000000000000)⟩
def e291 : ℝ := (21191891/12500000000000)
theorem h291 : Model (fun x => f291 ((97/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(4213349578139451/50000000000000),(188135499413/2500000000000),(-4401865461/100000000000000),(-6746137/10000000000000)⟩
def e292 : ℝ := (169535129/100000000000000)
theorem h292 : Model (fun x => f292 ((97/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9551545946265401/100000000000000),(14197278262291/50000000000000),(-1070601683/25000000000000),(-270846311/100000000000000)⟩
def e293 : ℝ := (40028157/6250000000000)
theorem h293 : Model (fun x => f293 ((97/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(741029678265651/5000000000000),(14197278262291/50000000000000),(-1070601683/25000000000000),(-270846311/100000000000000)⟩
def e294 : ℝ := (640450513/100000000000000)
theorem h294 : Model (fun x => f294 ((97/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8399468033965221/50000000000000),(33561008493769/50000000000000),(803116113/2500000000000),(-671355197/100000000000000)⟩
def e295 : ℝ := (1516651409/100000000000000)
theorem h295 : Model (fun x => f295 ((97/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(19134650353644727/100000000000000),(33561008493769/50000000000000),(803116113/2500000000000),(-671355197/100000000000000)⟩
def e296 : ℝ := (151665141/10000000000000)
theorem h296 : Model (fun x => f296 ((97/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(1355553703688197/6250000000000),(121188753346027/100000000000000),(3899132741/2500000000000),(-1204195823/100000000000000)⟩
def e297 : ℝ := (2744666799/100000000000000)
theorem h297 : Model (fun x => f297 ((97/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(2761405026424013/12500000000000),(121188753346027/100000000000000),(3899132741/2500000000000),(-1204195823/100000000000000)⟩
def e298 : ℝ := (6861667/250000000000)
theorem h298 : Model (fun x => f298 ((97/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(12520056310060213/50000000000000),(18944233338631/10000000000000),(417814505277/100000000000000),(-168473631/10000000000000)⟩
def e299 : ℝ := (430186663/10000000000000)
theorem h299 : Model (fun x => f299 ((97/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(12511246786250689/50000000000000),(18944233338631/10000000000000),(417814505277/100000000000000),(-168473631/10000000000000)⟩
def e300 : ℝ := (4301866631/100000000000000)
theorem h300 : Model (fun x => f300 ((97/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(7090661853929819/25000000000000),(136858388048039/50000000000000),(869588876989/100000000000000),(-72353227/4000000000000)⟩
def e301 : ℝ := (6232828891/100000000000000)
theorem h301 : Model (fun x => f301 ((97/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(28365980749052609/100000000000000),(136858388048039/50000000000000),(869588876989/100000000000000),(-72353227/4000000000000)⟩
def e302 : ℝ := (1558207223/25000000000000)
theorem h302 : Model (fun x => f302 ((97/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(3786462741655591/100000000000000),(20681128494379/20000000000000),(703985285193/100000000000000),(343505139/50000000000000)⟩
def e303 : ℝ := (1189052083/50000000000000)
theorem h303 : Model (fun x => f303 ((97/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(128479062691029/100000000000000),(53440248113/10000000000000),(97481131/100000000000000),(-1098773/20000000000000)⟩
def e304 : ℝ := (3016087/25000000000000)
theorem h304 : Model (fun x => f304 ((97/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(213348605060243/100000000000000),(58933508803/25000000000000),(-50532627/25000000000000),(-2003061/100000000000000)⟩
def e305 : ℝ := (5306753/100000000000000)
theorem h305 : Model (fun x => f305 ((97/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(91035254562303/20000000000000),(502935275777/50000000000000),(-61355977/20000000000000),(-9499987/100000000000000)⟩
def e306 : ℝ := (11338927/50000000000000)
theorem h306 : Model (fun x => f306 ((97/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(971112228608573/100000000000000),(1609508092839/50000000000000),(398309261/50000000000000),(-6428381/20000000000000)⟩
def e307 : ℝ := (72686819/100000000000000)
theorem h307 : Model (fun x => f307 ((97/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(517963598326457/25000000000000),(9156968171743/100000000000000),(1831244293/25000000000000),(-9265499/10000000000000)⟩
def e308 : ℝ := (103547561/50000000000000)
theorem h308 : Model (fun x => f308 ((97/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2661899104842233/100000000000000),(11418414080599/50000000000000),(30182897107/50000000000000),(-184795971/100000000000000)⟩
def e309 : ℝ := (519233761/100000000000000)
theorem h309 : Model (fun x => f309 ((97/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(113348605060243/12500000000000),(58933508803/3125000000000),(-50532627/3125000000000),(-2003061/12500000000000)⟩
def e310 : ℝ := (5306753/12500000000000)
theorem h310 : Model (fun x => f310 ((97/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(1035267903172973/100000000000000),(1210137381413/50000000000000),(-1519562933/100000000000000),(-21518353/100000000000000)⟩
def e311 : ℝ := (13629593/25000000000000)
theorem h311 : Model (fun x => f311 ((97/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(1135267903172973/100000000000000),(1210137381413/50000000000000),(-1519562933/100000000000000),(-21518353/100000000000000)⟩
def e312 : ℝ := (13629593/25000000000000)
theorem h312 : Model (fun x => f312 ((97/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(7554921538030639/25000000000000),(64736890492647/20000000000000),(1197578242711/100000000000000),(-311345617/20000000000000)⟩
def e313 : ℝ := (3690645467/50000000000000)
theorem h313 : Model (fun x => f313 ((97/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(64630883/19531250000),(-886098393/25000000000000),(49701/200000000000),(-27167/25000000000000)⟩
def e314 : ℝ := (82599/100000000000000)
theorem h314 : Model (fun x => f314 ((97/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (29894795183397591/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(12529788438517/100000000000000),(207972594561/100000000000000),(-394589463/100000000000000),(-1096477/100000000000000)⟩
def e315 : ℝ := (11206669/100000000000000)
theorem h315 : Model (fun x => f315 ((97/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(26857495572291/100000000000000),(240010670867/50000000000000),(-257805563/100000000000000),(-1685787/50000000000000)⟩
def e316 : ℝ := (15860519/100000000000000)
theorem h316 : Model (fun x => f316 ((97/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(28771710567053/25000000000000),(326922497759/20000000000000),(-5244909247/50000000000000),(-11524323/20000000000000)⟩
def e317 : ℝ := (1380171/2000000000000)
theorem h317 : Model (fun x => f317 ((97/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(47458491656993/100000000000000),(1848042051/1000000000000),(-6230896339/100000000000000),(40474553/100000000000000)⟩
def e318 : ℝ := (3782319/12500000000000)
theorem h318 : Model (fun x => f318 ((97/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-22360214965923/20000000000000),(-92297332177/20000000000000),(3573141573/50000000000000),(-31095653/25000000000000)⟩
def e319 : ℝ := (51891717/100000000000000)
theorem h319 : Model (fun x => f319 ((97/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((97/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-103499/1600),(-1067/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((97/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((97/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(9409/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((97/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(272861/1600),(873/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((97/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((97/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(445661/1600),(873/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((97/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2228305/32),(4365/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((97/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((97/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(268447307975938249/25000000000000),(4208964651491/200000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (27781/20000000000000)
theorem h329 : Model (fun x => f329 ((97/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(4656407283/50000000000000),(-18251863/100000000000000),(8651/2000000000000),(-813/50000000000000)⟩
def e330 : ℝ := (3/12500000000000)
theorem h330 : Model (fun x => f330 ((97/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (535819499981045757/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(324246738460791/50000000000000),(634846149671/50000000000000),(4567340041/50000000000000),(4518711/12500000000000)⟩
def e331 : ℝ := (2867653/100000000000000)
theorem h331 : Model (fun x => f331 ((97/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((97/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(457/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((97/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((97/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((97/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(735806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((97/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((97/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((97/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3264400126834439/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (43/4000000000000)
theorem h339 : Model (fun x => f339 ((97/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3834193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((97/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((97/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((97/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(1080299936582651/50000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (537/50000000000000)
theorem h343 : Model (fun x => f343 ((97/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(289271515639/6250000000000),(-1508904169/25000000000000),(7870777/100000000000000),(-1283/12500000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((97/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2157782331529747/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(75543837787323/50000000000000),(207413464473/25000000000000),(-540957251/50000000000000),(1410873/100000000000000)⟩
def e345 : ℝ := (2921/100000000000000)
theorem h345 : Model (fun x => f345 ((97/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(125543837787323/50000000000000),(207413464473/25000000000000),(-540957251/50000000000000),(1410873/100000000000000)⟩
def e346 : ℝ := (2921/100000000000000)
theorem h346 : Model (fun x => f346 ((97/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(125543837787323/100000000000000),(207413464473/50000000000000),(-540957251/100000000000000),(176359/25000000000000)⟩
def e347 : ℝ := (1461/100000000000000)
theorem h347 : Model (fun x => f347 ((97/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(25543837787323/100000000000000),(207413464473/50000000000000),(-540957251/100000000000000),(176359/25000000000000)⟩
def e348 : ℝ := (1461/100000000000000)
theorem h348 : Model (fun x => f348 ((97/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(5791456802689/1250000000000),(1530908904443/100000000000000),(-399277971/20000000000000),(1301697/50000000000000)⟩
def e349 : ℝ := (2697/50000000000000)
theorem h349 : Model (fun x => f349 ((97/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(563806165985881/20000000000000),(1530908904443/100000000000000),(-399277971/20000000000000),(1301697/50000000000000)⟩
def e350 : ℝ := (1079/20000000000000)
theorem h350 : Model (fun x => f350 ((97/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(3539119492301197/100000000000000),(6808030404751/50000000000000),(-11405473731/100000000000000),(6591733/100000000000000)⟩
def e351 : ℝ := (40217/50000000000000)
theorem h351 : Model (fun x => f351 ((97/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(8821500444682149/100000000000000),(6808030404751/50000000000000),(-11405473731/100000000000000),(6591733/100000000000000)⟩
def e352 : ℝ := (16087/20000000000000)
theorem h352 : Model (fun x => f352 ((97/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(5537425104339867/50000000000000),(53688084677337/100000000000000),(-5556328843/100000000000000),(-50464491/100000000000000)⟩
def e353 : ℝ := (41561/10000000000000)
theorem h353 : Model (fun x => f353 ((97/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(16343897827727353/100000000000000),(53688084677337/100000000000000),(-5556328843/100000000000000),(-50464491/100000000000000)⟩
def e354 : ℝ := (415611/100000000000000)
theorem h354 : Model (fun x => f354 ((97/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(4103751315393567/20000000000000),(135200971367269/100000000000000),(31830876003/25000000000000),(-52307611/20000000000000)⟩
def e355 : ℝ := (481379/50000000000000)
theorem h355 : Model (fun x => f355 ((97/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(571361771567053/2500000000000),(135200971367269/100000000000000),(31830876003/25000000000000),(-52307611/20000000000000)⟩
def e356 : ℝ := (962759/100000000000000)
theorem h356 : Model (fun x => f356 ((97/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(179327373918729/625000000000),(264542987786731/100000000000000),(29853196673/5000000000000),(-370328523/100000000000000)⟩
def e357 : ℝ := (2370821/100000000000000)
theorem h357 : Model (fun x => f357 ((97/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(3636845097422199/12500000000000),(264542987786731/100000000000000),(29853196673/5000000000000),(-370328523/100000000000000)⟩
def e358 : ℝ := (1185411/50000000000000)
theorem h358 : Model (fun x => f358 ((97/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(36526679277471477/100000000000000),(113202580522497/25000000000000),(168958230999/10000000000000),(786037781/100000000000000)⟩
def e359 : ℝ := (3160669/50000000000000)
theorem h359 : Model (fun x => f359 ((97/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(36509060229852429/100000000000000),(113202580522497/25000000000000),(168958230999/10000000000000),(786037781/100000000000000)⟩
def e360 : ℝ := (6321339/100000000000000)
theorem h360 : Model (fun x => f360 ((97/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(45834875352641987/100000000000000),(719924869587451/100000000000000),(950511804757/25000000000000),(1450925547/25000000000000)⟩
def e361 : ℝ := (2238991/20000000000000)
theorem h361 : Model (fun x => f361 ((97/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(1145955217149383/2500000000000),(719924869587451/100000000000000),(950511804757/25000000000000),(1450925547/25000000000000)⟩
def e362 : ℝ := (2798739/25000000000000)
theorem h362 : Model (fun x => f362 ((97/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(11708837671360137/100000000000000),(74809134850781/20000000000000),(1854832943919/50000000000000),(1368327743/10000000000000)⟩
def e363 : ℝ := (761093/6250000000000)
theorem h363 : Model (fun x => f363 ((97/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(9850784503981/6250000000000),(260394823387/25000000000000),(181268411/50000000000000),(-271681/10000000000000)⟩
def e364 : ℝ := (12469/100000000000000)
theorem h364 : Model (fun x => f364 ((97/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(225543837787323/100000000000000),(207413464473/50000000000000),(-540957251/100000000000000),(176359/25000000000000)⟩
def e365 : ℝ := (1461/100000000000000)
theorem h365 : Model (fun x => f365 ((97/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(254350113819171/50000000000000),(23390414393/1250000000000),(-8992221/1250000000000),(-652969/50000000000000)⟩
def e366 : ℝ := (15391/100000000000000)
theorem h366 : Model (fun x => f366 ((97/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(286835504062091/25000000000000),(6330676595559/100000000000000),(169400811/5000000000000),(-3115913/25000000000000)⟩
def e367 : ℝ := (13479/25000000000000)
theorem h367 : Model (fun x => f367 ((97/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(2587759215993011/100000000000000),(19037934602037/100000000000000),(27696183279/100000000000000),(-20104543/50000000000000)⟩
def e368 : ℝ := (164149/100000000000000)
theorem h368 : Model (fun x => f368 ((97/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(163145333663603/4000000000000),(56959738747151/100000000000000),(125664713023/50000000000000),(44763633/20000000000000)⟩
def e369 : ℝ := (711001/50000000000000)
theorem h369 : Model (fun x => f369 ((97/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(125543837787323/12500000000000),(207413464473/6250000000000),(-540957251/12500000000000),(176359/3125000000000)⟩
def e370 : ℝ := (1461/12500000000000)
theorem h370 : Model (fun x => f370 ((97/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(29049081359057/2500000000000),(1090048681279/25000000000000),(-1982560593/50000000000000),(1463339/50000000000000)⟩
def e371 : ℝ := (24157/100000000000000)
theorem h371 : Model (fun x => f371 ((97/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(31549081359057/2500000000000),(1090048681279/25000000000000),(-1982560593/50000000000000),(1463339/50000000000000)⟩
def e372 : ℝ := (24157/100000000000000)
theorem h372 : Model (fun x => f372 ((97/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(25735427025517559/50000000000000),(112080916073329/12500000000000),(2746758886833/50000000000000),(2910950293/25000000000000)⟩
def e373 : ℝ := (4093649/20000000000000)
theorem h373 : Model (fun x => f373 ((97/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(194284710917/100000000000000),(-211533389/6250000000000),(38224099/100000000000000),(-348601/100000000000000)⟩
def e374 : ℝ := (2921/100000000000000)
theorem h374 : Model (fun x => f374 ((97/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (50568701540405403/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(11374240710771/50000000000000),(330423938701/100000000000000),(-97679251/10000000000000),(797017/25000000000000)⟩
def e375 : ℝ := (366967/50000000000000)
theorem h375 : Model (fun x => f375 ((97/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(75543837787323/25000000000000),(207413464473/12500000000000),(-540957251/25000000000000),(1410873/50000000000000)⟩
def e376 : ℝ := (2921/50000000000000)
theorem h376 : Model (fun x => f376 ((97/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(7965345154527/20000000000000),(-131597047163/100000000000000),(75804751/12500000000000),(-558929/20000000000000)⟩
def e377 : ℝ := (6557/50000000000000)
theorem h377 : Model (fun x => f377 ((97/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (125128469194229/50000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(4813861938189/4000000000000),(131597047161/50000000000000),(-1212876021/100000000000000),(698661/12500000000000)⟩
def e378 : ℝ := (105467/100000000000000)
theorem h378 : Model (fun x => f378 ((97/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(813861938189/4000000000000),(131597047161/50000000000000),(-1212876021/100000000000000),(698661/12500000000000)⟩
def e379 : ℝ := (105467/100000000000000)
theorem h379 : Model (fun x => f379 ((97/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(444136071678151/100000000000000),(971311538569/100000000000000),(-2238045039/50000000000000),(10313567/50000000000000)⟩
def e380 : ℝ := (194613/50000000000000)
theorem h380 : Model (fun x => f380 ((97/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(699962589348109/25000000000000),(971311538569/100000000000000),(-2238045039/50000000000000),(10313567/50000000000000)⟩
def e381 : ℝ := (389227/100000000000000)
theorem h381 : Model (fun x => f381 ((97/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(3369523267019079/100000000000000),(53362379387/625000000000),(-36789098917/100000000000000),(78877067/50000000000000)⟩
def e382 : ℝ := (358677/10000000000000)
theorem h382 : Model (fun x => f382 ((97/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8651904219400031/100000000000000),(53362379387/625000000000),(-36789098917/100000000000000),(78877067/50000000000000)⟩
def e383 : ℝ := (3586771/100000000000000)
theorem h383 : Model (fun x => f383 ((97/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2082453620731331/20000000000000),(8261616508587/25000000000000),(-12673982141/10000000000000),(473049643/100000000000000)⟩
def e384 : ℝ := (2960517/20000000000000)
theorem h384 : Model (fun x => f384 ((97/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(7840657861352137/50000000000000),(8261616508587/25000000000000),(-12673982141/10000000000000),(473049643/100000000000000)⟩
def e385 : ℝ := (7401293/50000000000000)
theorem h385 : Model (fun x => f385 ((97/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(4717980556140677/25000000000000),(16208515630549/20000000000000),(-255745571779/100000000000000),(177847107/25000000000000)⟩
def e386 : ℝ := (39069291/100000000000000)
theorem h386 : Model (fun x => f386 ((97/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(21207636510276993/100000000000000),(16208515630549/20000000000000),(-255745571779/100000000000000),(177847107/25000000000000)⟩
def e387 : ℝ := (9767323/25000000000000)
theorem h387 : Model (fun x => f387 ((97/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(25522658548942451/100000000000000),(38337298106469/25000000000000),(-87926006683/25000000000000),(385434063/100000000000000)⟩
def e388 : ℝ := (79101527/100000000000000)
theorem h388 : Model (fun x => f388 ((97/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(25925039501323403/100000000000000),(38337298106469/25000000000000),(-87926006683/25000000000000),(385434063/100000000000000)⟩
def e389 : ℝ := (9887691/12500000000000)
theorem h389 : Model (fun x => f389 ((97/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(6239978045073353/20000000000000),(50556726617173/20000000000000),(-16704811317/5000000000000),(-436359049/50000000000000)⟩
def e390 : ℝ := (136785237/100000000000000)
theorem h390 : Model (fun x => f390 ((97/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(31182271177747717/100000000000000),(50556726617173/20000000000000),(-16704811317/5000000000000),(-436359049/50000000000000)⟩
def e391 : ℝ := (68392619/50000000000000)
theorem h391 : Model (fun x => f391 ((97/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(586356048315811/1562500000000),(386286273692597/100000000000000),(-57481986571/50000000000000),(-406586597/12500000000000)⟩
def e392 : ℝ := (214024129/100000000000000)
theorem h392 : Model (fun x => f392 ((97/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(37530120425545237/100000000000000),(386286273692597/100000000000000),(-57481986571/50000000000000),(-406586597/12500000000000)⟩
def e393 : ℝ := (21402413/10000000000000)
theorem h393 : Model (fun x => f393 ((97/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(3818042068750103/50000000000000),(35474596880557/20000000000000),(26904881387/5000000000000),(-3551896169/100000000000000)⟩
def e394 : ℝ := (98559189/100000000000000)
theorem h394 : Model (fun x => f394 ((97/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(72416458624827/50000000000000),(316745008253/50000000000000),(-278324693/12500000000000),(3534297/50000000000000)⟩
def e395 : ℝ := (7467/2500000000000)
theorem h395 : Model (fun x => f395 ((97/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(8813861938189/4000000000000),(131597047161/50000000000000),(-1212876021/100000000000000),(698661/12500000000000)⟩
def e396 : ℝ := (105467/100000000000000)
theorem h396 : Model (fun x => f396 ((97/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(1896585992809/390625000000),(23197564103/2000000000000),(-2326174793/50000000000000),(1824717/10000000000000)⟩
def e397 : ℝ := (254807/50000000000000)
theorem h397 : Model (fun x => f397 ((97/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(213967962809877/20000000000000),(383362738699/10000000000000),(-13087389399/100000000000000),(20515931/50000000000000)⟩
def e398 : ℝ := (56479/3125000000000)
theorem h398 : Model (fun x => f398 ((97/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2357355104252267/100000000000000),(1126302083713/10000000000000),(-31723560511/100000000000000),(2164573/3125000000000)⟩
def e399 : ℝ := (700223/12500000000000)
theorem h399 : Model (fun x => f399 ((97/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(170711308371109/5000000000000),(7811542721971/25000000000000),(-13542428219/50000000000000),(-92397709/50000000000000)⟩
def e400 : ℝ := (17168603/100000000000000)
theorem h400 : Model (fun x => f400 ((97/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(4813861938189/500000000000),(131597047161/6250000000000),(-1212876021/12500000000000),(698661/1562500000000)⟩
def e401 : ℝ := (105467/12500000000000)
theorem h401 : Model (fun x => f401 ((97/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(553802652443727/50000000000000),(1369521385541/50000000000000),(-745600357/6250000000000),(25891449/50000000000000)⟩
def e402 : ℝ := (71401/6250000000000)
theorem h402 : Model (fun x => f402 ((97/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(603802652443727/50000000000000),(1369521385541/50000000000000),(-745600357/6250000000000),(25891449/50000000000000)⟩
def e403 : ℝ := (71401/6250000000000)
theorem h403 : Model (fun x => f403 ((97/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(10307594079661463/25000000000000),(470847532243453/100000000000000),(118617287/97656250000),(-4933024807/100000000000000)⟩
def e404 : ℝ := (130760497/50000000000000)
theorem h404 : Model (fun x => f404 ((97/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(121269812367/50000000000000),(-1384891359/50000000000000),(15458087/50000000000000),(-157941/50000000000000)⟩
def e405 : ℝ := (4803/100000000000000)
theorem h405 : Model (fun x => f405 ((97/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (4075940212775471/10000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(3704105962293/20000000000000),(218696831977/100000000000000),(-1246961243/100000000000000),(3598517/50000000000000)⟩
def e406 : ℝ := (457737/50000000000000)
theorem h406 : Model (fun x => f406 ((97/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(41269011233007/100000000000000),(274560385339/50000000000000),(-2223753753/100000000000000),(5192551/50000000000000)⟩
def e407 : ℝ := (6443/390625000000)
theorem h407 : Model (fun x => f407 ((97/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(53525369167217/20000000000000),(1021250458977/25000000000000),(-3678961743/100000000000000),(104190923/100000000000000)⟩
def e408 : ℝ := (6022021/50000000000000)
theorem h408 : Model (fun x => f408 ((97/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(22072317182357/20000000000000),(546788531179/100000000000000),(-3577046397/50000000000000),(58359431/50000000000000)⟩
def e409 : ℝ := (4376687/50000000000000)
theorem h409 : Model (fun x => f409 ((97/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-143948891783/10000000000000),(42650935147/50000000000000),(-488103/6250000000000),(-6131/80000000000)⟩
def e410 : ℝ := (60645091/100000000000000)
theorem h410 : Model (fun x => f410 ((97/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(5922124754394531/50000000000000),(143719259033203/25000000000000),(1138489/10240000),(10961/10240000)⟩
def e411 : ℝ := (128417969/25000000000000)
theorem h411 : Model (fun x => f411 ((97/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(47089/1600),(217/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((97/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(10218313/64000),(141267/64000),(651/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((97/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(1891066386420357601/100000000000000),(29482324558888621/25000000000000),(1582262057806487/50000000000000),(23831893038879/50000000000000)⟩
def e414 : ℝ := (22138096617/5000000000000)
theorem h414 : Model (fun x => f414 ((97/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(5288021653/100000000000000),(-329767737/100000000000000),(292893/2500000000000),(-62411/20000000000000)⟩
def e415 : ℝ := (2597/25000000000000)
theorem h415 : Model (fun x => f415 ((97/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (353984891504236009/20000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5643560051837/100000000000000),(-11657044359/100000000000000),(-328122681/100000000000000),(1492269/20000000000000)⟩
def e416 : ℝ := (10623943/50000000000000)
theorem h416 : Model (fun x => f416 ((97/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(4204071134007/100000000000000),(14728965187/20000000000000),(-335932329/100000000000000),(-40481/20000000000000)⟩
def e417 : ℝ := (81892977/100000000000000)
theorem h417 : Model (fun x => f417 ((97/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((97/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((4203877263587/2000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (12/5) (49/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (12/5) (49/20) ≤ (4204041049541/2000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(97/40)-(1/40)) (by norm_num : ((97/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel28


noncomputable section
namespace Hf4Quad.Panel29
open Hf4Quad.Dag

def p0 : Cubic := ⟨(99/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((99/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((99/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((99/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((99/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(86742857142857/20000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/50000000000000)
theorem h4 : Model (fun x => f4 ((99/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-86742857142857/20000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/50000000000000)
theorem h5 : Model (fun x => f5 ((99/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-171142857142857/50000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (3/100000000000000)
theorem h6 : Model (fun x => f6 ((99/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((99/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(9801/1600),(99/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((99/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(370778571428571/50000000000000),(1872619047619/12500000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((99/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-370778571428571/50000000000000),(-1872619047619/12500000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((99/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-135480357142857/12500000000000),(-1210119047619/6250000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/20000000000000)
theorem h11 : Model (fun x => f11 ((99/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((99/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(970299/64000),(29403/64000),(297/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((99/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(189064557/1280000),(5729229/1280000),(57871/1280000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/100000000000000)
theorem h14 : Model (fun x => f14 ((99/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-189064557/1280000),(-5729229/1280000),(-57871/1280000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/100000000000000)
theorem h15 : Model (fun x => f15 ((99/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-990906960797991/6250000000000),(-58369740048363/12500000000000),(-4596833250661/100000000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((99/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((99/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(96059601/2560000),(970299/640000),(29403/1280000),(99/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((99/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(2620673638392857/25000000000000),(211771607142857/50000000000000),(6417321428571/100000000000000),(21607142857/50000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((99/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1342954204799107/25000000000000),(-4341470610119/10000000000000),(182048817791/10000000000000),(27991484789/100000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((99/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((99/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(9287012206054687/100000000000000),(117260255126953/25000000000000),(970299/10240000),(9801/10240000)⟩
def e22 : ℝ := (484375001/100000000000000)
theorem h22 : Model (fun x => f22 ((99/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(6050316470537109/10000000000000),(381964423645019/12500000000000),(61731624023437/100000000000000),(155887939453/25000000000000)⟩
def e23 : ℝ := (631122687/20000000000000)
theorem h23 : Model (fun x => f23 ((99/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(27565673943087331/50000000000000),(1506150341529481/50000000000000),(63552112201347/100000000000000),(651543242601/100000000000000)⟩
def e24 : ℝ := (3264740427/100000000000000)
theorem h24 : Model (fun x => f24 ((99/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((99/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(459707104199707/2000000000000),(1393051830908201/100000000000000),(7035615307617/20000000000000),(473778808593/100000000000000)⟩
def e26 : ℝ := (3603759771/100000000000000)
theorem h26 : Model (fun x => f26 ((99/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(51613675931840119/100000000000000),(3128101571626669/100000000000000),(19748115982491/25000000000000),(531935784039/50000000000000)⟩
def e27 : ℝ := (4046126051/50000000000000)
theorem h27 : Model (fun x => f27 ((99/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(106745023818014781/100000000000000),(6140402254685631/100000000000000),(142544576131311/100000000000000),(1715414810679/100000000000000)⟩
def e28 : ℝ := (11356992529/100000000000000)
theorem h28 : Model (fun x => f28 ((99/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((99/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(56888754144713741/100000000000000),(4022437161747431/100000000000000),(24378407040893/20000000000000),(2052054464719/100000000000000)⟩
def e30 : ℝ := (5213467411/25000000000000)
theorem h30 : Model (fun x => f30 ((99/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(3374947914537581/25000000000000),(954530723303557/100000000000000),(180782333959/625000000000),(486955781707/100000000000000)⟩
def e31 : ℝ := (4948656369/100000000000000)
theorem h31 : Model (fun x => f31 ((99/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(24048963095233021/20000000000000),(1773733244497297/25000000000000),(171469749564751/100000000000000),(1101185296193/50000000000000)⟩
def e32 : ℝ := (8152824449/50000000000000)
theorem h32 : Model (fun x => f32 ((99/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((99/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(4204629/320),(42471/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((99/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((99/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(218691/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((99/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(1540737/64),(60143/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((99/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((99/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(1686657/64),(60143/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((99/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-1686657/64),(-60143/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((99/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((99/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(139/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((99/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(19321/1600),(139/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((99/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((99/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(405741/160),(2919/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((99/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(19717011591/50000000000000),(-283698009/50000000000000),(3061489/50000000000000),(-29367/50000000000000)⟩
def e46 : ℝ := (271/50000000000000)
theorem h46 : Model (fun x => f46 ((99/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (199941/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-1039244863095041/100000000000000),(26032134493/20000000000000),(-950678271/100000000000000),(3476439/50000000000000)⟩
def e47 : ℝ := (28436207/100000000000000)
theorem h47 : Model (fun x => f47 ((99/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((99/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(179/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((99/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((99/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((99/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(29833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (1/20000000000000)
theorem h52 : Model (fun x => f52 ((99/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(49833333333333/20000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (1/20000000000000)
theorem h53 : Model (fun x => f53 ((99/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((99/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(31145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((99/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((99/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(654062499999993/25000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((99/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((99/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(6145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((99/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(643161458333291/100000000000000),(203938802083/1562500000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (1/781250000000)
theorem h60 : Model (fun x => f60 ((99/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(155210069444441/100000000000000),(519097222221/50000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (3/25000000000000)
theorem h61 : Model (fun x => f61 ((99/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((99/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(31145833333333/2500000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((99/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1401043402777761/100000000000000),(2602430555551/50000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (13/25000000000000)
theorem h64 : Model (fun x => f64 ((99/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1501043402777761/100000000000000),(2602430555551/50000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (13/25000000000000)
theorem h65 : Model (fun x => f65 ((99/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(4827066319760551/50000000000000),(229393096426121/100000000000000),(1237764214401/100000000000000),(1062102141/50000000000000)⟩
def e66 : ℝ := (635229/100000000000000)
theorem h66 : Model (fun x => f66 ((99/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(56145833333333/25000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((99/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(100875347222221/20000000000000),(935763888887/50000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (1/5000000000000)
theorem h68 : Model (fun x => f68 ((99/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1132746086516183/100000000000000),(197022162543/3125000000000),(1169704861/10000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (17/25000000000000)
theorem h69 : Model (fun x => f69 ((99/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(109356809661256763/100000000000000),(320710631134211/10000000000000),(14806270972171/50000000000000),(16203732181/12500000000000)⟩
def e70 : ℝ := (302881153/100000000000000)
theorem h70 : Model (fun x => f70 ((99/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((99/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3259411458333261/12500000000000),(10901041666641/6250000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (63/3125000000000)
theorem h72 : Model (fun x => f72 ((99/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(1282035173611013/20000000000000),(151524479166387/100000000000000),(99804687499/12500000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (1557/100000000000000)
theorem h73 : Model (fun x => f73 ((99/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(72611016284198511/100000000000000),(2120530555648929/100000000000000),(386944974041/2000000000000),(41146382509/50000000000000)⟩
def e74 : ℝ := (4529913/2500000000000)
theorem h74 : Model (fun x => f74 ((99/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(90983912972727637/50000000000000),(5327636866991039/100000000000000),(6119973830799/12500000000000),(105961311233/50000000000000)⟩
def e75 : ℝ := (484077673/100000000000000)
theorem h75 : Model (fun x => f75 ((99/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((99/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1086470486111087/12500000000000),(3633680555547/6250000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (21/3125000000000)
theorem h77 : Model (fun x => f77 ((99/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(6043402777777/100000000000000),(20486111111/10000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (1/25000000000000)
theorem h78 : Model (fun x => f78 ((99/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(23213591399/1562500000000),(75542534721/100000000000000),(160047743/12500000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (1/25000000000000)
theorem h79 : Model (fun x => f79 ((99/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(129130915490077/100000000000000),(3714865348353/50000000000000),(19581470877/12500000000000),(289317687/20000000000000)⟩
def e80 : ℝ := (5457859/100000000000000)
theorem h80 : Model (fun x => f80 ((99/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(145003257185731/50000000000000),(17223982337559/100000000000000),(191385485663/50000000000000),(1950756111/50000000000000)⟩
def e81 : ℝ := (18307643/100000000000000)
theorem h81 : Model (fun x => f81 ((99/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(11391114528739171/6250000000000),(2672430424664299/50000000000000),(24671280808859/50000000000000),(6744504209/3125000000000)⟩
def e82 : ℝ := (125596329/25000000000000)
theorem h82 : Model (fun x => f82 ((99/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(22826698209/6250000000000),(12380582079/50000000000000),(314760561/50000000000000),(444577/6250000000000)⟩
def e83 : ℝ := (6029/20000000000000)
theorem h83 : Model (fun x => f83 ((99/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(17957002591/20000000000000),(3804449701/50000000000000),(257928793/100000000000000),(2185837/50000000000000)⟩
def e84 : ℝ := (37177/100000000000000)
theorem h84 : Model (fun x => f84 ((99/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(11036074509/50000000000000),(2244625323/100000000000000),(47555621/50000000000000),(1074703/50000000000000)⟩
def e85 : ℝ := (3439/12500000000000)
theorem h85 : Model (fun x => f85 ((99/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(2713034983/50000000000000),(160942753/25000000000000),(32734119/100000000000000),(231173/25000000000000)⟩
def e86 : ℝ := (15837/100000000000000)
theorem h86 : Model (fun x => f86 ((99/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(8139104949/50000000000000),(482828259/25000000000000),(98202357/100000000000000),(693519/25000000000000)⟩
def e87 : ℝ := (47511/100000000000000)
theorem h87 : Model (fun x => f87 ((99/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-8139104949/50000000000000),(-482828259/25000000000000),(-98202357/100000000000000),(-693519/25000000000000)⟩
def e88 : ℝ := (47511/100000000000000)
theorem h88 : Model (fun x => f88 ((99/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(91128908090808419/50000000000000),(2672429459007781/50000000000000),(49342463415361/100000000000000),(53955340153/25000000000000)⟩
def e89 : ℝ := (502432827/100000000000000)
theorem h89 : Model (fun x => f89 ((99/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3259411458333261/10000000000000),(10901041666641/5000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (63/2500000000000)
theorem h90 : Model (fun x => f90 ((99/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(158997432456307/6250000000000),(188791014419/1000000000000),(26269621671/50000000000000),(32491801/50000000000000)⟩
def e91 : ℝ := (15171/50000000000000)
theorem h91 : Model (fun x => f91 ((99/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(829180885109849221/100000000000000),(2339967278356187/20000000000000),(6755992569151/10000000000000),(204557383193/100000000000000)⟩
def e92 : ℝ := (34348459/10000000000000)
theorem h92 : Model (fun x => f92 ((99/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(6030047351/50000000000000),(-34033861/20000000000000),(354619/25000000000000),(-4563/50000000000000)⟩
def e93 : ℝ := (13/20000000000000)
theorem h93 : Model (fun x => f93 ((99/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (817413283891508993/100000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(219804652333/1000000000000),(5225752939/1562500000000),(-279639039/50000000000000),(622613/50000000000000)⟩
def e94 : ℝ := (21251/6250000000000)
theorem h94 : Model (fun x => f94 ((99/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(29833333333333/10000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (1/10000000000000)
theorem h95 : Model (fun x => f95 ((99/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(20066889632107/50000000000000),(-134226686503/100000000000000),(448918683/100000000000000),(-1501401/100000000000000)⟩
def e96 : ℝ := (2521/50000000000000)
theorem h96 : Model (fun x => f96 ((99/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (248333333333327/100000000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(11973244147157/10000000000000),(134226686501/50000000000000),(-897837371/100000000000000),(1501399/50000000000000)⟩
def e97 : ℝ := (10039/25000000000000)
theorem h97 : Model (fun x => f97 ((99/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(251438127090297/10000000000000),(2818760416521/50000000000000),(-18854584791/100000000000000),(31529379/50000000000000)⟩
def e98 : ℝ := (210819/25000000000000)
theorem h98 : Model (fun x => f98 ((99/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(1973244147157/10000000000000),(134226686501/50000000000000),(-897837371/100000000000000),(1501399/50000000000000)⟩
def e99 : ℝ := (10039/25000000000000)
theorem h99 : Model (fun x => f99 ((99/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(248074406326523/50000000000000),(7862361830697/100000000000000),(-11161409779/100000000000000),(-2657343/20000000000000)⟩
def e100 : ℝ := (1689603/100000000000000)
theorem h100 : Model (fun x => f100 ((99/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(143358575407429/100000000000000),(80356444427/12500000000000),(-57173323/4000000000000),(2370097/100000000000000)⟩
def e101 : ℝ := (24123/20000000000000)
theorem h101 : Model (fun x => f101 ((99/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(11973244147157/1000000000000),(134226686501/5000000000000),(-897837371/10000000000000),(1501399/5000000000000)⟩
def e102 : ℝ := (10039/2500000000000)
theorem h102 : Model (fun x => f102 ((99/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(1340682990123129/100000000000000),(831846321359/25000000000000),(-2081541357/20000000000000),(32398077/100000000000000)⟩
def e103 : ℝ := (20887/4000000000000)
theorem h103 : Model (fun x => f103 ((99/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(1440682990123129/100000000000000),(831846321359/25000000000000),(-2081541357/20000000000000),(32398077/100000000000000)⟩
def e104 : ℝ := (20887/4000000000000)
theorem h104 : Model (fun x => f104 ((99/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(223372860924697/3125000000000),(32445123025717/25000000000000),(2458641243/5000000000000),(-1220351441/100000000000000)⟩
def e105 : ℝ := (30299137/100000000000000)
theorem h105 : Model (fun x => f105 ((99/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(21973244147157/10000000000000),(134226686501/50000000000000),(-897837371/100000000000000),(1501399/50000000000000)⟩
def e106 : ℝ := (10039/25000000000000)
theorem h106 : Model (fun x => f106 ((99/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(482823458350569/100000000000000),(58987915071/5000000000000),(-3225007817/100000000000000),(8375693/100000000000000)⟩
def e107 : ℝ := (200927/100000000000000)
theorem h107 : Model (fun x => f107 ((99/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(530459886515587/50000000000000),(97211689469/2500000000000),(-4127128453/50000000000000),(6826187/50000000000000)⟩
def e108 : ℝ := (723441/100000000000000)
theorem h108 : Model (fun x => f108 ((99/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(75833819172337131/100000000000000),(206851487889283/12500000000000),(622268493413/12500000000000),(-2077143327/10000000000000)⟩
def e109 : ℝ := (409181847/100000000000000)
theorem h109 : Model (fun x => f109 ((99/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(3010530083556009/12500000000000),(1687485332967/1562500000000),(-1200639783/500000000000),(49772037/12500000000000)⟩
def e110 : ℝ := (506583/2500000000000)
theorem h110 : Model (fun x => f110 ((99/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(190096347750943/4000000000000),(42982903999593/50000000000000),(26306701161/100000000000000),(-812516531/100000000000000)⟩
def e111 : ℝ := (2024643/10000000000000)
theorem h111 : Model (fun x => f111 ((99/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(6302405440937049/12500000000000),(137103015797117/12500000000000),(3229569544309/100000000000000),(-7022121513/50000000000000)⟩
def e112 : ℝ := (272690573/100000000000000)
theorem h112 : Model (fun x => f112 ((99/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(126253062699833523/100000000000000),(53742891201/1953125000),(8207717491613/100000000000000),(-4351959537/12500000000000)⟩
def e113 : ℝ := (34093621/5000000000000)
theorem h113 : Model (fun x => f113 ((99/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(1003510027852003/12500000000000),(562495110989/1562500000000),(-400213261/500000000000),(16590679/12500000000000)⟩
def e114 : ℝ := (168861/2500000000000)
theorem h114 : Model (fun x => f114 ((99/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(3893692464289/100000000000000),(26486202353/25000000000000),(366341667/100000000000000),(-3635499/100000000000000)⟩
def e115 : ℝ := (40303/100000000000000)
theorem h115 : Model (fun x => f115 ((99/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(384160293299/50000000000000),(3919780783/12500000000000),(321741543/100000000000000),(-568209/100000000000000)⟩
def e116 : ℝ := (19581/100000000000000)
theorem h116 : Model (fun x => f116 ((99/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(30840696530249/50000000000000),(2794058173667/100000000000000),(36503555543/100000000000000),(46129459/100000000000000)⟩
def e117 : ℝ := (2054427/100000000000000)
theorem h117 : Model (fun x => f117 ((99/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(135534030905507/100000000000000),(6305038021319/100000000000000),(87157098631/100000000000000),(176122481/100000000000000)⟩
def e118 : ℝ := (37331/800000000000)
theorem h118 : Model (fun x => f118 ((99/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(12638859673073903/10000000000000),(2757941067512519/100000000000000),(2073718647561/25000000000000),(-6927910763/20000000000000)⟩
def e119 : ℝ := (137307759/20000000000000)
theorem h119 : Model (fun x => f119 ((99/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(9475525629/6250000000000),(206258253/2500000000000),(70385731/50000000000000),(493129/100000000000000)⟩
def e120 : ℝ := (7727/100000000000000)
theorem h120 : Model (fun x => f120 ((99/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(29916040781/100000000000000),(508747363/25000000000000),(24282369/50000000000000),(40569/10000000000000)⟩
def e121 : ℝ := (1921/100000000000000)
theorem h121 : Model (fun x => f121 ((99/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(5903165237/100000000000000),(481863723/100000000000000),(230897/1562500000000),(193053/100000000000000)⟩
def e122 : ℝ := (279/25000000000000)
theorem h122 : Model (fun x => f122 ((99/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(9318709/800000000000),(110930723/100000000000000),(4156521/100000000000000),(14723/20000000000000)⟩
def e123 : ℝ := (63/10000000000000)
theorem h123 : Model (fun x => f123 ((99/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(27956127/800000000000),(332792169/100000000000000),(12469563/100000000000000),(44169/20000000000000)⟩
def e124 : ℝ := (189/10000000000000)
theorem h124 : Model (fun x => f124 ((99/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-27956127/800000000000),(-332792169/100000000000000),(-12469563/100000000000000),(-44169/20000000000000)⟩
def e125 : ℝ := (189/10000000000000)
theorem h125 : Model (fun x => f125 ((99/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(25277718647244631/20000000000000),(55158814694407/2000000000000),(8294862120681/100000000000000),(-1731988733/5000000000000)⟩
def e126 : ℝ := (137308137/20000000000000)
theorem h126 : Model (fun x => f126 ((99/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(3010530083556009/10000000000000),(1687485332967/1250000000000),(-1200639783/400000000000),(49772037/10000000000000)⟩
def e127 : ℝ := (506583/2000000000000)
theorem h127 : Model (fun x => f127 ((99/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(2331184919336037/100000000000000),(11392299662187/100000000000000),(-17223892051/100000000000000),(2392513/50000000000000)⟩
def e128 : ℝ := (2247067/100000000000000)
theorem h128 : Model (fun x => f128 ((99/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(701810232999322757/100000000000000),(6576758373240629/100000000000000),(3196882964207/100000000000000),(-22201921989/50000000000000)⟩
def e129 : ℝ := (693923339/50000000000000)
theorem h129 : Model (fun x => f129 ((99/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(7124433023/50000000000000),(-133528047/100000000000000),(593201/50000000000000),(-9609/100000000000000)⟩
def e130 : ℝ := (109/100000000000000)
theorem h130 : Model (fun x => f130 ((99/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (139046046390285453/20000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(18008941347653/100000000000000),(224211060739/100000000000000),(-1001223811/100000000000000),(4563841/100000000000000)⟩
def e131 : ℝ := (2821/781250000000)
theorem h131 : Model (fun x => f131 ((99/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(39989406580953/100000000000000),(111731849767/20000000000000),(-1560501889/100000000000000),(5809067/100000000000000)⟩
def e132 : ℝ := (43819/6250000000000)
theorem h132 : Model (fun x => f132 ((99/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-83117570734949/20000000000000),(-5753787065203/100000000000000),(3312883951/20000000000000),(-16233057/25000000000000)⟩
def e133 : ℝ := (18879291/100000000000000)
theorem h133 : Model (fun x => f133 ((99/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(1010101010101/2500000000000),(-408121620243/100000000000000),(128826269/3125000000000),(-8328163/20000000000000)⟩
def e134 : ℝ := (424909/100000000000000)
theorem h134 : Model (fun x => f134 ((99/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (49/20))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-167914284313027/100000000000000),(-628658568637/100000000000000),(3260695351/25000000000000),(-39495127/25000000000000)⟩
def e135 : ℝ := (12849611/100000000000000)
theorem h135 : Model (fun x => f135 ((99/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(96059601/256000),(970299/64000),(29403/128000),(99/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((99/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((99/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(8732691/32000),(264627/32000),(2673/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((99/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(165921129/256000),(1499553/64000),(8019/25600),(117/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((99/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-9801/1600),(-99/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((99/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(164352969/256000),(1491633/64000),(8003/25600),(117/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((99/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((99/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(297/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((99/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-297/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((99/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(160551369/256000),(1482033/64000),(8003/25600),(117/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((99/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(161319369/256000),(1482033/64000),(8003/25600),(117/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((99/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((99/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(161319369/4000),(1482033/1000),(8003/400),(117/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((99/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((99/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(18155264589/512000),(183386511/128000),(5557167/256000),(18711/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((99/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(564023727/20000000000000),(-28486047/25000000000000),(1438689/50000000000000),(-58129/100000000000000)⟩
def e151 : ℝ := (1161/100000000000000)
theorem h151 : Model (fun x => f151 ((99/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (8705264589/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(22746987935167/20000000000000),(-10396056159/2500000000000),(3598677649/100000000000000),(-3718589/12500000000000)⟩
def e152 : ℝ := (92045793/100000000000000)
theorem h152 : Model (fun x => f152 ((99/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(219/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((99/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(39201/1600),(199/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((99/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(417/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((99/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(599520383693/12500000000000),(-6900954057/20000000000000),(248235757/100000000000000),(-1785869/100000000000000)⟩
def e156 : ℝ := (12943/100000000000000)
theorem h156 : Model (fun x => f156 ((99/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := (207/10))
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(58754496402873/50000000000000),(69531425217/20000000000000),(496471503/100000000000000),(-111617/3125000000000)⟩
def e157 : ℝ := (122109/20000000000000)
theorem h157 : Model (fun x => f157 ((99/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(108754496402873/50000000000000),(69531425217/20000000000000),(496471503/100000000000000),(-111617/3125000000000)⟩
def e158 : ℝ := (122109/20000000000000)
theorem h158 : Model (fun x => f158 ((99/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(108754496402873/100000000000000),(86914281521/50000000000000),(248235751/100000000000000),(-111617/6250000000000)⟩
def e159 : ℝ := (152637/50000000000000)
theorem h159 : Model (fun x => f159 ((99/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(8754496402873/100000000000000),(86914281521/50000000000000),(248235751/100000000000000),(-111617/6250000000000)⟩
def e160 : ℝ := (152637/50000000000000)
theorem h160 : Model (fun x => f160 ((99/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((99/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((99/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(401355879582031/100000000000000),(641510173131/100000000000000),(28628379/3125000000000),(-6590719/100000000000000)⟩
def e163 : ℝ := (1126609/100000000000000)
theorem h163 : Model (fun x => f163 ((99/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(689267541324079/25000000000000),(641510173131/100000000000000),(28628379/3125000000000),(-6590719/100000000000000)⟩
def e164 : ℝ := (112661/10000000000000)
theorem h164 : Model (fun x => f164 ((99/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((99/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(1499218886870933/50000000000000),(1372561652139/25000000000000),(8955470527/100000000000000),(-53220533/100000000000000)⟩
def e166 : ℝ := (4833227/50000000000000)
theorem h166 : Model (fun x => f166 ((99/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(4140409363061409/50000000000000),(1372561652139/25000000000000),(8955470527/100000000000000),(-53220533/100000000000000)⟩
def e167 : ℝ := (1933291/20000000000000)
theorem h167 : Model (fun x => f167 ((99/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((99/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(9005762703629673/100000000000000),(20365318250143/100000000000000),(39839046213/100000000000000),(-88284313/50000000000000)⟩
def e169 : ℝ := (8998533/25000000000000)
theorem h169 : Model (fun x => f169 ((99/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(3568702580669323/25000000000000),(20365318250143/100000000000000),(39839046213/100000000000000),(-88284313/50000000000000)⟩
def e170 : ℝ := (35994133/100000000000000)
theorem h170 : Model (fun x => f170 ((99/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((99/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15524498078893019/100000000000000),(23480948482333/50000000000000),(57081338381/50000000000000),(-327150519/100000000000000)⟩
def e172 : ℝ := (41710179/50000000000000)
theorem h172 : Model (fun x => f172 ((99/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(2232526545575913/12500000000000),(23480948482333/50000000000000),(57081338381/50000000000000),(-327150519/100000000000000)⟩
def e173 : ℝ := (83420359/100000000000000)
theorem h173 : Model (fun x => f173 ((99/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((99/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(19423784013612329/100000000000000),(16423865010961/20000000000000),(62531416789/25000000000000),(-179863937/50000000000000)⟩
def e175 : ℝ := (146661733/100000000000000)
theorem h175 : Model (fun x => f175 ((99/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(19826164965993281/100000000000000),(16423865010961/20000000000000),(62531416789/25000000000000),(-179863937/50000000000000)⟩
def e176 : ℝ := (73330867/50000000000000)
theorem h176 : Model (fun x => f176 ((99/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((99/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(21561845864768829/100000000000000),(61885998039757/50000000000000),(46398538191/10000000000000),(-106650791/100000000000000)⟩
def e178 : ℝ := (222008441/100000000000000)
theorem h178 : Model (fun x => f178 ((99/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(21544226817149781/100000000000000),(61885998039757/50000000000000),(46398538191/10000000000000),(-106650791/100000000000000)⟩
def e179 : ℝ := (111004221/50000000000000)
theorem h179 : Model (fun x => f179 ((99/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((99/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(11715157689441979/50000000000000),(172057630918819/100000000000000),(773236520949/100000000000000),(613045621/100000000000000)⟩
def e181 : ℝ := (309231393/100000000000000)
theorem h181 : Model (fun x => f181 ((99/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(23433648712217291/100000000000000),(172057630918819/100000000000000),(773236520949/100000000000000),(613045621/100000000000000)⟩
def e182 : ℝ := (154615697/50000000000000)
theorem h182 : Model (fun x => f182 ((99/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(2051497933572957/100000000000000),(55797153934413/100000000000000),(424948964709/100000000000000),(1406388571/100000000000000)⟩
def e183 : ℝ := (99774337/100000000000000)
theorem h183 : Model (fun x => f183 ((99/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(4731016195137/4000000000000),(378092756681/100000000000000),(33683951/4000000000000),(-3021423/100000000000000)⟩
def e184 : ℝ := (83833/12500000000000)
theorem h184 : Model (fun x => f184 ((99/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(208754496402873/100000000000000),(86914281521/50000000000000),(248235751/100000000000000),(-111617/6250000000000)⟩
def e185 : ℝ := (152637/50000000000000)
theorem h185 : Model (fun x => f185 ((99/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(435784397684171/100000000000000),(145149976553/20000000000000),(1338570277/100000000000000),(-6593167/100000000000000)⟩
def e186 : ℝ := (320303/25000000000000)
theorem h186 : Model (fun x => f186 ((99/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(227429881196971/25000000000000),(1136276634683/50000000000000),(1027531781/20000000000000),(-544303/3125000000000)⟩
def e187 : ℝ := (806103/20000000000000)
theorem h187 : Model (fun x => f187 ((99/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(474770103162389/25000000000000),(6325409510603/100000000000000),(105835561/625000000000),(-19017321/50000000000000)⟩
def e188 : ℝ := (5631617/50000000000000)
theorem h188 : Model (fun x => f188 ((99/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(1123072523514063/50000000000000),(14661689192659/100000000000000),(11987287641/20000000000000),(14926371/100000000000000)⟩
def e189 : ℝ := (13168231/50000000000000)
theorem h189 : Model (fun x => f189 ((99/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((99/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(108754496402873/12500000000000),(86914281521/6250000000000),(248235751/12500000000000),(-111617/781250000000)⟩
def e191 : ℝ := (152637/6250000000000)
theorem h191 : Model (fun x => f191 ((99/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(988311376101409/100000000000000),(1768721261017/100000000000000),(2827984783/100000000000000),(-17308399/100000000000000)⟩
def e192 : ℝ := (389107/12500000000000)
theorem h192 : Model (fun x => f192 ((99/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1088311376101409/100000000000000),(1768721261017/100000000000000),(2827984783/100000000000000),(-17308399/100000000000000)⟩
def e193 : ℝ := (389107/12500000000000)
theorem h193 : Model (fun x => f193 ((99/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(12222526035272719/50000000000000),(39858575282481/20000000000000),(975140129523/100000000000000),(1248412511/100000000000000)⟩
def e194 : ℝ := (358055467/100000000000000)
theorem h194 : Model (fun x => f194 ((99/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(204540370197/50000000000000),(-3335107539/100000000000000),(10871407/100000000000000),(11759/50000000000000)⟩
def e195 : ℝ := (3277/50000000000000)
theorem h195 : Model (fun x => f195 ((99/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (6061195611883883/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(8392282935827/100000000000000),(39958937047/25000000000000),(100515973/100000000000000),(-935417/50000000000000)⟩
def e196 : ℝ := (562309/100000000000000)
theorem h196 : Model (fun x => f196 ((99/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(58754496402873/25000000000000),(69531425217/10000000000000),(496471503/50000000000000),(-111617/1562500000000)⟩
def e197 : ℝ := (122109/10000000000000)
theorem h197 : Model (fun x => f197 ((99/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(45975110596603/100000000000000),(-14696932403/20000000000000),(12515041/100000000000000),(902691/100000000000000)⟩
def e198 : ℝ := (16519/12500000000000)
theorem h198 : Model (fun x => f198 ((99/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (217160835025869/100000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(108049778806791/100000000000000),(36742331007/25000000000000),(-12515043/50000000000000),(-1805383/100000000000000)⟩
def e199 : ℝ := (885457/100000000000000)
theorem h199 : Model (fun x => f199 ((99/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(8049778806791/100000000000000),(36742331007/25000000000000),(-12515043/50000000000000),(-1805383/100000000000000)⟩
def e200 : ℝ := (885457/100000000000000)
theorem h200 : Model (fun x => f200 ((99/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(398755136072681/100000000000000),(108477358211/20000000000000),(-92372937/100000000000000),(-6662723/100000000000000)⟩
def e201 : ℝ := (40847/1250000000000)
theorem h201 : Model (fun x => f201 ((99/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(1377234710893483/50000000000000),(108477358211/20000000000000),(-92372937/100000000000000),(-6662723/100000000000000)⟩
def e202 : ℝ := (3267761/100000000000000)
theorem h202 : Model (fun x => f202 ((99/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2976198117541511/100000000000000),(463427281777/10000000000000),(7887381/100000000000000),(-571993/1000000000000)⟩
def e203 : ℝ := (223597/800000000000)
theorem h203 : Model (fun x => f203 ((99/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8258579069922463/100000000000000),(463427281777/10000000000000),(7887381/100000000000000),(-571993/1000000000000)⟩
def e204 : ℝ := (13974813/50000000000000)
theorem h204 : Model (fun x => f204 ((99/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4461688208817579/50000000000000),(8572449681143/50000000000000),(148511009/3125000000000),(-212051071/100000000000000)⟩
def e205 : ℝ := (103575547/100000000000000)
theorem h205 : Model (fun x => f205 ((99/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14192424036682777/100000000000000),(8572449681143/50000000000000),(148511009/3125000000000),(-212051071/100000000000000)⟩
def e206 : ℝ := (25893887/25000000000000)
theorem h206 : Model (fun x => f206 ((99/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(7667441389478789/50000000000000),(39383535507497/100000000000000),(26780272891/100000000000000),(-60331901/12500000000000)⟩
def e207 : ℝ := (5962687/2500000000000)
theorem h207 : Model (fun x => f207 ((99/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(17670597064671863/100000000000000),(39383535507497/100000000000000),(26780272891/100000000000000),(-60331901/12500000000000)⟩
def e208 : ℝ := (238507481/100000000000000)
theorem h208 : Model (fun x => f208 ((99/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(19093041042217251/100000000000000),(17131045014951/25000000000000),(41197387947/50000000000000),(-811028787/100000000000000)⟩
def e209 : ℝ := (104074841/25000000000000)
theorem h209 : Model (fun x => f209 ((99/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(19495421994598203/100000000000000),(17131045014951/25000000000000),(41197387947/50000000000000),(-811028787/100000000000000)⟩
def e210 : ℝ := (83259873/20000000000000)
theorem h210 : Model (fun x => f210 ((99/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(263309504282673/1250000000000),(25673128726413/25000000000000),(4621429411/2500000000000),(-1124338461/100000000000000)⟩
def e211 : ℝ := (62610457/10000000000000)
theorem h211 : Model (fun x => f211 ((99/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(2630892661874349/12500000000000),(25673128726413/25000000000000),(4621429411/2500000000000),(-1124338461/100000000000000)⟩
def e212 : ℝ := (626104571/100000000000000)
theorem h212 : Model (fun x => f212 ((99/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(22741389614394639/100000000000000),(141891876495159/100000000000000),(345396147669/100000000000000),(-674423707/50000000000000)⟩
def e213 : ℝ := (173651013/20000000000000)
theorem h213 : Model (fun x => f213 ((99/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(5686180736931993/25000000000000),(141891876495159/100000000000000),(345396147669/100000000000000),(-674423707/50000000000000)⟩
def e214 : ℝ := (434127533/50000000000000)
theorem h214 : Model (fun x => f214 ((99/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(366179977501907/20000000000000),(22424873885491/50000000000000),(46129626783/20000000000000),(-47097871/100000000000000)⟩
def e215 : ℝ := (278459587/100000000000000)
theorem h215 : Model (fun x => f215 ((99/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(29186886750491/25000000000000),(79400014763/25000000000000),(40477479/25000000000000),(-1987499/50000000000000)⟩
def e216 : ℝ := (60043/3125000000000)
theorem h216 : Model (fun x => f216 ((99/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(208049778806791/100000000000000),(36742331007/25000000000000),(-12515043/50000000000000),(-1805383/100000000000000)⟩
def e217 : ℝ := (885457/100000000000000)
theorem h217 : Model (fun x => f217 ((99/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(216423552307773/50000000000000),(152884676777/25000000000000),(6990609/6250000000000),(-1896441/25000000000000)⟩
def e218 : ℝ := (369229/10000000000000)
theorem h218 : Model (fun x => f218 ((99/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(450268721862121/50000000000000),(119278586949/6250000000000),(511567723/50000000000000),(-11792699/50000000000000)⟩
def e219 : ℝ := (577377/5000000000000)
theorem h219 : Model (fun x => f219 ((99/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(374713231948123/20000000000000),(66175689683/1250000000000),(2354036331/50000000000000),(-8037689/12500000000000)⟩
def e220 : ℝ := (2006361/6250000000000)
theorem h220 : Model (fun x => f220 ((99/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(1093671266478033/50000000000000),(12131126783037/100000000000000),(253439711/1000000000000),(-63010107/50000000000000)⟩
def e221 : ℝ := (74087439/100000000000000)
theorem h221 : Model (fun x => f221 ((99/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(108049778806791/12500000000000),(36742331007/3125000000000),(-12515043/6250000000000),(-1805383/12500000000000)⟩
def e222 : ℝ := (885457/12500000000000)
theorem h222 : Model (fun x => f222 ((99/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(245286444364073/25000000000000),(373338662819/25000000000000),(-9582693/25000000000000),(-9209031/50000000000000)⟩
def e223 : ℝ := (1125629/12500000000000)
theorem h223 : Model (fun x => f223 ((99/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(270286444364073/25000000000000),(373338662819/25000000000000),(-9582693/25000000000000),(-9209031/50000000000000)⟩
def e224 : ℝ := (1125629/12500000000000)
theorem h224 : Model (fun x => f224 ((99/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(23648361433560009/100000000000000),(163819946427911/100000000000000),(227163797087/50000000000000),(-139150291/10000000000000)⟩
def e225 : ℝ := (1004295863/100000000000000)
theorem h225 : Model (fun x => f225 ((99/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(422862278559/100000000000000),(-1464652763/50000000000000),(12168313/100000000000000),(-627/20000000000000)⟩
def e226 : ℝ := (93/500000000000)
theorem h226 : Model (fun x => f226 ((99/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (23484084763739151/100000000000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(967773122807/12500000000000),(136020013771/100000000000000),(-115672557/100000000000000),(-1555489/100000000000000)⟩
def e227 : ℝ := (39067/2500000000000)
theorem h227 : Model (fun x => f227 ((99/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(16134467918283/100000000000000),(295855761959/100000000000000),(-1894573/12500000000000),(-3426323/100000000000000)⟩
def e228 : ℝ := (2124989/100000000000000)
theorem h228 : Model (fun x => f228 ((99/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(4587631838469/25000000000000),(269397438561/100000000000000),(-83363011/12500000000000),(2013199/100000000000000)⟩
def e229 : ℝ := (17623643/100000000000000)
theorem h229 : Model (fun x => f229 ((99/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3707177243207/50000000000000),(33954980363/100000000000000),(-612435797/100000000000000),(6999633/100000000000000)⟩
def e230 : ℝ := (7420697/100000000000000)
theorem h230 : Model (fun x => f230 ((99/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-160499929826613/100000000000000),(-297351794137/50000000000000),(12430345607/100000000000000),(-1207847/800000000000)⟩
def e231 : ℝ := (5067577/25000000000000)
theorem h231 : Model (fun x => f231 ((99/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((99/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-9801/320),(-99/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((99/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2079/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((99/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6831/320),(-3/32),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((99/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((99/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15151/320),(-3/32),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((99/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((99/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(378775/32),(-375/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((99/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(13959/1600),(21/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((99/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23559/1600),(21/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((99/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((99/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4452651/1600),(3969/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((99/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(17966824707/50000000000000),(-4003813/6250000000000),(1639467/100000000000000),(-2821/50000000000000)⟩
def e244 : ℝ := (41/50000000000000)
theorem h244 : Model (fun x => f244 ((99/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (1111131/400))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(21266825088731/5000000000000),(-1600467042679/100000000000000),(-7165823951/100000000000000),(-55160113/100000000000000)⟩
def e245 : ℝ := (1062803/50000000000000)
theorem h245 : Model (fun x => f245 ((99/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(891/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((99/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(81081/1600),(459/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((99/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(114681/1600),(459/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((99/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(32041/1600),(179/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((99/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3674493921/2560000),(17617359/640000),(237683/1280000),(319/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((99/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((99/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(173889/160),(1251/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((99/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(46006360379/50000000000000),(-33098101/2500000000000),(285739/2000000000000),(-68523/50000000000000)⟩
def e253 : ℝ := (63/5000000000000)
theorem h253 : Model (fun x => f253 ((99/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (85689/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(66035192007801/50000000000000),(316276113241/50000000000000),(1148769349/100000000000000),(-3406887/100000000000000)⟩
def e254 : ℝ := (919439/25000000000000)
theorem h254 : Model (fun x => f254 ((99/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(116035192007801/50000000000000),(316276113241/50000000000000),(1148769349/100000000000000),(-3406887/100000000000000)⟩
def e255 : ℝ := (919439/25000000000000)
theorem h255 : Model (fun x => f255 ((99/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(116035192007801/100000000000000),(316276113241/100000000000000),(287192337/50000000000000),(-425861/25000000000000)⟩
def e256 : ℝ := (1838879/100000000000000)
theorem h256 : Model (fun x => f256 ((99/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(16035192007801/100000000000000),(316276113241/100000000000000),(287192337/50000000000000),(-425861/25000000000000)⟩
def e257 : ℝ := (1838879/100000000000000)
theorem h257 : Model (fun x => f257 ((99/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(214112556681061/50000000000000),(291802366383/25000000000000),(2119752963/100000000000000),(-157163/2500000000000)⟩
def e258 : ℝ := (3393171/50000000000000)
theorem h258 : Model (fun x => f258 ((99/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(2783939399076407/100000000000000),(291802366383/25000000000000),(2119752963/100000000000000),(-157163/2500000000000)⟩
def e259 : ℝ := (6786343/100000000000000)
theorem h259 : Model (fun x => f259 ((99/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(323034942709913/10000000000000),(5079654535423/50000000000000),(22141785393/100000000000000),(-516361/1250000000000)⟩
def e260 : ℝ := (59138493/100000000000000)
theorem h260 : Model (fun x => f260 ((99/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(4256365189740041/50000000000000),(5079654535423/50000000000000),(22141785393/100000000000000),(-516361/1250000000000)⟩
def e261 : ℝ := (29569247/50000000000000)
theorem h261 : Model (fun x => f261 ((99/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(9877763040936119/100000000000000),(38712106561927/100000000000000),(53359774847/50000000000000),(-64559741/100000000000000)⟩
def e262 : ℝ := (7053501/3125000000000)
theorem h262 : Model (fun x => f262 ((99/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(7573405329991869/50000000000000),(38712106561927/100000000000000),(53359774847/50000000000000),(-64559741/100000000000000)⟩
def e263 : ℝ := (225712033/100000000000000)
theorem h263 : Model (fun x => f263 ((99/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(87878154161851/500000000000),(46412705607383/50000000000000),(66654067883/20000000000000),(113477697/50000000000000)⟩
def e264 : ℝ := (542118759/100000000000000)
theorem h264 : Model (fun x => f264 ((99/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(3982269023616897/20000000000000),(46412705607383/50000000000000),(66654067883/20000000000000),(113477697/50000000000000)⟩
def e265 : ℝ := (13552969/2500000000000)
theorem h265 : Model (fun x => f265 ((99/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(11552083769552621/50000000000000),(170684972568563/100000000000000),(4966644973/625000000000),(60455957/4000000000000)⟩
def e266 : ℝ := (124960013/12500000000000)
theorem h266 : Model (fun x => f266 ((99/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(11753274245743097/50000000000000),(170684972568563/100000000000000),(4966644973/625000000000),(60455957/4000000000000)⟩
def e267 : ℝ := (199936021/20000000000000)
theorem h267 : Model (fun x => f267 ((99/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(13637934338251427/50000000000000),(272400233574377/100000000000000),(159694277397/10000000000000),(2423525973/50000000000000)⟩
def e268 : ℝ := (32100011/2000000000000)
theorem h268 : Model (fun x => f268 ((99/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(13629124814441903/50000000000000),(272400233574377/100000000000000),(159694277397/10000000000000),(2423525973/50000000000000)⟩
def e269 : ℝ := (1605000551/100000000000000)
theorem h269 : Model (fun x => f269 ((99/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(31629162294841027/100000000000000),(402291466521489/100000000000000),(717779923377/25000000000000),(1471916343/12500000000000)⟩
def e270 : ℝ := (2393598973/100000000000000)
theorem h270 : Model (fun x => f270 ((99/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(790812390704359/2500000000000),(402291466521489/100000000000000),(717779923377/25000000000000),(1471916343/12500000000000)⟩
def e271 : ℝ := (1196799487/50000000000000)
theorem h271 : Model (fun x => f271 ((99/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(1014466282167403/20000000000000),(82277118390819/50000000000000),(957216788367/50000000000000),(12740721347/100000000000000)⟩
def e272 : ℝ := (513718171/50000000000000)
theorem h272 : Model (fun x => f272 ((99/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(16830207230359/12500000000000),(183495797637/25000000000000),(583320629/25000000000000),(-159953/50000000000000)⟩
def e273 : ℝ := (1071661/25000000000000)
theorem h273 : Model (fun x => f273 ((99/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(216035192007801/100000000000000),(316276113241/100000000000000),(287192337/50000000000000),(-425861/25000000000000)⟩
def e274 : ℝ := (1838879/100000000000000)
theorem h274 : Model (fun x => f274 ((99/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(233356020929237/50000000000000),(136653541703/10000000000000),(435256483/12500000000000),(-1863397/50000000000000)⟩
def e275 : ℝ := (3982201/50000000000000)
theorem h275 : Model (fun x => f275 ((99/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(504131127876241/50000000000000),(4428296118053/100000000000000),(14525204973/100000000000000),(2860703/100000000000000)⟩
def e276 : ℝ := (25853757/100000000000000)
theorem h276 : Model (fun x => f276 ((99/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(108910065007853/5000000000000),(12755570695079/100000000000000),(3198531323/6250000000000),(1207603/2000000000000)⟩
def e277 : ℝ := (74574831/100000000000000)
theorem h277 : Model (fun x => f277 ((99/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1466383170843229/50000000000000),(518155363291/1562500000000),(106676112229/50000000000000),(149515811/20000000000000)⟩
def e278 : ℝ := (196476331/100000000000000)
theorem h278 : Model (fun x => f278 ((99/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(116035192007801/12500000000000),(316276113241/12500000000000),(287192337/6250000000000),(-425861/3125000000000)⟩
def e279 : ℝ := (1838879/12500000000000)
theorem h279 : Model (fun x => f279 ((99/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(1660817490477/156250000000),(816048024119/25000000000000),(1732089977/25000000000000),(-6973729/50000000000000)⟩
def e280 : ℝ := (4749419/25000000000000)
theorem h280 : Model (fun x => f280 ((99/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(1817067490477/156250000000),(816048024119/25000000000000),(1732089977/25000000000000),(-6973729/50000000000000)⟩
def e281 : ℝ := (4749419/25000000000000)
theorem h281 : Model (fun x => f281 ((99/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(17052910005259597/50000000000000),(9627581134893/2000000000000),(941696160243/25000000000000),(8773264549/50000000000000)⟩
def e282 : ℝ := (2889375109/100000000000000)
theorem h282 : Model (fun x => f282 ((99/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(146602544623/50000000000000),(-2069189207/50000000000000),(26027471/100000000000000),(-30573/50000000000000)⟩
def e283 : ℝ := (5137/20000000000000)
theorem h283 : Model (fun x => f283 ((99/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (6724130746645873/20000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(14872333839997/100000000000000),(272569128621/100000000000000),(123539249/100000000000000),(-428457/20000000000000)⟩
def e284 : ℝ := (4532627/100000000000000)
theorem h284 : Model (fun x => f284 ((99/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(66035192007801/25000000000000),(316276113241/25000000000000),(1148769349/50000000000000),(-3406887/50000000000000)⟩
def e285 : ℝ := (919439/12500000000000)
theorem h285 : Model (fun x => f285 ((99/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(43090375544549/100000000000000),(-1835172839/1562500000000),(13354261/12500000000000),(46139/5000000000000)⟩
def e286 : ℝ := (691403/100000000000000)
theorem h286 : Model (fun x => f286 ((99/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (28929584491891/12500000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(113819248910901/100000000000000),(58725530847/25000000000000),(-106834089/50000000000000),(-461391/25000000000000)⟩
def e287 : ℝ := (5035353/100000000000000)
theorem h287 : Model (fun x => f287 ((99/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(13819248910901/100000000000000),(58725530847/25000000000000),(-106834089/50000000000000),(-461391/25000000000000)⟩
def e288 : ℝ := (5035353/100000000000000)
theorem h288 : Model (fun x => f288 ((99/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(420047228123563/100000000000000),(173380138691/20000000000000),(-197134331/25000000000000),(-681101/10000000000000)⟩
def e289 : ℝ := (4645713/25000000000000)
theorem h289 : Model (fun x => f289 ((99/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(346970189229731/12500000000000),(173380138691/20000000000000),(-197134331/25000000000000),(-681101/10000000000000)⟩
def e290 : ℝ := (18582853/100000000000000)
theorem h290 : Model (fun x => f290 ((99/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(3159350906608093/100000000000000),(1501404518857/20000000000000),(-74875909/1562500000000),(-31342639/50000000000000)⟩
def e291 : ℝ := (32207597/20000000000000)
theorem h291 : Model (fun x => f291 ((99/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(1688346371797809/20000000000000),(1501404518857/20000000000000),(-74875909/1562500000000),(-31342639/50000000000000)⟩
def e292 : ℝ := (80518993/50000000000000)
theorem h292 : Model (fun x => f292 ((99/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(9608315796973571/100000000000000),(28374244119873/100000000000000),(-5857423801/100000000000000),(-127221121/50000000000000)⟩
def e293 : ℝ := (609395893/100000000000000)
theorem h293 : Model (fun x => f293 ((99/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(1487736341602119/10000000000000),(28374244119873/100000000000000),(-5857423801/100000000000000),(-127221121/50000000000000)⟩
def e294 : ℝ := (304697947/50000000000000)
theorem h294 : Model (fun x => f294 ((99/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8466651648930241/50000000000000),(8405324263721/12500000000000),(28196634811/100000000000000),(-39910091/6250000000000)⟩
def e295 : ℝ := (361677243/25000000000000)
theorem h295 : Model (fun x => f295 ((99/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(19269017583574767/100000000000000),(8405324263721/12500000000000),(28196634811/100000000000000),(-39910091/6250000000000)⟩
def e296 : ℝ := (1446708973/100000000000000)
theorem h296 : Model (fun x => f296 ((99/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(4386370217226849/20000000000000),(121798347023767/100000000000000),(29775144111/20000000000000),(-1159869437/100000000000000)⟩
def e297 : ℝ := (1313243671/50000000000000)
theorem h297 : Model (fun x => f297 ((99/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(22334232038515197/100000000000000),(121798347023767/100000000000000),(29775144111/20000000000000),(-1159869437/100000000000000)⟩
def e298 : ℝ := (2626487343/100000000000000)
theorem h298 : Model (fun x => f298 ((99/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(2542065515625581/10000000000000),(191093549069219/100000000000000),(407834983689/100000000000000),(-410719827/25000000000000)⟩
def e299 : ℝ := (2065831203/50000000000000)
theorem h299 : Model (fun x => f299 ((99/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(12701518054318381/50000000000000),(191093549069219/100000000000000),(407834983689/100000000000000),(-410719827/25000000000000)⟩
def e300 : ℝ := (4131662407/100000000000000)
theorem h300 : Model (fun x => f300 ((99/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(5782708979883067/20000000000000),(277173513491977/100000000000000),(858799315241/100000000000000),(-1789035247/100000000000000)⟩
def e301 : ℝ := (1502344591/25000000000000)
theorem h301 : Model (fun x => f301 ((99/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(7229219558187167/25000000000000),(277173513491977/100000000000000),(858799315241/100000000000000),(-1789035247/100000000000000)⟩
def e302 : ℝ := (1201875673/20000000000000)
theorem h302 : Model (fun x => f302 ((99/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(499511922530711/12500000000000),(21245931746159/20000000000000),(28319196673/4000000000000),(322097751/50000000000000)⟩
def e303 : ℝ := (2325812199/100000000000000)
theorem h303 : Model (fun x => f303 ((99/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(8096763389151/6250000000000),(534727665031/100000000000000),(16349761/25000000000000),(-5205037/100000000000000)⟩
def e304 : ℝ := (5747153/50000000000000)
theorem h304 : Model (fun x => f304 ((99/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(213819248910901/100000000000000),(58725530847/25000000000000),(-106834089/50000000000000),(-461391/25000000000000)⟩
def e305 : ℝ := (5035353/100000000000000)
theorem h305 : Model (fun x => f305 ((99/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(228593356024109/50000000000000),(1004531911807/100000000000000),(-11310541/3125000000000),(-1779233/20000000000000)⟩
def e306 : ℝ := (5391253/25000000000000)
theorem h306 : Model (fun x => f306 ((99/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(977553193821943/100000000000000),(644364776669/20000000000000),(608912631/100000000000000),(-30455951/100000000000000)⟩
def e307 : ℝ := (69271107/100000000000000)
theorem h307 : Model (fun x => f307 ((99/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1045098448367301/50000000000000),(1837034567627/20000000000000),(6781385029/100000000000000),(-2215393/2500000000000)⟩
def e308 : ℝ := (19779571/10000000000000)
theorem h308 : Model (fun x => f308 ((99/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2707812753535641/100000000000000),(23076088445873/100000000000000),(59267792239/100000000000000),(-22665831/12500000000000)⟩
def e309 : ℝ := (499556757/100000000000000)
theorem h309 : Model (fun x => f309 ((99/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(113819248910901/12500000000000),(58725530847/3125000000000),(-106834089/6250000000000),(-461391/3125000000000)⟩
def e310 : ℝ := (5035353/12500000000000)
theorem h310 : Model (fun x => f310 ((99/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(130012775689203/12500000000000),(482788930427/20000000000000),(-82197319/5000000000000),(-19969549/100000000000000)⟩
def e311 : ℝ := (5177713/10000000000000)
theorem h311 : Model (fun x => f311 ((99/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(142512775689203/12500000000000),(482788930427/20000000000000),(-82197319/5000000000000),(-19969549/100000000000000)⟩
def e312 : ℝ := (5177713/10000000000000)
theorem h312 : Model (fun x => f312 ((99/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(15435916462119517/50000000000000),(13138243778859/4000000000000),(594121209849/50000000000000),(-194589241/12500000000000)⟩
def e313 : ℝ := (3565750193/50000000000000)
theorem h313 : Model (fun x => f313 ((99/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(161959933259/50000000000000),(-3446295351/100000000000000),(12099401/50000000000000),(-339/312500000000)⟩
def e314 : ℝ := (38251/50000000000000)
theorem h314 : Model (fun x => f314 ((99/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (30542179899133547/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(12944146821623/100000000000000),(51595429863/25000000000000),(-20034649/5000000000000),(-470531/50000000000000)⟩
def e315 : ℝ := (10787891/100000000000000)
theorem h315 : Model (fun x => f315 ((99/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(1390824033081/5000000000000),(478950848073/100000000000000),(-277153731/100000000000000),(-3083347/100000000000000)⟩
def e316 : ℝ := (7660259/50000000000000)
theorem h316 : Model (fun x => f316 ((99/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(29578411440737/25000000000000),(1591959176991/100000000000000),(-2709391623/25000000000000),(-58343223/100000000000000)⟩
def e317 : ℝ := (16551719/25000000000000)
theorem h317 : Model (fun x => f317 ((99/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(23901746618777/50000000000000),(16035226103/10000000000000),(-2999267277/50000000000000),(37018237/100000000000000)⟩
def e318 : ℝ := (7101613/25000000000000)
theorem h318 : Model (fun x => f318 ((99/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-112696436589059/100000000000000),(-108587831811/25000000000000),(6431811053/100000000000000),(-56981319/50000000000000)⟩
def e319 : ℝ := (1216919/2500000000000)
theorem h319 : Model (fun x => f319 ((99/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((99/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-107811/1600),(-1089/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((99/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((99/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(9603/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((99/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(276309/1600),(851/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((99/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((99/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(449109/1600),(851/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((99/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2245545/32),(4255/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((99/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((99/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(269453799523033923/25000000000000),(384296772527439/20000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (69701/50000000000000)
theorem h329 : Model (fun x => f329 ((99/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(9278028383/100000000000000),(-8270241/50000000000000),(105827/25000000000000),(-1457/100000000000000)⟩
def e330 : ℝ := (3/12500000000000)
theorem h330 : Model (fun x => f330 ((99/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (537923982306791009/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(651069695165741/100000000000000),(1306675777707/100000000000000),(1169945703/12500000000000),(38759953/100000000000000)⟩
def e331 : ℝ := (2808121/100000000000000)
theorem h331 : Model (fun x => f331 ((99/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((99/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(459/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((99/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((99/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((99/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(745806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((99/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((99/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((99/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(3308765043565477/100000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (1077/100000000000000)
theorem h339 : Model (fun x => f339 ((99/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3844193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((99/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((99/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((99/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(270779369554283/12500000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1077/100000000000000)
theorem h343 : Model (fun x => f343 ((99/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2308152209043/50000000000000),(-3002128153/50000000000000),(7809513/100000000000000),(-5079/50000000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((99/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (1081708707399353/50000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(76371333445099/50000000000000),(206335767947/25000000000000),(-53674661/5000000000000),(1396237/100000000000000)⟩
def e345 : ℝ := (1453/50000000000000)
theorem h345 : Model (fun x => f345 ((99/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(126371333445099/50000000000000),(206335767947/25000000000000),(-53674661/5000000000000),(1396237/100000000000000)⟩
def e346 : ℝ := (1453/50000000000000)
theorem h346 : Model (fun x => f346 ((99/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(126371333445099/100000000000000),(206335767947/50000000000000),(-53674661/10000000000000),(349059/50000000000000)⟩
def e347 : ℝ := (727/50000000000000)
theorem h347 : Model (fun x => f347 ((99/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(26371333445099/100000000000000),(206335767947/50000000000000),(-53674661/10000000000000),(349059/50000000000000)⟩
def e348 : ℝ := (727/50000000000000)
theorem h348 : Model (fun x => f348 ((99/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(93274079447573/20000000000000),(190369309713/12500000000000),(-396170117/20000000000000),(2576387/100000000000000)⟩
def e349 : ℝ := (671/12500000000000)
theorem h349 : Model (fun x => f349 ((99/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(56441693659043/2000000000000),(190369309713/12500000000000),(-396170117/20000000000000),(2576387/100000000000000)⟩
def e350 : ℝ := (5369/100000000000000)
theorem h350 : Model (fun x => f350 ((99/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1783153022398263/50000000000000),(3392629521651/25000000000000),(-11365871531/100000000000000),(3304241/50000000000000)⟩
def e351 : ℝ := (19947/25000000000000)
theorem h351 : Model (fun x => f351 ((99/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4424343498588739/50000000000000),(3392629521651/25000000000000),(-11365871531/100000000000000),(3304241/50000000000000)⟩
def e352 : ℝ := (79789/100000000000000)
theorem h352 : Model (fun x => f352 ((99/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(2795550937679067/25000000000000),(26832628599577/50000000000000),(-2928282741/50000000000000),(-49617509/100000000000000)⟩
def e353 : ℝ := (8263/2000000000000)
theorem h353 : Model (fun x => f353 ((99/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(16451251369763887/100000000000000),(26832628599577/50000000000000),(-2928282741/50000000000000),(-49617509/100000000000000)⟩
def e354 : ℝ := (413151/100000000000000)
theorem h354 : Model (fun x => f354 ((99/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(10394832862187869/50000000000000),(1357071328207/1000000000000),(125758687201/100000000000000),(-260067989/100000000000000)⟩
def e355 : ℝ := (482673/50000000000000)
theorem h355 : Model (fun x => f355 ((99/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(23125380010090023/100000000000000),(1357071328207/1000000000000),(125758687201/100000000000000),(-260067989/100000000000000)⟩
def e356 : ℝ := (965347/100000000000000)
theorem h356 : Model (fun x => f356 ((99/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(29223851082997131/100000000000000),(8341461693581/3125000000000),(297411473007/50000000000000),(-15065683/4000000000000)⟩
def e357 : ℝ := (591311/25000000000000)
theorem h357 : Model (fun x => f357 ((99/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(29626232035378083/100000000000000),(8341461693581/3125000000000),(297411473007/50000000000000),(-15065683/4000000000000)⟩
def e358 : ℝ := (473049/20000000000000)
theorem h358 : Model (fun x => f358 ((99/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(37439064472646377/100000000000000),(459577950639609/100000000000000),(67767948447/4000000000000),(752803021/100000000000000)⟩
def e359 : ℝ := (6323123/100000000000000)
theorem h359 : Model (fun x => f359 ((99/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(37421445425027329/100000000000000),(459577950639609/100000000000000),(67767948447/4000000000000),(752803021/100000000000000)⟩
def e360 : ℝ := (1580781/25000000000000)
theorem h360 : Model (fun x => f360 ((99/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(4728997957803703/10000000000000),(2871884523563/390625000000),(959167637581/25000000000000),(2868639917/50000000000000)⟩
def e361 : ℝ := (11353907/100000000000000)
theorem h361 : Model (fun x => f361 ((99/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(47293312911370363/100000000000000),(2871884523563/390625000000),(959167637581/25000000000000),(2868639917/50000000000000)⟩
def e362 : ℝ := (2838477/25000000000000)
theorem h362 : Model (fun x => f362 ((99/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(779492327818221/6250000000000),(389048727196457/100000000000000),(947976780791/25000000000000),(274596669/2000000000000)⟩
def e363 : ℝ := (11959037/100000000000000)
theorem h363 : Model (fun x => f363 ((99/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(159697139166923/100000000000000),(208599409063/20000000000000),(86597567/25000000000000),(-2665559/100000000000000)⟩
def e364 : ℝ := (617/5000000000000)
theorem h364 : Model (fun x => f364 ((99/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(226371333445099/100000000000000),(206335767947/50000000000000),(-53674661/10000000000000),(349059/50000000000000)⟩
def e365 : ℝ := (727/50000000000000)
theorem h365 : Model (fun x => f365 ((99/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(512439806057121/100000000000000),(1868340117103/100000000000000),(-90887869/12500000000000),(-1269323/100000000000000)⟩
def e366 : ℝ := (953/6250000000000)
theorem h366 : Model (fun x => f366 ((99/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(145002102759373/12500000000000),(6344079654563/100000000000000),(3313651921/100000000000000),(-12324749/100000000000000)⟩
def e367 : ℝ := (53771/100000000000000)
theorem h367 : Model (fun x => f367 ((99/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(1312972774159301/50000000000000),(19148236945139/100000000000000),(1372750901/5000000000000),(-40178547/100000000000000)⟩
def e368 : ℝ := (20419/12500000000000)
theorem h368 : Model (fun x => f368 ((99/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(4193559916745977/100000000000000),(28983860541417/50000000000000),(10106257749/4000000000000),(218522537/100000000000000)⟩
def e369 : ℝ := (1424223/100000000000000)
theorem h369 : Model (fun x => f369 ((99/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(126371333445099/12500000000000),(206335767947/6250000000000),(-53674661/1250000000000),(349059/6250000000000)⟩
def e370 : ℝ := (727/6250000000000)
theorem h370 : Model (fun x => f370 ((99/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(234133561345543/20000000000000),(4344369332467/100000000000000),(-986895653/25000000000000),(583877/20000000000000)⟩
def e371 : ℝ := (5993/25000000000000)
theorem h371 : Model (fun x => f371 ((99/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(254133561345543/20000000000000),(4344369332467/100000000000000),(-986895653/25000000000000),(583877/20000000000000)⟩
def e372 : ℝ := (5993/25000000000000)
theorem h372 : Model (fun x => f372 ((99/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(53286215817928697/100000000000000),(459380450527513/50000000000000),(86925183553/1562500000000),(5793563533/50000000000000)⟩
def e373 : ℝ := (10195737/50000000000000)
theorem h373 : Model (fun x => f373 ((99/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(93832896993/50000000000000),(-3235733507/100000000000000),(7239549/20000000000000),(-40889/12500000000000)⟩
def e374 : ℝ := (2713/100000000000000)
theorem h374 : Model (fun x => f374 ((99/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (52361880097607739/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(73142023303/312500000000),(163277335957/50000000000000),(-957929093/100000000000000),(62001/2000000000000)⟩
def e375 : ℝ := (723637/100000000000000)
theorem h375 : Model (fun x => f375 ((99/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(76371333445099/25000000000000),(206335767947/12500000000000),(-53674661/2500000000000),(1396237/50000000000000)⟩
def e376 : ℝ := (1453/25000000000000)
theorem h376 : Model (fun x => f376 ((99/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(1978296763867/5000000000000),(-129204423463/100000000000000),(589974541/100000000000000),(-1346973/50000000000000)⟩
def e377 : ℝ := (3133/25000000000000)
theorem h377 : Model (fun x => f377 ((99/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (251916248926047/100000000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(120868129445317/100000000000000),(64602211731/25000000000000),(-235989817/20000000000000),(5387887/100000000000000)⟩
def e378 : ℝ := (50809/50000000000000)
theorem h378 : Model (fun x => f378 ((99/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(20868129445317/100000000000000),(64602211731/25000000000000),(-235989817/20000000000000),(5387887/100000000000000)⟩
def e379 : ℝ := (50809/50000000000000)
theorem h379 : Model (fun x => f379 ((99/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(55757619238167/12500000000000),(953651696981/100000000000000),(-870914801/20000000000000),(4970967/25000000000000)⟩
def e380 : ℝ := (187511/50000000000000)
theorem h380 : Model (fun x => f380 ((99/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(2801775239619621/100000000000000),(953651696981/100000000000000),(-870914801/20000000000000),(4970967/25000000000000)⟩
def e381 : ℝ := (375023/100000000000000)
theorem h381 : Model (fun x => f381 ((99/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(846613330847571/25000000000000),(8392696057667/100000000000000),(-7171698619/20000000000000),(76242267/50000000000000)⟩
def e382 : ℝ := (691391/20000000000000)
theorem h382 : Model (fun x => f382 ((99/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(2167208568942809/25000000000000),(8392696057667/100000000000000),(-7171698619/20000000000000),(76242267/50000000000000)⟩
def e383 : ℝ := (864239/25000000000000)
theorem h383 : Model (fun x => f383 ((99/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(5238928916919593/50000000000000),(6509025885741/20000000000000),(-6197092573/5000000000000),(22984057/5000000000000)⟩
def e384 : ℝ := (14278069/100000000000000)
theorem h384 : Model (fun x => f384 ((99/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(3149381090577361/20000000000000),(6509025885741/20000000000000),(-6197092573/5000000000000),(22984057/5000000000000)⟩
def e385 : ℝ := (1427807/10000000000000)
theorem h385 : Model (fun x => f385 ((99/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(2379123758303363/12500000000000),(1600561719461/2000000000000),(-251512170581/100000000000000),(699740801/100000000000000)⟩
def e386 : ℝ := (37745521/100000000000000)
theorem h386 : Model (fun x => f386 ((99/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(21368704352141189/100000000000000),(1600561719461/2000000000000),(-251512170581/100000000000000),(699740801/100000000000000)⟩
def e387 : ℝ := (18872761/50000000000000)
theorem h387 : Model (fun x => f387 ((99/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(25827953237133099/100000000000000),(75973536532741/50000000000000),(-34933823321/10000000000000),(100716223/25000000000000)⟩
def e388 : ℝ := (766259/1000000000000)
theorem h388 : Model (fun x => f388 ((99/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(26230334189514051/100000000000000),(75973536532741/50000000000000),(-34933823321/10000000000000),(100716223/25000000000000)⟩
def e389 : ℝ := (76625901/100000000000000)
theorem h389 : Model (fun x => f389 ((99/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(7926028570530271/25000000000000),(15714818067787/6250000000000),(-339098496737/100000000000000),(-397711487/50000000000000)⟩
def e390 : ℝ := (1329981/1000000000000)
theorem h390 : Model (fun x => f390 ((99/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(7921623808625509/25000000000000),(15714818067787/6250000000000),(-339098496737/100000000000000),(-397711487/50000000000000)⟩
def e391 : ℝ := (132998101/100000000000000)
theorem h391 : Model (fun x => f391 ((99/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(38298874076722123/100000000000000),(192894006637203/50000000000000),(-134010837929/100000000000000),(-154863523/5000000000000)⟩
def e392 : ℝ := (52263607/25000000000000)
theorem h392 : Model (fun x => f392 ((99/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(1196943981564233/3125000000000),(192894006637203/50000000000000),(-134010837929/100000000000000),(-154863523/5000000000000)⟩
def e393 : ℝ := (209054429/100000000000000)
theorem h393 : Model (fun x => f393 ((99/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(1998238555686043/25000000000000),(89741517254691/50000000000000),(516998255673/100000000000000),(-3481060749/100000000000000)⟩
def e394 : ℝ := (19575101/20000000000000)
theorem h394 : Model (fun x => f394 ((99/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(146091047156099/100000000000000),(156166969799/25000000000000),(-1092306727/50000000000000),(692629/10000000000000)⟩
def e395 : ℝ := (144037/50000000000000)
theorem h395 : Model (fun x => f395 ((99/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(220868129445317/100000000000000),(64602211731/25000000000000),(-235989817/20000000000000),(5387887/100000000000000)⟩
def e396 : ℝ := (50809/50000000000000)
theorem h396 : Model (fun x => f396 ((99/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(487827306046733/100000000000000),(285371393261/25000000000000),(-568063953/12500000000000),(1106379/6250000000000)⟩
def e397 : ℝ := (49131/10000000000000)
theorem h397 : Model (fun x => f397 ((99/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(10774550457889/1000000000000),(1890883374803/50000000000000),(-1605473993/12500000000000),(5021179/12500000000000)⟩
def e398 : ℝ := (872317/50000000000000)
theorem h398 : Model (fun x => f398 ((99/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2379754805248127/100000000000000),(11136956639787/100000000000000),(-782721103/2500000000000),(17240279/25000000000000)⟩
def e399 : ℝ := (5416893/100000000000000)
theorem h399 : Model (fun x => f399 ((99/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(3476608714734573/100000000000000),(31135660448393/100000000000000),(-28158871027/100000000000000),(-173301011/100000000000000)⟩
def e400 : ℝ := (4181249/25000000000000)
theorem h400 : Model (fun x => f400 ((99/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(120868129445317/12500000000000),(64602211731/3125000000000),(-235989817/2500000000000),(5387887/12500000000000)⟩
def e401 : ℝ := (50809/6250000000000)
theorem h401 : Model (fun x => f401 ((99/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(222607216543727/20000000000000),(672984663647/25000000000000),(-5812103067/50000000000000),(25014693/50000000000000)⟩
def e402 : ℝ := (550509/50000000000000)
theorem h402 : Model (fun x => f402 ((99/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(242607216543727/20000000000000),(672984663647/25000000000000),(-5812103067/50000000000000),(25014693/50000000000000)⟩
def e403 : ℝ := (550509/50000000000000)
theorem h403 : Model (fun x => f403 ((99/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(10543129541167737/25000000000000),(117818742423119/25000000000000),(46223724727/50000000000000),(-74065167/1562500000000)⟩
def e404 : ℝ := (256144839/100000000000000)
theorem h404 : Model (fun x => f404 ((99/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(47424248943/20000000000000),(-165613343/6250000000000),(14545841/50000000000000),(-292637/100000000000000)⟩
def e405 : ℝ := (2211/50000000000000)
theorem h405 : Model (fun x => f405 ((99/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (41701145751213491/100000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(18952992542471/100000000000000),(53448506599/25000000000000),(-602384067/50000000000000),(1717617/25000000000000)⟩
def e406 : ℝ := (881241/100000000000000)
theorem h406 : Model (fun x => f406 ((99/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(42358439999431/100000000000000),(54034869831/10000000000000),(-2162697227/100000000000000),(4985259/50000000000000)⟩
def e407 : ℝ := (802439/50000000000000)
theorem h407 : Model (fun x => f407 ((99/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(137891483090629/50000000000000),(2035767049103/50000000000000),(-3055494699/100000000000000),(51823991/50000000000000)⟩
def e408 : ℝ := (11812111/100000000000000)
theorem h408 : Model (fun x => f408 ((99/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(22285492216667/20000000000000),(51953437217/10000000000000),(-810295657/12500000000000),(107356407/100000000000000)⟩
def e409 : ℝ := (8260391/100000000000000)
theorem h409 : Model (fun x => f409 ((99/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-317243876431/25000000000000),(42591522463/50000000000000),(-50554203/100000000000000),(-6606231/100000000000000)⟩
def e410 : ℝ := (56937151/100000000000000)
theorem h410 : Model (fun x => f410 ((99/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(13039340370117187/100000000000000),(155162559814453/25000000000000),(1205523/10240000),(2277/2048000)⟩
def e411 : ℝ := (523437501/100000000000000)
theorem h411 : Model (fun x => f411 ((99/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(47961/1600),(219/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((99/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(10503459/64000),(143883/64000),(657/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((99/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(2139971515071417169/100000000000000),(65586826186392109/50000000000000),(865319472499191/25000000000000),(51288869780639/100000000000000)⟩
def e414 : ℝ := (46892102121/10000000000000)
theorem h414 : Model (fun x => f414 ((99/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(1168239849/25000000000000),(-71609499/25000000000000),(1249941/12500000000000),(-261641/100000000000000)⟩
def e415 : ℝ := (8549/100000000000000)
theorem h415 : Model (fun x => f415 ((99/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (1002642413508917169/50000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(1404747850749/25000000000000),(-12883502509/100000000000000),(-11438323/4000000000000),(6611441/100000000000000)⟩
def e416 : ℝ := (9835573/50000000000000)
theorem h416 : Model (fun x => f416 ((99/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(543751987159/12500000000000),(72299542417/100000000000000),(-168256139/50000000000000),(521/10000000000000)⟩
def e417 : ℝ := (76608297/100000000000000)
theorem h417 : Model (fun x => f417 ((99/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((99/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((13049481354647/6000000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (49/20) (5/2) ∧
    SigmaActualBlockSeparable.endpointCellMass (49/20) (5/2) ≤ (13049941004429/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(99/40)-(1/40)) (by norm_num : ((99/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel29


noncomputable section
namespace Hf4Quad.Panel30
open Hf4Quad.Dag

def p0 : Cubic := ⟨(101/40),(1/40),0,0⟩
def e0 : ℝ := 0
theorem h0 : Model (fun x => f0 ((101/40)+(1/40)*x)) p0 e0 := by
  exact Model.variable _ _

def p1 : Cubic := ⟨(1549193338483/400000000000),0,0,0⟩
def e1 : ℝ := (1/2000000000000)
theorem h1 : Model (fun x => f1 ((101/40)+(1/40)*x)) p1 e1 := by
  convert Model.radical using 1 <;> norm_num [f1,p1,e1]

def p2 : Cubic := ⟨(32/35),0,0,0⟩
def e2 : ℝ := 0
theorem h2 : Model (fun x => f2 ((101/40)+(1/40)*x)) p2 e2 := by
  exact Model.constant _

def p3 : Cubic := ⟨(184/105),0,0,0⟩
def e3 : ℝ := 0
theorem h3 : Model (fun x => f3 ((101/40)+(1/40)*x)) p3 e3 := by
  exact Model.constant _

def p4 : Cubic := ⟨(44247619047619/10000000000000),(547619047619/12500000000000),0,0⟩
def e4 : ℝ := (1/100000000000000)
theorem h4 : Model (fun x => f4 ((101/40)+(1/40)*x)) p4 e4 := by
  apply Model.mul h3 h0
  norm_num [mulError,Cubic.norm,p3,p0,p4,e3,e0,e4]

def p5 : Cubic := ⟨(-44247619047619/10000000000000),(-547619047619/12500000000000),0,0⟩
def e5 : ℝ := (1/100000000000000)
theorem h5 : Model (fun x => f5 ((101/40)+(1/40)*x)) p5 e5 := by
  convert h4.neg using 1 <;> norm_num [f5,p4,p5,e4,e5]

def p6 : Cubic := ⟨(-351047619047619/100000000000000),(-547619047619/12500000000000),0,0⟩
def e6 : ℝ := (1/50000000000000)
theorem h6 : Model (fun x => f6 ((101/40)+(1/40)*x)) p6 e6 := by
  apply Model.add h2 h5
  norm_num [mulError,Cubic.norm,p2,p5,p6,e2,e5,e6]

def p7 : Cubic := ⟨(1144/945),0,0,0⟩
def e7 : ℝ := 0
theorem h7 : Model (fun x => f7 ((101/40)+(1/40)*x)) p7 e7 := by
  exact Model.constant _

def p8 : Cubic := ⟨(10201/1600),(101/800),(1/1600),0⟩
def e8 : ℝ := 0
theorem h8 : Model (fun x => f8 ((101/40)+(1/40)*x)) p8 e8 := by
  apply Model.mul h0 h0
  norm_num [mulError,Cubic.norm,p0,p0,p8,e0,e0,e8]

def p9 : Cubic := ⟨(771821693121693/100000000000000),(15283597883597/100000000000000),(75661375661/100000000000000),0⟩
def e9 : ℝ := (1/50000000000000)
theorem h9 : Model (fun x => f9 ((101/40)+(1/40)*x)) p9 e9 := by
  apply Model.mul h7 h8
  norm_num [mulError,Cubic.norm,p7,p8,p9,e7,e8,e9]

def p10 : Cubic := ⟨(-771821693121693/100000000000000),(-15283597883597/100000000000000),(-75661375661/100000000000000),0⟩
def e10 : ℝ := (1/50000000000000)
theorem h10 : Model (fun x => f10 ((101/40)+(1/40)*x)) p10 e10 := by
  convert h9.neg using 1 <;> norm_num [f10,p9,p10,e9,e10]

def p11 : Cubic := ⟨(-35089666005291/3125000000000),(-19664550264549/100000000000000),(-75661375661/100000000000000),0⟩
def e11 : ℝ := (1/25000000000000)
theorem h11 : Model (fun x => f11 ((101/40)+(1/40)*x)) p11 e11 := by
  apply Model.add h6 h10
  norm_num [mulError,Cubic.norm,p6,p10,p11,e6,e10,e11]

def p12 : Cubic := ⟨(5261/540),0,0,0⟩
def e12 : ℝ := 0
theorem h12 : Model (fun x => f12 ((101/40)+(1/40)*x)) p12 e12 := by
  exact Model.constant _

def p13 : Cubic := ⟨(1030301/64000),(30603/64000),(303/64000),(1/64000)⟩
def e13 : ℝ := 0
theorem h13 : Model (fun x => f13 ((101/40)+(1/40)*x)) p13 e13 := by
  apply Model.mul h8 h0
  norm_num [mulError,Cubic.norm,p8,p0,p13,e8,e0,e13]

def p14 : Cubic := ⟨(15684067016782407/100000000000000),(465863376736111/100000000000000),(922501736111/20000000000000),(608912037/4000000000000)⟩
def e14 : ℝ := (1/50000000000000)
theorem h14 : Model (fun x => f14 ((101/40)+(1/40)*x)) p14 e14 := by
  apply Model.mul h12 h13
  norm_num [mulError,Cubic.norm,p12,p13,p14,e12,e13,e14]

def p15 : Cubic := ⟨(-15684067016782407/100000000000000),(-465863376736111/100000000000000),(-922501736111/20000000000000),(-608912037/4000000000000)⟩
def e15 : ℝ := (1/50000000000000)
theorem h15 : Model (fun x => f15 ((101/40)+(1/40)*x)) p15 e15 := by
  convert h14.neg using 1 <;> norm_num [f15,p14,p15,e14,e15]

def p16 : Cubic := ⟨(-16806936328951719/100000000000000),(-24276396350033/5000000000000),(-586021257027/12500000000000),(-608912037/4000000000000)⟩
def e16 : ℝ := (3/50000000000000)
theorem h16 : Model (fun x => f16 ((101/40)+(1/40)*x)) p16 e16 := by
  apply Model.add h11 h15
  norm_num [mulError,Cubic.norm,p11,p15,p16,e11,e15,e16]

def p17 : Cubic := ⟨(176/63),0,0,0⟩
def e17 : ℝ := 0
theorem h17 : Model (fun x => f17 ((101/40)+(1/40)*x)) p17 e17 := by
  exact Model.constant _

def p18 : Cubic := ⟨(104060401/2560000),(1030301/640000),(30603/1280000),(101/640000)⟩
def e18 : ℝ := (1/2560000)
theorem h18 : Model (fun x => f18 ((101/40)+(1/40)*x)) p18 e18 := by
  apply Model.mul h13 h0
  norm_num [mulError,Cubic.norm,p13,p0,p18,e13,e0,e18]

def p19 : Cubic := ⟨(11355797728174603/100000000000000),(449734563492063/100000000000000),(1669806547619/25000000000000),(44087301587/100000000000000)⟩
def e19 : ℝ := (54563493/50000000000000)
theorem h19 : Model (fun x => f19 ((101/40)+(1/40)*x)) p19 e19 := by
  apply Model.mul h17 h18
  norm_num [mulError,Cubic.norm,p17,p18,p19,e17,e18,e19]

def p20 : Cubic := ⟨(-1362784650194279/25000000000000),(-35793363508597/100000000000000),(99552806713/5000000000000),(14432250331/50000000000000)⟩
def e20 : ℝ := (6820437/6250000000000)
theorem h20 : Model (fun x => f20 ((101/40)+(1/40)*x)) p20 e20 := by
  apply Model.add h16 h19
  norm_num [mulError,Cubic.norm,p16,p19,p20,e16,e19,e20]

def p21 : Cubic := ⟨(1759/270),0,0,0⟩
def e21 : ℝ := 0
theorem h21 : Model (fun x => f21 ((101/40)+(1/40)*x)) p21 e21 := by
  exact Model.constant _

def p22 : Cubic := ⟨(2565942505126953/25000000000000),(127026856689453/25000000000000),(1030301/10240000),(10201/10240000)⟩
def e22 : ℝ := (247070313/50000000000000)
theorem h22 : Model (fun x => f22 ((101/40)+(1/40)*x)) p22 e22 := by
  apply Model.mul h18 h0
  norm_num [mulError,Cubic.norm,p18,p0,p22,e18,e0,e22]

def p23 : Cubic := ⟨(66866560985456449/100000000000000),(3310225791359227/100000000000000),(65549025571469/100000000000000),(324500126591/50000000000000)⟩
def e23 : ℝ := (3219234673/100000000000000)
theorem h23 : Model (fun x => f23 ((101/40)+(1/40)*x)) p23 e23 := by
  apply Model.mul h21 h22
  norm_num [mulError,Cubic.norm,p21,p22,p23,e21,e22,e23]

def p24 : Cubic := ⟨(61415422384679333/100000000000000),(327443242785063/10000000000000),(67540081705729/100000000000000),(169466188461/25000000000000)⟩
def e24 : ℝ := (665672333/20000000000000)
theorem h24 : Model (fun x => f24 ((101/40)+(1/40)*x)) p24 e24 := by
  apply Model.add h20 h23
  norm_num [mulError,Cubic.norm,p20,p23,p24,e20,e23,e24]

def p25 : Cubic := ⟨(2122/945),0,0,0⟩
def e25 : ℝ := 0
theorem h25 : Model (fun x => f25 ((101/40)+(1/40)*x)) p25 e25 := by
  exact Model.constant _

def p26 : Cubic := ⟨(1036640772071289/4000000000000),(153956550307617/10000000000000),(7621611401367/20000000000000),(125769165039/25000000000000)⟩
def e26 : ℝ := (1875268557/50000000000000)
theorem h26 : Model (fun x => f26 ((101/40)+(1/40)*x)) p26 e26 := by
  apply Model.mul h22 h0
  norm_num [mulError,Cubic.norm,p22,p0,p26,e22,e0,e26]

def p27 : Cubic := ⟨(5819448990304961/10000000000000),(3457098410082151/100000000000000),(85571742823813/100000000000000),(112965997127/10000000000000)⟩
def e27 : ℝ := (4210920507/50000000000000)
theorem h27 : Model (fun x => f27 ((101/40)+(1/40)*x)) p27 e27 := by
  apply Model.mul h25 h26
  norm_num [mulError,Cubic.norm,p25,p26,p27,e25,e26,e27]

def p28 : Cubic := ⟨(119609912287728943/100000000000000),(6731530837932781/100000000000000),(76555912264771/50000000000000),(903762362557/50000000000000)⟩
def e28 : ℝ := (11750202679/100000000000000)
theorem h28 : Model (fun x => f28 ((101/40)+(1/40)*x)) p28 e28 := by
  apply Model.add h24 h27
  norm_num [mulError,Cubic.norm,p24,p27,p28,e24,e27,e28]

def p29 : Cubic := ⟨(299/1260),0,0,0⟩
def e29 : ℝ := 0
theorem h29 : Model (fun x => f29 ((101/40)+(1/40)*x)) p29 e29 := by
  exact Model.constant _

def p30 : Cubic := ⟨(32718974368500059/50000000000000),(1133825844452971/25000000000000),(67355990759581/50000000000000),(17366953063/781250000000)⟩
def e30 : ℝ := (22140786147/100000000000000)
theorem h30 : Model (fun x => f30 ((101/40)+(1/40)*x)) p30 e30 := by
  apply Model.mul h26 h0
  norm_num [mulError,Cubic.norm,p26,p0,p30,e26,e0,e30]

def p31 : Cubic := ⟨(3882132276262507/25000000000000),(107623469044901/10000000000000),(31967367043039/100000000000000),(13187857691/2500000000000)⟩
def e31 : ℝ := (5254043699/100000000000000)
theorem h31 : Model (fun x => f31 ((101/40)+(1/40)*x)) p31 e31 := by
  apply Model.mul h29 h30
  norm_num [mulError,Cubic.norm,p29,p30,p31,e29,e30,e31]

def p32 : Cubic := ⟨(135138441392778971/100000000000000),(7807765528381791/100000000000000),(185079191572581/100000000000000),(1167519516377/50000000000000)⟩
def e32 : ℝ := (8502123189/50000000000000)
theorem h32 : Model (fun x => f32 ((101/40)+(1/40)*x)) p32 e32 := by
  apply Model.add h28 h31
  norm_num [mulError,Cubic.norm,p28,p31,p32,e28,e31,e32]

def p33 : Cubic := ⟨2145,0,0,0⟩
def e33 : ℝ := 0
theorem h33 : Model (fun x => f33 ((101/40)+(1/40)*x)) p33 e33 := by
  exact Model.constant _

def p34 : Cubic := ⟨(4376229/320),(43329/160),(429/320),0⟩
def e34 : ℝ := 0
theorem h34 : Model (fun x => f34 ((101/40)+(1/40)*x)) p34 e34 := by
  apply Model.mul h33 h8
  norm_num [mulError,Cubic.norm,p33,p8,p34,e33,e8,e34]

def p35 : Cubic := ⟨4418,0,0,0⟩
def e35 : ℝ := 0
theorem h35 : Model (fun x => f35 ((101/40)+(1/40)*x)) p35 e35 := by
  exact Model.constant _

def p36 : Cubic := ⟨(223109/20),(2209/20),0,0⟩
def e36 : ℝ := 0
theorem h36 : Model (fun x => f36 ((101/40)+(1/40)*x)) p36 e36 := by
  apply Model.mul h35 h0
  norm_num [mulError,Cubic.norm,p35,p0,p36,e35,e0,e36]

def p37 : Cubic := ⟨(7945973/320),(61001/160),(429/320),0⟩
def e37 : ℝ := 0
theorem h37 : Model (fun x => f37 ((101/40)+(1/40)*x)) p37 e37 := by
  apply Model.add h34 h36
  norm_num [mulError,Cubic.norm,p34,p36,p37,e34,e36,e37]

def p38 : Cubic := ⟨2280,0,0,0⟩
def e38 : ℝ := 0
theorem h38 : Model (fun x => f38 ((101/40)+(1/40)*x)) p38 e38 := by
  exact Model.constant _

def p39 : Cubic := ⟨(8675573/320),(61001/160),(429/320),0⟩
def e39 : ℝ := 0
theorem h39 : Model (fun x => f39 ((101/40)+(1/40)*x)) p39 e39 := by
  apply Model.add h37 h38
  norm_num [mulError,Cubic.norm,p37,p38,p39,e37,e38,e39]

def p40 : Cubic := ⟨(-8675573/320),(-61001/160),(-429/320),0⟩
def e40 : ℝ := 0
theorem h40 : Model (fun x => f40 ((101/40)+(1/40)*x)) p40 e40 := by
  convert h39.neg using 1 <;> norm_num [f40,p39,p40,e39,e40]

def p41 : Cubic := ⟨1,0,0,0⟩
def e41 : ℝ := 0
theorem h41 : Model (fun x => f41 ((101/40)+(1/40)*x)) p41 e41 := by
  exact Model.constant _

def p42 : Cubic := ⟨(141/40),(1/40),0,0⟩
def e42 : ℝ := 0
theorem h42 : Model (fun x => f42 ((101/40)+(1/40)*x)) p42 e42 := by
  apply Model.add h0 h41
  norm_num [mulError,Cubic.norm,p0,p41,p42,e0,e41,e42]

def p43 : Cubic := ⟨(19881/1600),(141/800),(1/1600),0⟩
def e43 : ℝ := 0
theorem h43 : Model (fun x => f43 ((101/40)+(1/40)*x)) p43 e43 := by
  apply Model.mul h42 h42
  norm_num [mulError,Cubic.norm,p42,p42,p43,e42,e42,e43]

def p44 : Cubic := ⟨210,0,0,0⟩
def e44 : ℝ := 0
theorem h44 : Model (fun x => f44 ((101/40)+(1/40)*x)) p44 e44 := by
  exact Model.constant _

def p45 : Cubic := ⟨(417501/160),(2961/80),(21/160),0⟩
def e45 : ℝ := 0
theorem h45 : Model (fun x => f45 ((101/40)+(1/40)*x)) p45 e45 := by
  apply Model.mul h44 h43
  norm_num [mulError,Cubic.norm,p44,p43,p45,e44,e43,e45]

def p46 : Cubic := ⟨(38323261501/100000000000000),(-271796181/50000000000000),(5782897/100000000000000),(-10937/20000000000000)⟩
def e46 : ℝ := (31/6250000000000)
theorem h46 : Model (fun x => f46 ((101/40)+(1/40)*x)) p46 e46 := by
  apply Model.inv h45 (L := (205779/80))
  · norm_num
  · norm_num [p45,e45]
  · norm_num [mulError,Cubic.norm,p45,p46,e45,e46]

def p47 : Cubic := ⟨(-519494144921899/50000000000000),(63219795513/50000000000000),(-182043069/20000000000000),(3280989/50000000000000)⟩
def e47 : ℝ := (26806523/100000000000000)
theorem h47 : Model (fun x => f47 ((101/40)+(1/40)*x)) p47 e47 := by
  apply Model.mul h40 h46
  norm_num [mulError,Cubic.norm,p40,p46,p47,e40,e46,e47]

def p48 : Cubic := ⟨2,0,0,0⟩
def e48 : ℝ := 0
theorem h48 : Model (fun x => f48 ((101/40)+(1/40)*x)) p48 e48 := by
  exact Model.constant _

def p49 : Cubic := ⟨(181/40),(1/40),0,0⟩
def e49 : ℝ := 0
theorem h49 : Model (fun x => f49 ((101/40)+(1/40)*x)) p49 e49 := by
  apply Model.add h0 h48
  norm_num [mulError,Cubic.norm,p0,p48,p49,e0,e48,e49]

def p50 : Cubic := ⟨3,0,0,0⟩
def e50 : ℝ := 0
theorem h50 : Model (fun x => f50 ((101/40)+(1/40)*x)) p50 e50 := by
  exact Model.constant _

def p51 : Cubic := ⟨(33333333333333/100000000000000),0,0,0⟩
def e51 : ℝ := (1/100000000000000)
theorem h51 : Model (fun x => f51 ((101/40)+(1/40)*x)) p51 e51 := by
  apply Model.inv h50 (L := 3)
  · norm_num
  · norm_num [p50,e50]
  · norm_num [mulError,Cubic.norm,p50,p51,e50,e51]

def p52 : Cubic := ⟨(150833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e52 : ℝ := (3/50000000000000)
theorem h52 : Model (fun x => f52 ((101/40)+(1/40)*x)) p52 e52 := by
  apply Model.mul h49 h51
  norm_num [mulError,Cubic.norm,p49,p51,p52,e49,e51,e52]

def p53 : Cubic := ⟨(250833333333331/100000000000000),(833333333333/100000000000000),0,0⟩
def e53 : ℝ := (3/50000000000000)
theorem h53 : Model (fun x => f53 ((101/40)+(1/40)*x)) p53 e53 := by
  apply Model.add h52 h41
  norm_num [mulError,Cubic.norm,p52,p41,p53,e52,e41,e53]

def p54 : Cubic := ⟨(1/2),0,0,0⟩
def e54 : ℝ := 0
theorem h54 : Model (fun x => f54 ((101/40)+(1/40)*x)) p54 e54 := by
  apply Model.inv h48 (L := 2)
  · norm_num
  · norm_num [p48,e48]
  · norm_num [mulError,Cubic.norm,p48,p54,e48,e54]

def p55 : Cubic := ⟨(25083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e55 : ℝ := (1/25000000000000)
theorem h55 : Model (fun x => f55 ((101/40)+(1/40)*x)) p55 e55 := by
  apply Model.mul h53 h54
  norm_num [mulError,Cubic.norm,p53,p54,p55,e53,e54,e55]

def p56 : Cubic := ⟨21,0,0,0⟩
def e56 : ℝ := 0
theorem h56 : Model (fun x => f56 ((101/40)+(1/40)*x)) p56 e56 := by
  exact Model.constant _

def p57 : Cubic := ⟨(526749999999993/20000000000000),(4374999999993/50000000000000),0,0⟩
def e57 : ℝ := (21/25000000000000)
theorem h57 : Model (fun x => f57 ((101/40)+(1/40)*x)) p57 e57 := by
  apply Model.mul h56 h55
  norm_num [mulError,Cubic.norm,p56,p55,p57,e56,e55,e57]

def p58 : Cubic := ⟨-1,0,0,0⟩
def e58 : ℝ := 0
theorem h58 : Model (fun x => f58 ((101/40)+(1/40)*x)) p58 e58 := by
  convert h41.neg using 1 <;> norm_num [f58,p41,p58,e41,e58]

def p59 : Cubic := ⟨(5083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e59 : ℝ := (1/25000000000000)
theorem h59 : Model (fun x => f59 ((101/40)+(1/40)*x)) p59 e59 := by
  apply Model.add h55 h58
  norm_num [mulError,Cubic.norm,p55,p58,p59,e55,e58,e59]

def p60 : Cubic := ⟨(4183821614583/625000000000),(2639583333329/20000000000000),(36458333333/100000000000000),0⟩
def e60 : ℝ := (129/100000000000000)
theorem h60 : Model (fun x => f60 ((101/40)+(1/40)*x)) p60 e60 := by
  apply Model.mul h57 h59
  norm_num [mulError,Cubic.norm,p57,p59,p60,e57,e59,e60]

def p61 : Cubic := ⟨(157293402777773/100000000000000),(1045138888887/100000000000000),(1736111111/100000000000000),0⟩
def e61 : ℝ := (11/100000000000000)
theorem h61 : Model (fun x => f61 ((101/40)+(1/40)*x)) p61 e61 := by
  apply Model.mul h55 h55
  norm_num [mulError,Cubic.norm,p55,p55,p61,e55,e55,e61]

def p62 : Cubic := ⟨10,0,0,0⟩
def e62 : ℝ := 0
theorem h62 : Model (fun x => f62 ((101/40)+(1/40)*x)) p62 e62 := by
  exact Model.constant _

def p63 : Cubic := ⟨(25083333333333/2000000000000),(208333333333/5000000000000),0,0⟩
def e63 : ℝ := (1/2500000000000)
theorem h63 : Model (fun x => f63 ((101/40)+(1/40)*x)) p63 e63 := by
  apply Model.mul h62 h55
  norm_num [mulError,Cubic.norm,p62,p55,p63,e62,e55,e63]

def p64 : Cubic := ⟨(1411460069444423/100000000000000),(5211805555547/100000000000000),(1736111111/100000000000000),0⟩
def e64 : ℝ := (51/100000000000000)
theorem h64 : Model (fun x => f64 ((101/40)+(1/40)*x)) p64 e64 := by
  apply Model.add h61 h63
  norm_num [mulError,Cubic.norm,p61,p63,p64,e61,e63,e64]

def p65 : Cubic := ⟨(1511460069444423/100000000000000),(5211805555547/100000000000000),(1736111111/100000000000000),0⟩
def e65 : ℝ := (51/100000000000000)
theorem h65 : Model (fun x => f65 ((101/40)+(1/40)*x)) p65 e65 := by
  apply Model.add h64 h41
  norm_num [mulError,Cubic.norm,p64,p41,p65,e64,e41,e65]

def p66 : Cubic := ⟨(5058943446496559/50000000000000),(234369663989771/100000000000000),(312631157767/25000000000000),(2129267939/100000000000000)⟩
def e66 : ℝ := (127053/20000000000000)
theorem h66 : Model (fun x => f66 ((101/40)+(1/40)*x)) p66 e66 := by
  apply Model.mul h60 h65
  norm_num [mulError,Cubic.norm,p60,p65,p66,e60,e65,e66]

def p67 : Cubic := ⟨(45083333333333/20000000000000),(208333333333/50000000000000),0,0⟩
def e67 : ℝ := (1/25000000000000)
theorem h67 : Model (fun x => f67 ((101/40)+(1/40)*x)) p67 e67 := by
  apply Model.add h55 h41
  norm_num [mulError,Cubic.norm,p55,p41,p67,e55,e41,e67]

def p68 : Cubic := ⟨(508126736111103/100000000000000),(1878472222219/100000000000000),(1736111111/100000000000000),0⟩
def e68 : ℝ := (19/100000000000000)
theorem h68 : Model (fun x => f68 ((101/40)+(1/40)*x)) p68 e68 := by
  apply Model.mul h67 h67
  norm_num [mulError,Cubic.norm,p67,p67,p68,e67,e67,e68]

def p69 : Cubic := ⟨(1145402350983769/100000000000000),(3175792100689/50000000000000),(2935112847/25000000000000),(1808449/25000000000000)⟩
def e69 : ℝ := (13/20000000000000)
theorem h69 : Model (fun x => f69 ((101/40)+(1/40)*x)) p69 e69 := by
  apply Model.mul h68 h67
  norm_num [mulError,Cubic.norm,p68,p67,p69,e68,e67,e69]

def p70 : Cubic := ⟨(115890514342221793/100000000000000),(3327121746740243/100000000000000),(6079522133369/20000000000000),(132064773699/100000000000000)⟩
def e70 : ℝ := (153338701/50000000000000)
theorem h70 : Model (fun x => f70 ((101/40)+(1/40)*x)) p70 e70 := by
  apply Model.mul h66 h69
  norm_num [mulError,Cubic.norm,p66,p69,p70,e66,e69,e70]

def p71 : Cubic := ⟨168,0,0,0⟩
def e71 : ℝ := 0
theorem h71 : Model (fun x => f71 ((101/40)+(1/40)*x)) p71 e71 := by
  exact Model.constant _

def p72 : Cubic := ⟨(3303161458333233/12500000000000),(21947916666627/12500000000000),(36458333331/12500000000000),0⟩
def e72 : ℝ := (231/12500000000000)
theorem h72 : Model (fun x => f72 ((101/40)+(1/40)*x)) p72 e72 := by
  apply Model.mul h71 h61
  norm_num [mulError,Cubic.norm,p71,p61,p72,e71,e61,e72]

def p73 : Cubic := ⟨(3358214149305233/50000000000000),(19341601562467/12500000000000),(805729166659/100000000000000),(1215277777/100000000000000)⟩
def e73 : ℝ := (309/20000000000000)
theorem h73 : Model (fun x => f73 ((101/40)+(1/40)*x)) p73 e73 := by
  apply Model.mul h72 h59
  norm_num [mulError,Cubic.norm,p72,p59,p73,e72,e59,e73]

def p74 : Cubic := ⟨(38465063817211717/50000000000000),(1099456435413353/50000000000000),(19845364689963/100000000000000),(41874285019/50000000000000)⟩
def e74 : ℝ := (36640401/20000000000000)
theorem h74 : Model (fun x => f74 ((101/40)+(1/40)*x)) p74 e74 := by
  apply Model.mul h73 h69
  norm_num [mulError,Cubic.norm,p73,p69,p74,e73,e69,e74]

def p75 : Cubic := ⟨(192820641976645227/100000000000000),(5526034617566949/100000000000000),(6280371919601/12500000000000),(215813343737/100000000000000)⟩
def e75 : ℝ := (489879407/100000000000000)
theorem h75 : Model (fun x => f75 ((101/40)+(1/40)*x)) p75 e75 := by
  apply Model.add h70 h74
  norm_num [mulError,Cubic.norm,p70,p74,p75,e70,e74,e75]

def p76 : Cubic := ⟨56,0,0,0⟩
def e76 : ℝ := 0
theorem h76 : Model (fun x => f76 ((101/40)+(1/40)*x)) p76 e76 := by
  exact Model.constant _

def p77 : Cubic := ⟨(1101053819444411/12500000000000),(7315972222209/12500000000000),(12152777777/12500000000000),0⟩
def e77 : ℝ := (77/12500000000000)
theorem h77 : Model (fun x => f77 ((101/40)+(1/40)*x)) p77 e77 := by
  apply Model.mul h76 h61
  norm_num [mulError,Cubic.norm,p76,p61,p77,e76,e61,e77]

def p78 : Cubic := ⟨(6460069444443/100000000000000),(42361111111/20000000000000),(1736111111/100000000000000),0⟩
def e78 : ℝ := (3/100000000000000)
theorem h78 : Model (fun x => f78 ((101/40)+(1/40)*x)) p78 e78 := by
  apply Model.mul h59 h59
  norm_num [mulError,Cubic.norm,p59,p59,p78,e59,e59,e78]

def p79 : Cubic := ⟨(1641934317129/100000000000000),(16150173611/20000000000000),(661892361/50000000000000),(1808449/25000000000000)⟩
def e79 : ℝ := (3/100000000000000)
theorem h79 : Model (fun x => f79 ((101/40)+(1/40)*x)) p79 e79 := by
  apply Model.mul h78 h59
  norm_num [mulError,Cubic.norm,p78,p59,p79,e78,e59,e79]

def p80 : Cubic := ⟨(72314322046069/50000000000000),(8073871804017/100000000000000),(165462671581/100000000000000),(298094693/20000000000000)⟩
def e80 : ℝ := (2764053/50000000000000)
theorem h80 : Model (fun x => f80 ((101/40)+(1/40)*x)) p80 e80 := by
  apply Model.mul h77 h79
  norm_num [mulError,Cubic.norm,p77,p79,p80,e77,e79,e80]

def p81 : Cubic := ⟨(326017068557691/100000000000000),(18802472041937/100000000000000),(101655392843/25000000000000),(20246017/500000000000)⟩
def e81 : ℝ := (18694621/100000000000000)
theorem h81 : Model (fun x => f81 ((101/40)+(1/40)*x)) p81 e81 := by
  apply Model.mul h80 h67
  norm_num [mulError,Cubic.norm,p80,p67,p81,e80,e67,e81]

def p82 : Cubic := ⟨(96573329522601459/50000000000000),(2772418544804443/50000000000000),(2532479846409/5000000000000),(219862547137/100000000000000)⟩
def e82 : ℝ := (127143507/25000000000000)
theorem h82 : Model (fun x => f82 ((101/40)+(1/40)*x)) p82 e82 := by
  apply Model.add h75 h81
  norm_num [mulError,Cubic.norm,p75,p81,p82,e75,e81,e82]

def p83 : Cubic := ⟨(41732497227/10000000000000),(1710348247/6250000000000),(6729239/1000000000000),(7354359/100000000000000)⟩
def e83 : ℝ := (30143/100000000000000)
theorem h83 : Model (fun x => f83 ((101/40)+(1/40)*x)) p83 e83 := by
  apply Model.mul h79 h59
  norm_num [mulError,Cubic.norm,p79,p59,p83,e79,e59,e83]

def p84 : Cubic := ⟨(53035048559/50000000000000),(1738854051/20000000000000),(285058041/100000000000000),(2336541/50000000000000)⟩
def e84 : ℝ := (1201/3125000000000)
theorem h84 : Model (fun x => f84 ((101/40)+(1/40)*x)) p84 e84 := by
  apply Model.mul h83 h59
  norm_num [mulError,Cubic.norm,p83,p59,p84,e83,e59,e84]

def p85 : Cubic := ⟨(26959483017/100000000000000),(2651752427/100000000000000),(54339189/50000000000000),(2375483/100000000000000)⟩
def e85 : ℝ := (14701/50000000000000)
theorem h85 : Model (fun x => f85 ((101/40)+(1/40)*x)) p85 e85 := by
  apply Model.mul h84 h59
  norm_num [mulError,Cubic.norm,p84,p59,p85,e84,e59,e85]

def p86 : Cubic := ⟨(6852201933/100000000000000),(393159127/50000000000000),(38671389/100000000000000),(211319/20000000000000)⟩
def e86 : ℝ := (3499/20000000000000)
theorem h86 : Model (fun x => f86 ((101/40)+(1/40)*x)) p86 e86 := by
  apply Model.mul h85 h59
  norm_num [mulError,Cubic.norm,p85,p59,p86,e85,e59,e86]

def p87 : Cubic := ⟨(20556605799/100000000000000),(1179477381/50000000000000),(116014167/100000000000000),(633957/20000000000000)⟩
def e87 : ℝ := (10497/20000000000000)
theorem h87 : Model (fun x => f87 ((101/40)+(1/40)*x)) p87 e87 := by
  apply Model.mul h50 h86
  norm_num [mulError,Cubic.norm,p50,p86,p87,e50,e86,e87]

def p88 : Cubic := ⟨(-20556605799/100000000000000),(-1179477381/50000000000000),(-116014167/100000000000000),(-633957/20000000000000)⟩
def e88 : ℝ := (10497/20000000000000)
theorem h88 : Model (fun x => f88 ((101/40)+(1/40)*x)) p88 e88 := by
  convert h87.neg using 1 <;> norm_num [f88,p87,p88,e87,e88]

def p89 : Cubic := ⟨(193146638488597119/100000000000000),(1386208682663531/25000000000000),(50649480914013/100000000000000),(27482422169/12500000000000)⟩
def e89 : ℝ := (508626513/100000000000000)
theorem h89 : Model (fun x => f89 ((101/40)+(1/40)*x)) p89 e89 := by
  apply Model.add h82 h88
  norm_num [mulError,Cubic.norm,p82,p88,p89,e82,e88,e89]

def p90 : Cubic := ⟨(3303161458333233/10000000000000),(21947916666627/10000000000000),(36458333331/10000000000000),0⟩
def e90 : ℝ := (231/10000000000000)
theorem h90 : Model (fun x => f90 ((101/40)+(1/40)*x)) p90 e90 := by
  apply Model.mul h44 h61
  norm_num [mulError,Cubic.norm,p44,p61,p90,e44,e61,e90]

def p91 : Cubic := ⟨(1290963899754613/50000000000000),(1909003918303/10000000000000),(26464934171/50000000000000),(65224729/100000000000000)⟩
def e91 : ℝ := (30337/100000000000000)
theorem h91 : Model (fun x => f91 ((101/40)+(1/40)*x)) p91 e91 := by
  apply Model.mul h69 h67
  norm_num [mulError,Cubic.norm,p69,p67,p91,e69,e67,e91]

def p92 : Cubic := ⟨(426426219776900509/50000000000000),(2394508357006641/20000000000000),(68795527460481/100000000000000),(103656958117/50000000000000)⟩
def e92 : ℝ := (6930271/2000000000000)
theorem h92 : Model (fun x => f92 ((101/40)+(1/40)*x)) p92 e92 := by
  apply Model.mul h90 h91
  norm_num [mulError,Cubic.norm,p90,p91,p92,e90,e91,e92]

def p93 : Cubic := ⟨(5862678897/50000000000000),(-10287707/6250000000000),(1364911/100000000000000),(-4367/50000000000000)⟩
def e93 : ℝ := (61/100000000000000)
theorem h93 : Model (fun x => f93 ((101/40)+(1/40)*x)) p93 e93 := by
  apply Model.inv h92 (L := (210202723645219387/25000000000000))
  · norm_num
  · norm_num [p92,e92]
  · norm_num [mulError,Cubic.norm,p92,p93,e92,e93]

def p94 : Cubic := ⟨(22647134429871/100000000000000),(166112973643/50000000000000),(-551869039/100000000000000),(1221207/100000000000000)⟩
def e94 : ℝ := (338021/100000000000000)
theorem h94 : Model (fun x => f94 ((101/40)+(1/40)*x)) p94 e94 := by
  apply Model.mul h89 h93
  norm_num [mulError,Cubic.norm,p89,p93,p94,e89,e93,e94]

def p95 : Cubic := ⟨(150833333333331/50000000000000),(833333333333/50000000000000),0,0⟩
def e95 : ℝ := (3/25000000000000)
theorem h95 : Model (fun x => f95 ((101/40)+(1/40)*x)) p95 e95 := by
  apply Model.mul h48 h52
  norm_num [mulError,Cubic.norm,p48,p52,p95,e48,e52,e95]

def p96 : Cubic := ⟨(39867109634551/100000000000000),(-66224434609/50000000000000),(88005893/20000000000000),(-365473/25000000000000)⟩
def e96 : ℝ := (4877/100000000000000)
theorem h96 : Model (fun x => f96 ((101/40)+(1/40)*x)) p96 e96 := by
  apply Model.inv h53 (L := (31249999999999/12500000000000))
  · norm_num
  · norm_num [p53,e53]
  · norm_num [mulError,Cubic.norm,p53,p96,e53,e96]

def p97 : Cubic := ⟨(120265780730893/100000000000000),(132448869217/50000000000000),(-176011787/20000000000000),(2923783/100000000000000)⟩
def e97 : ℝ := (19583/50000000000000)
theorem h97 : Model (fun x => f97 ((101/40)+(1/40)*x)) p97 e97 := by
  apply Model.mul h95 h96
  norm_num [mulError,Cubic.norm,p95,p96,p97,e95,e96,e97]

def p98 : Cubic := ⟨(2525581395348753/100000000000000),(2781426253557/50000000000000),(-3696247527/20000000000000),(61399443/100000000000000)⟩
def e98 : ℝ := (411243/50000000000000)
theorem h98 : Model (fun x => f98 ((101/40)+(1/40)*x)) p98 e98 := by
  apply Model.mul h56 h97
  norm_num [mulError,Cubic.norm,p56,p97,p98,e56,e97,e98]

def p99 : Cubic := ⟨(20265780730893/100000000000000),(132448869217/50000000000000),(-176011787/20000000000000),(2923783/100000000000000)⟩
def e99 : ℝ := (19583/50000000000000)
theorem h99 : Model (fun x => f99 ((101/40)+(1/40)*x)) p99 e99 := by
  apply Model.add h97 h58
  norm_num [mulError,Cubic.norm,p97,p58,p99,e97,e58,e99]

def p100 : Cubic := ⟨(255914393880803/50000000000000),(7817563490063/100000000000000),(-11236101343/100000000000000),(-5813583/50000000000000)⟩
def e100 : ℝ := (1649247/100000000000000)
theorem h100 : Model (fun x => f100 ((101/40)+(1/40)*x)) p100 e100 := by
  apply Model.mul h98 h99
  norm_num [mulError,Cubic.norm,p98,p99,p100,e98,e99,e100]

def p101 : Cubic := ⟨(9039911259257/6250000000000),(159290666633/25000000000000),(-70755569/5000000000000),(592527/25000000000000)⟩
def e101 : ℝ := (117703/100000000000000)
theorem h101 : Model (fun x => f101 ((101/40)+(1/40)*x)) p101 e101 := by
  apply Model.mul h97 h97
  norm_num [mulError,Cubic.norm,p97,p97,p101,e97,e97,e101]

def p102 : Cubic := ⟨(120265780730893/10000000000000),(132448869217/5000000000000),(-176011787/2000000000000),(2923783/10000000000000)⟩
def e102 : ℝ := (19583/5000000000000)
theorem h102 : Model (fun x => f102 ((101/40)+(1/40)*x)) p102 e102 := by
  apply Model.mul h62 h97
  norm_num [mulError,Cubic.norm,p62,p97,p102,e62,e97,e102]

def p103 : Cubic := ⟨(673648193728521/50000000000000),(410767506359/12500000000000),(-1021570073/10000000000000),(15803969/50000000000000)⟩
def e103 : ℝ := (509363/100000000000000)
theorem h103 : Model (fun x => f103 ((101/40)+(1/40)*x)) p103 e103 := by
  apply Model.add h101 h102
  norm_num [mulError,Cubic.norm,p101,p102,p103,e101,e102,e103]

def p104 : Cubic := ⟨(723648193728521/50000000000000),(410767506359/12500000000000),(-1021570073/10000000000000),(15803969/50000000000000)⟩
def e104 : ℝ := (509363/100000000000000)
theorem h104 : Model (fun x => f104 ((101/40)+(1/40)*x)) p104 e104 := by
  apply Model.add h103 h41
  norm_num [mulError,Cubic.norm,p103,p41,p104,e103,e41,e104]

def p105 : Cubic := ⟨(3703839777619447/50000000000000),(129962724765369/100000000000000),(41989498813/100000000000000),(-234870789/20000000000000)⟩
def e105 : ℝ := (29809903/100000000000000)
theorem h105 : Model (fun x => f105 ((101/40)+(1/40)*x)) p105 e105 := by
  apply Model.mul h100 h104
  norm_num [mulError,Cubic.norm,p100,p104,p105,e100,e104,e105]

def p106 : Cubic := ⟨(220265780730893/100000000000000),(132448869217/50000000000000),(-176011787/20000000000000),(2923783/100000000000000)⟩
def e106 : ℝ := (19583/50000000000000)
theorem h106 : Model (fun x => f106 ((101/40)+(1/40)*x)) p106 e106 := by
  apply Model.add h97 h41
  norm_num [mulError,Cubic.norm,p97,p41,p106,e97,e41,e106]

def p107 : Cubic := ⟨(242585070804949/50000000000000),(5834790717/500000000000),(-12700917/400000000000),(4108837/50000000000000)⟩
def e107 : ℝ := (39207/20000000000000)
theorem h107 : Model (fun x => f107 ((101/40)+(1/40)*x)) p107 e107 := by
  apply Model.mul h106 h106
  norm_num [mulError,Cubic.norm,p106,p106,p107,e106,e106,e107]

def p108 : Cubic := ⟨(53433190014511/5000000000000),(963903549511/25000000000000),(-8172480949/100000000000000),(1700627/12500000000000)⟩
def e108 : ℝ := (706799/100000000000000)
theorem h108 : Model (fun x => f108 ((101/40)+(1/40)*x)) p108 e108 := by
  apply Model.mul h107 h106
  norm_num [mulError,Cubic.norm,p107,p106,p108,e107,e106,e108]

def p109 : Cubic := ⟨(79163189848337631/100000000000000),(209309517264463/12500000000000),(4854196641541/100000000000000),(-10272152677/50000000000000)⟩
def e109 : ℝ := (50515783/12500000000000)
theorem h109 : Model (fun x => f109 ((101/40)+(1/40)*x)) p109 e109 := by
  apply Model.mul h105 h108
  norm_num [mulError,Cubic.norm,p105,p108,p109,e105,e108,e109]

def p110 : Cubic := ⟨(189838136444397/781250000000),(3345103999293/3125000000000),(-1485866949/625000000000),(12443067/3125000000000)⟩
def e110 : ℝ := (2471763/12500000000000)
theorem h110 : Model (fun x => f110 ((101/40)+(1/40)*x)) p110 e110 := by
  apply Model.mul h71 h101
  norm_num [mulError,Cubic.norm,p71,p101,p110,e71,e101,e110]

def p111 : Cubic := ⟨(1231109775213919/25000000000000),(21515353297783/25000000000000),(2152775123/10000000000000),(-390328337/50000000000000)⟩
def e111 : ℝ := (4976549/25000000000000)
theorem h111 : Model (fun x => f111 ((101/40)+(1/40)*x)) p111 e111 := by
  apply Model.mul h110 h99
  norm_num [mulError,Cubic.norm,p110,p99,p111,e110,e99,e111]

def p112 : Cubic := ⟨(26312849019090903/50000000000000),(1109574541938441/100000000000000),(3145806503083/100000000000000),(-13875950117/100000000000000)⟩
def e112 : ℝ := (269130401/100000000000000)
theorem h112 : Model (fun x => f112 ((101/40)+(1/40)*x)) p112 e112 := by
  apply Model.mul h111 h108
  norm_num [mulError,Cubic.norm,p111,p108,p112,e111,e108,e112]

def p113 : Cubic := ⟨(131788887886519437/100000000000000),(556810136010829/20000000000000),(500000196539/6250000000000),(-34420255471/100000000000000)⟩
def e113 : ℝ := (134651333/20000000000000)
theorem h113 : Model (fun x => f113 ((101/40)+(1/40)*x)) p113 e113 := by
  apply Model.add h109 h112
  norm_num [mulError,Cubic.norm,p109,p112,p113,e109,e112,e113]

def p114 : Cubic := ⟨(63279378814799/781250000000),(1115034666431/3125000000000),(-495288983/625000000000),(4147689/3125000000000)⟩
def e114 : ℝ := (823921/12500000000000)
theorem h114 : Model (fun x => f114 ((101/40)+(1/40)*x)) p114 e114 := by
  apply Model.mul h76 h101
  norm_num [mulError,Cubic.norm,p76,p101,p114,e76,e101,e114]

def p115 : Cubic := ⟨(2053509343163/50000000000000),(3355224677/3125000000000),(34500649/10000000000000),(-1738729/50000000000000)⟩
def e115 : ℝ := (39371/100000000000000)
theorem h115 : Model (fun x => f115 ((101/40)+(1/40)*x)) p115 e115 := by
  apply Model.mul h99 h99
  norm_num [mulError,Cubic.norm,p99,p99,p115,e99,e99,e115]

def p116 : Cubic := ⟨(832319401547/100000000000000),(32638198851/100000000000000),(318187331/100000000000000),(-307817/50000000000000)⟩
def e116 : ℝ := (9443/50000000000000)
theorem h116 : Model (fun x => f116 ((101/40)+(1/40)*x)) p116 e116 := by
  apply Model.mul h115 h99
  norm_num [mulError,Cubic.norm,p115,p99,p116,e115,e99,e116]

def p117 : Cubic := ⟨(67415878022911/100000000000000),(2940596730229/100000000000000),(36758501321/100000000000000),(778161/2000000000000)⟩
def e117 : ℝ := (1011459/50000000000000)
theorem h117 : Model (fun x => f117 ((101/40)+(1/40)*x)) p117 e117 := by
  apply Model.mul h114 h116
  norm_num [mulError,Cubic.norm,p114,p116,p117,e114,e116,e117]

def p118 : Cubic := ⟨(148494110063751/100000000000000),(3327855741107/50000000000000),(11020334337/12500000000000),(39791417/25000000000000)⟩
def e118 : ℝ := (1155983/25000000000000)
theorem h118 : Model (fun x => f118 ((101/40)+(1/40)*x)) p118 e118 := by
  apply Model.mul h117 h106
  norm_num [mulError,Cubic.norm,p117,p106,p118,e117,e106,e118]

def p119 : Cubic := ⟨(32984345499145797/25000000000000),(2790706391536359/100000000000000),(202204145483/2500000000000),(-34261089803/100000000000000)⟩
def e119 : ℝ := (677880597/100000000000000)
theorem h119 : Model (fun x => f119 ((101/40)+(1/40)*x)) p119 e119 := by
  apply Model.add h113 h118
  norm_num [mulError,Cubic.norm,p113,p118,p119,e113,e118,e119]

def p120 : Cubic := ⟨(84338012449/50000000000000),(2204795271/25000000000000),(4488003/3125000000000),(455207/100000000000000)⟩
def e120 : ℝ := (7711/100000000000000)
theorem h120 : Model (fun x => f120 ((101/40)+(1/40)*x)) p120 e120 := by
  apply Model.mul h116 h99
  norm_num [mulError,Cubic.norm,p116,p99,p120,e116,e99,e120]

def p121 : Cubic := ⟨(34183513351/100000000000000),(17872759/800000000000),(10196457/20000000000000),(100001/25000000000000)⟩
def e121 : ℝ := (29/1562500000000)
theorem h121 : Model (fun x => f121 ((101/40)+(1/40)*x)) p121 e121 := by
  apply Model.mul h120 h99
  norm_num [mulError,Cubic.norm,p120,p99,p121,e120,e99,e121]

def p122 : Cubic := ⟨(6927555861/100000000000000),(271654061/50000000000000),(15949189/100000000000000),(49363/25000000000000)⟩
def e122 : ℝ := (1077/100000000000000)
theorem h122 : Model (fun x => f122 ((101/40)+(1/40)*x)) p122 e122 := by
  apply Model.mul h121 h99
  norm_num [mulError,Cubic.norm,p121,p99,p122,e121,e99,e122]

def p123 : Cubic := ⟨(17549041/1250000000000),(128456571/100000000000000),(576309/12500000000000),(15537/20000000000000)⟩
def e123 : ℝ := (313/50000000000000)
theorem h123 : Model (fun x => f123 ((101/40)+(1/40)*x)) p123 e123 := by
  apply Model.mul h122 h99
  norm_num [mulError,Cubic.norm,p122,p99,p123,e122,e99,e123]

def p124 : Cubic := ⟨(52647123/1250000000000),(385369713/100000000000000),(1728927/12500000000000),(46611/20000000000000)⟩
def e124 : ℝ := (939/50000000000000)
theorem h124 : Model (fun x => f124 ((101/40)+(1/40)*x)) p124 e124 := by
  apply Model.mul h50 h123
  norm_num [mulError,Cubic.norm,p50,p123,p124,e50,e123,e124]

def p125 : Cubic := ⟨(-52647123/1250000000000),(-385369713/100000000000000),(-1728927/12500000000000),(-46611/20000000000000)⟩
def e125 : ℝ := (939/50000000000000)
theorem h125 : Model (fun x => f125 ((101/40)+(1/40)*x)) p125 e125 := by
  convert h124.neg using 1 <;> norm_num [f125,p124,p125,e124,e125]

def p126 : Cubic := ⟨(32984344446203337/25000000000000),(1395353003083323/50000000000000),(126377374811/1562500000000),(-17130661429/50000000000000)⟩
def e126 : ℝ := (27115299/4000000000000)
theorem h126 : Model (fun x => f126 ((101/40)+(1/40)*x)) p126 e126 := by
  apply Model.add h119 h125
  norm_num [mulError,Cubic.norm,p119,p125,p126,e119,e125,e126]

def p127 : Cubic := ⟨(189838136444397/625000000000),(3345103999293/2500000000000),(-1485866949/500000000000),(12443067/2500000000000)⟩
def e127 : ℝ := (2471763/10000000000000)
theorem h127 : Model (fun x => f127 ((101/40)+(1/40)*x)) p127 e127 := by
  apply Model.mul h44 h101
  norm_num [mulError,Cubic.norm,p44,p101,p127,e44,e101,e127]

def p128 : Cubic := ⟨(588475165774421/25000000000000),(2830866238431/25000000000000),(-8596307707/50000000000000),(563221/10000000000000)⟩
def e128 : ℝ := (1099917/50000000000000)
theorem h128 : Model (fun x => f128 ((101/40)+(1/40)*x)) p128 e128 := by
  apply Model.mul h108 h106
  norm_num [mulError,Cubic.norm,p108,p106,p128,e108,e106,e128]

def p129 : Cubic := ⟨(142995236882462307/20000000000000),(6589017784680049/100000000000000),(733499563673/25000000000000),(-43228128613/100000000000000)⟩
def e129 : ℝ := (1370851239/100000000000000)
theorem h129 : Model (fun x => f129 ((101/40)+(1/40)*x)) p129 e129 := by
  apply Model.mul h127 h128
  norm_num [mulError,Cubic.norm,p127,p128,p129,e127,e128,e129]

def p130 : Cubic := ⟨(6993239927/50000000000000),(-128895433/100000000000000),(282617/25000000000000),(-2261/25000000000000)⟩
def e130 : ℝ := (51/50000000000000)
theorem h130 : Model (fun x => f130 ((101/40)+(1/40)*x)) p130 e130 := by
  apply Model.inv h129 (L := (354192094015198471/50000000000000))
  · norm_num
  · norm_num [p129,e129]
  · norm_num [mulError,Cubic.norm,p129,p130,e129,e130]

def p131 : Cubic := ⟨(2306674345471/12500000000000),(27532534869/12500000000000),(-974335007/100000000000000),(439841/10000000000000)⟩
def e131 : ℝ := (70209/20000000000000)
theorem h131 : Model (fun x => f131 ((101/40)+(1/40)*x)) p131 e131 := by
  apply Model.mul h126 h130
  norm_num [mulError,Cubic.norm,p126,p130,p131,e126,e130,e131]

def p132 : Cubic := ⟨(41100529193639/100000000000000),(276243113119/50000000000000),(-763102023/50000000000000),(5619617/100000000000000)⟩
def e132 : ℝ := (344533/50000000000000)
theorem h132 : Model (fun x => f132 ((101/40)+(1/40)*x)) p132 e132 := by
  apply Model.add h94 h131
  norm_num [mulError,Cubic.norm,p94,p131,p132,e94,e131,e132]

def p133 : Cubic := ⟨(-427029685385741/100000000000000),(-5688299852591/100000000000000),(8090769659/50000000000000),(-7831087/12500000000000)⟩
def e133 : ℝ := (18383733/100000000000000)
theorem h133 : Model (fun x => f133 ((101/40)+(1/40)*x)) p133 e133 := by
  apply Model.mul h47 h132
  norm_num [mulError,Cubic.norm,p47,p132,p133,e47,e132,e133]

def p134 : Cubic := ⟨(39603960396039/100000000000000),(-392118419763/100000000000000),(3882360591/100000000000000),(-19219607/50000000000000)⟩
def e134 : ℝ := (192197/50000000000000)
theorem h134 : Model (fun x => f134 ((101/40)+(1/40)*x)) p134 e134 := by
  apply Model.inv h0 (L := (5/2))
  · norm_num
  · norm_num [p0,e0]
  · norm_num [mulError,Cubic.norm,p0,p134,e0,e134]

def p135 : Cubic := ⟨(-169120667479499/100000000000000),(-23133198663/4000000000000),(12134569699/100000000000000),(-144955619/100000000000000)⟩
def e135 : ℝ := (3021499/25000000000000)
theorem h135 : Model (fun x => f135 ((101/40)+(1/40)*x)) p135 e135 := by
  apply Model.mul h133 h134
  norm_num [mulError,Cubic.norm,p133,p134,p135,e133,e134,e135]

def p136 : Cubic := ⟨(104060401/256000),(1030301/64000),(30603/128000),(101/64000)⟩
def e136 : ℝ := (1/256000)
theorem h136 : Model (fun x => f136 ((101/40)+(1/40)*x)) p136 e136 := by
  apply Model.mul h62 h18
  norm_num [mulError,Cubic.norm,p62,p18,p136,e62,e18,e136]

def p137 : Cubic := ⟨18,0,0,0⟩
def e137 : ℝ := 0
theorem h137 : Model (fun x => f137 ((101/40)+(1/40)*x)) p137 e137 := by
  exact Model.constant _

def p138 : Cubic := ⟨(9272709/32000),(275427/32000),(2727/32000),(9/32000)⟩
def e138 : ℝ := 0
theorem h138 : Model (fun x => f138 ((101/40)+(1/40)*x)) p138 e138 := by
  apply Model.mul h137 h13
  norm_num [mulError,Cubic.norm,p137,p13,p138,e137,e13,e138]

def p139 : Cubic := ⟨(178242073/256000),(316231/12800),(41511/128000),(119/64000)⟩
def e139 : ℝ := (1/256000)
theorem h139 : Model (fun x => f139 ((101/40)+(1/40)*x)) p139 e139 := by
  apply Model.add h136 h138
  norm_num [mulError,Cubic.norm,p136,p138,p139,e136,e138,e139]

def p140 : Cubic := ⟨(-10201/1600),(-101/800),(-1/1600),0⟩
def e140 : ℝ := 0
theorem h140 : Model (fun x => f140 ((101/40)+(1/40)*x)) p140 e140 := by
  convert h8.neg using 1 <;> norm_num [f140,p8,p140,e8,e140]

def p141 : Cubic := ⟨(176609913/256000),(62923/2560),(41431/128000),(119/64000)⟩
def e141 : ℝ := (1/256000)
theorem h141 : Model (fun x => f141 ((101/40)+(1/40)*x)) p141 e141 := by
  apply Model.add h139 h140
  norm_num [mulError,Cubic.norm,p139,p140,p141,e139,e140,e141]

def p142 : Cubic := ⟨6,0,0,0⟩
def e142 : ℝ := 0
theorem h142 : Model (fun x => f142 ((101/40)+(1/40)*x)) p142 e142 := by
  exact Model.constant _

def p143 : Cubic := ⟨(303/20),(3/20),0,0⟩
def e143 : ℝ := 0
theorem h143 : Model (fun x => f143 ((101/40)+(1/40)*x)) p143 e143 := by
  apply Model.mul h142 h0
  norm_num [mulError,Cubic.norm,p142,p0,p143,e142,e0,e143]

def p144 : Cubic := ⟨(-303/20),(-3/20),0,0⟩
def e144 : ℝ := 0
theorem h144 : Model (fun x => f144 ((101/40)+(1/40)*x)) p144 e144 := by
  convert h143.neg using 1 <;> norm_num [f144,p143,p144,e143,e144]

def p145 : Cubic := ⟨(172731513/256000),(62539/2560),(41431/128000),(119/64000)⟩
def e145 : ℝ := (1/256000)
theorem h145 : Model (fun x => f145 ((101/40)+(1/40)*x)) p145 e145 := by
  apply Model.add h141 h144
  norm_num [mulError,Cubic.norm,p141,p144,p145,e141,e144,e145]

def p146 : Cubic := ⟨(173499513/256000),(62539/2560),(41431/128000),(119/64000)⟩
def e146 : ℝ := (1/256000)
theorem h146 : Model (fun x => f146 ((101/40)+(1/40)*x)) p146 e146 := by
  apply Model.add h145 h50
  norm_num [mulError,Cubic.norm,p145,p50,p146,e145,e50,e146]

def p147 : Cubic := ⟨64,0,0,0⟩
def e147 : ℝ := 0
theorem h147 : Model (fun x => f147 ((101/40)+(1/40)*x)) p147 e147 := by
  exact Model.constant _

def p148 : Cubic := ⟨(173499513/4000),(62539/40),(41431/2000),(119/1000)⟩
def e148 : ℝ := (1/4000)
theorem h148 : Model (fun x => f148 ((101/40)+(1/40)*x)) p148 e148 := by
  apply Model.mul h147 h146
  norm_num [mulError,Cubic.norm,p147,p146,p148,e147,e146,e148]

def p149 : Cubic := ⟨945,0,0,0⟩
def e149 : ℝ := 0
theorem h149 : Model (fun x => f149 ((101/40)+(1/40)*x)) p149 e149 := by
  exact Model.constant _

def p150 : Cubic := ⟨(19667415789/512000),(194726889/128000),(5783967/256000),(19089/128000)⟩
def e150 : ℝ := (189/512000)
theorem h150 : Model (fun x => f150 ((101/40)+(1/40)*x)) p150 e150 := by
  apply Model.mul h149 h18
  norm_num [mulError,Cubic.norm,p149,p18,p150,e149,e18,e150]

def p151 : Cubic := ⟨(650822667/25000000000000),(-103100621/100000000000000),(510399/20000000000000),(-10107/20000000000000)⟩
def e151 : ℝ := (989/100000000000000)
theorem h151 : Model (fun x => f151 ((101/40)+(1/40)*x)) p151 e151 := by
  apply Model.inv h150 (L := (9438431877/256000))
  · norm_num
  · norm_num [p150,e150]
  · norm_num [mulError,Cubic.norm,p150,p151,e150,e151]

def p152 : Cubic := ⟨(112917415773861/100000000000000),(-25112312889/6250000000000),(1712848417/50000000000000),(-5591683/20000000000000)⟩
def e152 : ℝ := (84304403/100000000000000)
theorem h152 : Model (fun x => f152 ((101/40)+(1/40)*x)) p152 e152 := by
  apply Model.mul h148 h151
  norm_num [mulError,Cubic.norm,p148,p151,p152,e148,e151,e152]

def p153 : Cubic := ⟨(221/40),(1/40),0,0⟩
def e153 : ℝ := 0
theorem h153 : Model (fun x => f153 ((101/40)+(1/40)*x)) p153 e153 := by
  apply Model.add h0 h50
  norm_num [mulError,Cubic.norm,p0,p50,p153,e0,e50,e153]

def p154 : Cubic := ⟨(40001/1600),(201/800),(1/1600),0⟩
def e154 : ℝ := 0
theorem h154 : Model (fun x => f154 ((101/40)+(1/40)*x)) p154 e154 := by
  apply Model.mul h153 h49
  norm_num [mulError,Cubic.norm,p153,p49,p154,e153,e49,e154]

def p155 : Cubic := ⟨(423/20),(3/20),0,0⟩
def e155 : ℝ := 0
theorem h155 : Model (fun x => f155 ((101/40)+(1/40)*x)) p155 e155 := by
  apply Model.mul h142 h42
  norm_num [mulError,Cubic.norm,p142,p42,p155,e142,e42,e155]

def p156 : Cubic := ⟨(2364066193853/50000000000000),(-16766426907/50000000000000),(118910829/50000000000000),(-1686679/100000000000000)⟩
def e156 : ℝ := (241/2000000000000)
theorem h156 : Model (fun x => f156 ((101/40)+(1/40)*x)) p156 e156 := by
  apply Model.inv h155 (L := 21)
  · norm_num
  · norm_num [p155,e155]
  · norm_num [mulError,Cubic.norm,p155,p156,e155,e156]

def p157 : Cubic := ⟨(3693945774231/3125000000000),(349600959027/100000000000000),(47564331/10000000000000),(-843343/25000000000000)⟩
def e157 : ℝ := (580489/100000000000000)
theorem h157 : Model (fun x => f157 ((101/40)+(1/40)*x)) p157 e157 := by
  apply Model.mul h154 h156
  norm_num [mulError,Cubic.norm,p154,p156,p157,e154,e156,e157]

def p158 : Cubic := ⟨(6818945774231/3125000000000),(349600959027/100000000000000),(47564331/10000000000000),(-843343/25000000000000)⟩
def e158 : ℝ := (580489/100000000000000)
theorem h158 : Model (fun x => f158 ((101/40)+(1/40)*x)) p158 e158 := by
  apply Model.add h157 h41
  norm_num [mulError,Cubic.norm,p157,p41,p158,e157,e41,e158]

def p159 : Cubic := ⟨(6818945774231/6250000000000),(174800479513/100000000000000),(47564331/20000000000000),(-843343/50000000000000)⟩
def e159 : ℝ := (58049/20000000000000)
theorem h159 : Model (fun x => f159 ((101/40)+(1/40)*x)) p159 e159 := by
  apply Model.mul h158 h54
  norm_num [mulError,Cubic.norm,p158,p54,p159,e158,e54,e159]

def p160 : Cubic := ⟨(568945774231/6250000000000),(174800479513/100000000000000),(47564331/20000000000000),(-843343/50000000000000)⟩
def e160 : ℝ := (58049/20000000000000)
theorem h160 : Model (fun x => f160 ((101/40)+(1/40)*x)) p160 e160 := by
  apply Model.add h159 h58
  norm_num [mulError,Cubic.norm,p159,p58,p160,e159,e58,e160]

def p161 : Cubic := ⟨(155/42),0,0,0⟩
def e161 : ℝ := 0
theorem h161 : Model (fun x => f161 ((101/40)+(1/40)*x)) p161 e161 := by
  exact Model.constant _

def p162 : Cubic := ⟨(1649/70),0,0,0⟩
def e162 : ℝ := 0
theorem h162 : Model (fun x => f162 ((101/40)+(1/40)*x)) p162 e162 := by
  exact Model.constant _

def p163 : Cubic := ⟨(402642512383163/100000000000000),(322548503863/50000000000000),(175535031/20000000000000),(-248987/4000000000000)⟩
def e163 : ℝ := (214229/20000000000000)
theorem h163 : Model (fun x => f163 ((101/40)+(1/40)*x)) p163 e163 := by
  apply Model.mul h159 h161
  norm_num [mulError,Cubic.norm,p159,p161,p163,e159,e161,e163]

def p164 : Cubic := ⟨(344794599762181/12500000000000),(322548503863/50000000000000),(175535031/20000000000000),(-248987/4000000000000)⟩
def e164 : ℝ := (535573/50000000000000)
theorem h164 : Model (fun x => f164 ((101/40)+(1/40)*x)) p164 e164 := by
  apply Model.add h162 h163
  norm_num [mulError,Cubic.norm,p162,p163,p164,e162,e163,e164]

def p165 : Cubic := ⟨(11093/210),0,0,0⟩
def e165 : ℝ := 0
theorem h165 : Model (fun x => f165 ((101/40)+(1/40)*x)) p165 e165 := by
  exact Model.constant _

def p166 : Cubic := ⟨(3009453669153271/100000000000000),(2762720976061/50000000000000),(8645173537/100000000000000),(-50247773/100000000000000)⟩
def e166 : ℝ := (4599051/50000000000000)
theorem h166 : Model (fun x => f166 ((101/40)+(1/40)*x)) p166 e166 := by
  apply Model.mul h159 h164
  norm_num [mulError,Cubic.norm,p159,p164,p166,e159,e164,e166]

def p167 : Cubic := ⟨(8291834621534223/100000000000000),(2762720976061/50000000000000),(8645173537/100000000000000),(-50247773/100000000000000)⟩
def e167 : ℝ := (9198103/100000000000000)
theorem h167 : Model (fun x => f167 ((101/40)+(1/40)*x)) p167 e167 := by
  apply Model.add h165 h166
  norm_num [mulError,Cubic.norm,p165,p166,p167,e165,e166,e167]

def p168 : Cubic := ⟨(2213/42),0,0,0⟩
def e168 : ℝ := 0
theorem h168 : Model (fun x => f168 ((101/40)+(1/40)*x)) p168 e168 := by
  exact Model.constant _

def p169 : Cubic := ⟨(4523325652250647/50000000000000),(4104519385379/20000000000000),(38810432483/100000000000000),(-83213303/50000000000000)⟩
def e169 : ℝ := (8573739/25000000000000)
theorem h169 : Model (fun x => f169 ((101/40)+(1/40)*x)) p169 e169 := by
  apply Model.mul h159 h167
  norm_num [mulError,Cubic.norm,p159,p167,p169,e159,e167,e169]

def p170 : Cubic := ⟨(14315698923548913/100000000000000),(4104519385379/20000000000000),(38810432483/100000000000000),(-83213303/50000000000000)⟩
def e170 : ℝ := (34294957/100000000000000)
theorem h170 : Model (fun x => f170 ((101/40)+(1/40)*x)) p170 e170 := by
  apply Model.add h168 h169
  norm_num [mulError,Cubic.norm,p168,p169,p170,e168,e169,e170]

def p171 : Cubic := ⟨(327/14),0,0,0⟩
def e171 : ℝ := 0
theorem h171 : Model (fun x => f171 ((101/40)+(1/40)*x)) p171 e171 := by
  exact Model.constant _

def p172 : Cubic := ⟨(15618875948783541/100000000000000),(2963419153659/6250000000000),(112262827473/100000000000000),(-306389529/100000000000000)⟩
def e172 : ℝ := (15926601/20000000000000)
theorem h172 : Model (fun x => f172 ((101/40)+(1/40)*x)) p172 e172 := by
  apply Model.mul h159 h170
  norm_num [mulError,Cubic.norm,p159,p170,p172,e159,e170,e172]

def p173 : Cubic := ⟨(8977295117248913/50000000000000),(2963419153659/6250000000000),(112262827473/100000000000000),(-306389529/100000000000000)⟩
def e173 : ℝ := (39816503/50000000000000)
theorem h173 : Model (fun x => f173 ((101/40)+(1/40)*x)) p173 e173 := by
  apply Model.add h171 h172
  norm_num [mulError,Cubic.norm,p171,p172,p173,e171,e172,e173]

def p174 : Cubic := ⟨(169/42),0,0,0⟩
def e174 : ℝ := 0
theorem h174 : Model (fun x => f174 ((101/40)+(1/40)*x)) p174 e174 := by
  exact Model.constant _

def p175 : Cubic := ⟨(1567121628257/8000000000),(83115639783199/100000000000000),(248063299173/100000000000000),(-328119733/100000000000000)⟩
def e175 : ℝ := (140342691/100000000000000)
theorem h175 : Model (fun x => f175 ((101/40)+(1/40)*x)) p175 e175 := by
  apply Model.mul h159 h173
  norm_num [mulError,Cubic.norm,p159,p173,p175,e159,e173,e175]

def p176 : Cubic := ⟨(4997850326398363/25000000000000),(83115639783199/100000000000000),(248063299173/100000000000000),(-328119733/100000000000000)⟩
def e176 : ℝ := (35085673/25000000000000)
theorem h176 : Model (fun x => f176 ((101/40)+(1/40)*x)) p176 e176 := by
  apply Model.add h174 h175
  norm_num [mulError,Cubic.norm,p174,p175,p176,e174,e175,e176]

def p177 : Cubic := ⟨(-37/210),0,0,0⟩
def e177 : ℝ := 0
theorem h177 : Model (fun x => f177 ((101/40)+(1/40)*x)) p177 e177 := by
  exact Model.constant _

def p178 : Cubic := ⟨(2181124503259721/10000000000000),(125626831851089/100000000000000),(92695049607/20000000000000),(-7987281/12500000000000)⟩
def e178 : ℝ := (53255103/25000000000000)
theorem h178 : Model (fun x => f178 ((101/40)+(1/40)*x)) p178 e178 := by
  apply Model.mul h159 h176
  norm_num [mulError,Cubic.norm,p159,p176,p178,e159,e176,e178]

def p179 : Cubic := ⟨(10896812992489081/50000000000000),(125626831851089/100000000000000),(92695049607/20000000000000),(-7987281/12500000000000)⟩
def e179 : ℝ := (213020413/100000000000000)
theorem h179 : Model (fun x => f179 ((101/40)+(1/40)*x)) p179 e179 := by
  apply Model.add h177 h178
  norm_num [mulError,Cubic.norm,p177,p178,p179,e177,e178,e179]

def p180 : Cubic := ⟨(1/30),0,0,0⟩
def e180 : ℝ := 0
theorem h180 : Model (fun x => f180 ((101/40)+(1/40)*x)) p180 e180 := by
  exact Model.constant _

def p181 : Cubic := ⟨(594438215261751/2500000000000),(175158171393973/100000000000000),(388546139961/50000000000000),(335809869/50000000000000)⟩
def e181 : ℝ := (9298189/3125000000000)
theorem h181 : Model (fun x => f181 ((101/40)+(1/40)*x)) p181 e181 := by
  apply Model.mul h159 h179
  norm_num [mulError,Cubic.norm,p159,p179,p181,e159,e179,e181]

def p182 : Cubic := ⟨(23780861943803373/100000000000000),(175158171393973/100000000000000),(388546139961/50000000000000),(335809869/50000000000000)⟩
def e182 : ℝ := (297542049/100000000000000)
theorem h182 : Model (fun x => f182 ((101/40)+(1/40)*x)) p182 e182 := by
  apply Model.add h180 h181
  norm_num [mulError,Cubic.norm,p180,p181,p182,e180,e181,e182]

def p183 : Cubic := ⟨(2164803345679637/100000000000000),(57513940939953/100000000000000),(216736550983/50000000000000),(717477529/50000000000000)⟩
def e183 : ℝ := (97219117/100000000000000)
theorem h183 : Model (fun x => f183 ((101/40)+(1/40)*x)) p183 e183 := by
  apply Model.mul h160 h182
  norm_num [mulError,Cubic.norm,p160,p182,p183,e160,e182,e183]

def p184 : Cubic := ⟨(119034934968071/100000000000000),(190712798577/50000000000000),(412246913/50000000000000),(-712257/25000000000000)⟩
def e184 : ℝ := (63969/10000000000000)
theorem h184 : Model (fun x => f184 ((101/40)+(1/40)*x)) p184 e184 := by
  apply Model.mul h159 h159
  norm_num [mulError,Cubic.norm,p159,p159,p184,e159,e159,e184]

def p185 : Cubic := ⟨(13068945774231/6250000000000),(174800479513/100000000000000),(47564331/20000000000000),(-843343/50000000000000)⟩
def e185 : ℝ := (58049/20000000000000)
theorem h185 : Model (fun x => f185 ((101/40)+(1/40)*x)) p185 e185 := by
  apply Model.add h159 h41
  norm_num [mulError,Cubic.norm,p159,p41,p185,e159,e41,e185]

def p186 : Cubic := ⟨(437241199743463/100000000000000),(36551327809/5000000000000),(81258571/6250000000000),(-3889/62500000000)⟩
def e186 : ℝ := (61009/5000000000000)
theorem h186 : Model (fun x => f186 ((101/40)+(1/40)*x)) p186 e186 := by
  apply Model.mul h185 h185
  norm_num [mulError,Cubic.norm,p185,p185,p186,e185,e185,e186]

def p187 : Cubic := ⟨(914285044753123/100000000000000),(1146449570669/50000000000000),(5036319659/100000000000000),(-3274987/20000000000000)⟩
def e187 : ℝ := (1922461/50000000000000)
theorem h187 : Model (fun x => f187 ((101/40)+(1/40)*x)) p187 e187 := by
  apply Model.mul h186 h185
  norm_num [mulError,Cubic.norm,p186,p185,p187,e186,e185,e187]

def p188 : Cubic := ⟨(477949666882757/25000000000000),(1598174642343/25000000000000),(8356734341/50000000000000),(-35405099/100000000000000)⟩
def e188 : ℝ := (5381183/50000000000000)
theorem h188 : Model (fun x => f188 ((101/40)+(1/40)*x)) p188 e188 := by
  apply Model.mul h187 h185
  norm_num [mulError,Cubic.norm,p187,p185,p188,e187,e185,e188]

def p189 : Cubic := ⟨(2275708300616007/100000000000000),(14901634068769/100000000000000),(234534833/390625000000),(155037/781250000000)⟩
def e189 : ℝ := (6325711/25000000000000)
theorem h189 : Model (fun x => f189 ((101/40)+(1/40)*x)) p189 e189 := by
  apply Model.mul h184 h188
  norm_num [mulError,Cubic.norm,p184,p188,p189,e184,e188,e189]

def p190 : Cubic := ⟨8,0,0,0⟩
def e190 : ℝ := 0
theorem h190 : Model (fun x => f190 ((101/40)+(1/40)*x)) p190 e190 := by
  exact Model.constant _

def p191 : Cubic := ⟨(6818945774231/781250000000),(174800479513/12500000000000),(47564331/2500000000000),(-843343/6250000000000)⟩
def e191 : ℝ := (58049/2500000000000)
theorem h191 : Model (fun x => f191 ((101/40)+(1/40)*x)) p191 e191 := by
  apply Model.mul h190 h159
  norm_num [mulError,Cubic.norm,p190,p159,p191,e190,e159,e191]

def p192 : Cubic := ⟨(991859994069639/100000000000000),(889914716629/50000000000000),(1363533533/50000000000000),(-4085629/25000000000000)⟩
def e192 : ℝ := (59233/2000000000000)
theorem h192 : Model (fun x => f192 ((101/40)+(1/40)*x)) p192 e192 := by
  apply Model.add h184 h191
  norm_num [mulError,Cubic.norm,p184,p191,p192,e184,e191,e192]

def p193 : Cubic := ⟨(1091859994069639/100000000000000),(889914716629/50000000000000),(1363533533/50000000000000),(-4085629/25000000000000)⟩
def e193 : ℝ := (59233/2000000000000)
theorem h193 : Model (fun x => f193 ((101/40)+(1/40)*x)) p193 e193 := by
  apply Model.add h192 h41
  norm_num [mulError,Cubic.norm,p192,p41,p193,e192,e41,e193]

def p194 : Cubic := ⟨(3105943564518527/12500000000000),(203208707008999/100000000000000),(24571162907/2500000000000),(329943053/25000000000000)⟩
def e194 : ℝ := (345018321/100000000000000)
theorem h194 : Model (fun x => f194 ((101/40)+(1/40)*x)) p194 e194 := by
  apply Model.mul h189 h193
  norm_num [mulError,Cubic.norm,p189,p193,p194,e189,e193,e194]

def p195 : Cubic := ⟨(80490837907/20000000000000),(-3291358721/100000000000000),(219967/2000000000000),(9433/50000000000000)⟩
def e195 : ℝ := (6103/100000000000000)
theorem h195 : Model (fun x => f195 ((101/40)+(1/40)*x)) p195 e195 := by
  apply Model.inv h194 (L := (6160838824458101/25000000000000))
  · norm_num
  · norm_num [p194,e194]
  · norm_num [mulError,Cubic.norm,p194,p195,e194,e195]

def p196 : Cubic := ⟨(8712341759881/100000000000000),(10013488823/6250000000000),(89633197/100000000000000),(-879061/50000000000000)⟩
def e196 : ℝ := (270833/50000000000000)
theorem h196 : Model (fun x => f196 ((101/40)+(1/40)*x)) p196 e196 := by
  apply Model.mul h183 h195
  norm_num [mulError,Cubic.norm,p183,p195,p196,e183,e195,e196]

def p197 : Cubic := ⟨(3693945774231/1562500000000),(349600959027/50000000000000),(47564331/5000000000000),(-843343/12500000000000)⟩
def e197 : ℝ := (580489/50000000000000)
theorem h197 : Model (fun x => f197 ((101/40)+(1/40)*x)) p197 e197 := by
  apply Model.mul h48 h157
  norm_num [mulError,Cubic.norm,p48,p157,p197,e48,e157,e197]

def p198 : Cubic := ⟨(45828198426353/100000000000000),(-18356006113/25000000000000),(3548233/20000000000000),(210027/25000000000000)⟩
def e198 : ℝ := (62417/50000000000000)
theorem h198 : Model (fun x => f198 ((101/40)+(1/40)*x)) p198 e198 := by
  apply Model.inv h158 (L := (108928092109597/50000000000000))
  · norm_num
  · norm_num [p158,e158]
  · norm_num [mulError,Cubic.norm,p158,p198,e158,e198]

def p199 : Cubic := ⟨(108343603147293/100000000000000),(146848048901/100000000000000),(-35482331/100000000000000),(-840109/50000000000000)⟩
def e199 : ℝ := (104989/12500000000000)
theorem h199 : Model (fun x => f199 ((101/40)+(1/40)*x)) p199 e199 := by
  apply Model.mul h197 h198
  norm_num [mulError,Cubic.norm,p197,p198,p199,e197,e198,e199]

def p200 : Cubic := ⟨(8343603147293/100000000000000),(146848048901/100000000000000),(-35482331/100000000000000),(-840109/50000000000000)⟩
def e200 : ℝ := (104989/12500000000000)
theorem h200 : Model (fun x => f200 ((101/40)+(1/40)*x)) p200 e200 := by
  apply Model.add h199 h58
  norm_num [mulError,Cubic.norm,p199,p58,p200,e199,e58,e200]

def p201 : Cubic := ⟨(199919743902743/50000000000000),(541939228087/100000000000000),(-65473349/50000000000000),(-1240161/20000000000000)⟩
def e201 : ℝ := (3099677/100000000000000)
theorem h201 : Model (fun x => f201 ((101/40)+(1/40)*x)) p201 e201 := by
  apply Model.mul h199 h161
  norm_num [mulError,Cubic.norm,p199,p161,p201,e199,e161,e201]

def p202 : Cubic := ⟨(2755553773519771/100000000000000),(541939228087/100000000000000),(-65473349/50000000000000),(-1240161/20000000000000)⟩
def e202 : ℝ := (1549839/50000000000000)
theorem h202 : Model (fun x => f202 ((101/40)+(1/40)*x)) p202 e202 := by
  apply Model.add h162 h201
  norm_num [mulError,Cubic.norm,p162,p201,p202,e162,e201,e202]

def p203 : Cubic := ⟨(2985466244892517/100000000000000),(4633633439409/100000000000000),(-323779899/100000000000000),(-6675259/12500000000000)⟩
def e203 : ℝ := (1658113/6250000000000)
theorem h203 : Model (fun x => f203 ((101/40)+(1/40)*x)) p203 e203 := by
  apply Model.mul h199 h202
  norm_num [mulError,Cubic.norm,p199,p202,p203,e199,e202,e203]

def p204 : Cubic := ⟨(8267847197273469/100000000000000),(4633633439409/100000000000000),(-323779899/100000000000000),(-6675259/12500000000000)⟩
def e204 : ℝ := (26529809/100000000000000)
theorem h204 : Model (fun x => f204 ((101/40)+(1/40)*x)) p204 e204 := by
  apply Model.add h165 h203
  norm_num [mulError,Cubic.norm,p165,p203,p204,e165,e203,e204]

def p205 : Cubic := ⟨(4478841778119277/50000000000000),(3432283544041/20000000000000),(3519980581/100000000000000),(-49723793/25000000000000)⟩
def e205 : ℝ := (98420069/100000000000000)
theorem h205 : Model (fun x => f205 ((101/40)+(1/40)*x)) p205 e205 := by
  apply Model.mul h199 h204
  norm_num [mulError,Cubic.norm,p199,p204,p205,e199,e204,e205]

def p206 : Cubic := ⟨(14226731175286173/100000000000000),(3432283544041/20000000000000),(3519980581/100000000000000),(-49723793/25000000000000)⟩
def e206 : ℝ := (9842007/10000000000000)
theorem h206 : Model (fun x => f206 ((101/40)+(1/40)*x)) p206 e206 := by
  apply Model.add h168 h205
  norm_num [mulError,Cubic.norm,p168,p205,p206,e168,e205,e206]

def p207 : Cubic := ⟨(1926719145673033/12500000000000),(19742487731263/50000000000000),(23966905031/100000000000000),(-455450543/100000000000000)⟩
def e207 : ℝ := (226994299/100000000000000)
theorem h207 : Model (fun x => f207 ((101/40)+(1/40)*x)) p207 e207 := by
  apply Model.mul h199 h206
  norm_num [mulError,Cubic.norm,p199,p206,p207,e199,e206,e207]

def p208 : Cubic := ⟨(17749467451098549/100000000000000),(19742487731263/50000000000000),(23966905031/100000000000000),(-455450543/100000000000000)⟩
def e208 : ℝ := (2269943/1000000000000)
theorem h208 : Model (fun x => f208 ((101/40)+(1/40)*x)) p208 e208 := by
  apply Model.add h171 h207
  norm_num [mulError,Cubic.norm,p171,p207,p208,e171,e207,e208]

def p209 : Cubic := ⟨(9615206287988077/50000000000000),(68844191760181/100000000000000),(77651599757/100000000000000),(-385248267/50000000000000)⟩
def e209 : ℝ := (397019987/100000000000000)
theorem h209 : Model (fun x => f209 ((101/40)+(1/40)*x)) p209 e209 := by
  apply Model.mul h199 h208
  norm_num [mulError,Cubic.norm,p199,p208,p209,e199,e208,e209]

def p210 : Cubic := ⟨(9816396764178553/50000000000000),(68844191760181/100000000000000),(77651599757/100000000000000),(-385248267/50000000000000)⟩
def e210 : ℝ := (99254997/25000000000000)
theorem h210 : Model (fun x => f210 ((101/40)+(1/40)*x)) p210 e210 := by
  apply Model.add h174 h209
  norm_num [mulError,Cubic.norm,p174,p209,p210,e174,e209,e210]

def p211 : Cubic := ⟨(4254175181418129/20000000000000),(51709326075883/50000000000000),(7130428827/4000000000000),(-1075055103/100000000000000)⟩
def e211 : ℝ := (149630699/25000000000000)
theorem h211 : Model (fun x => f211 ((101/40)+(1/40)*x)) p211 e211 := by
  apply Model.mul h199 h210
  norm_num [mulError,Cubic.norm,p199,p210,p211,e199,e210,e211]

def p212 : Cubic := ⟨(21253256859471597/100000000000000),(51709326075883/50000000000000),(7130428827/4000000000000),(-1075055103/100000000000000)⟩
def e212 : ℝ := (598522797/100000000000000)
theorem h212 : Model (fun x => f212 ((101/40)+(1/40)*x)) p212 e212 := by
  apply Model.add h177 h211
  norm_num [mulError,Cubic.norm,p177,p211,p212,e177,e211,e212]

def p213 : Cubic := ⟨(11513272133850367/50000000000000),(3581437177341/2500000000000),(337461209713/100000000000000),(-8104859/625000000000)⟩
def e213 : ℝ := (416050669/50000000000000)
theorem h213 : Model (fun x => f213 ((101/40)+(1/40)*x)) p213 e213 := by
  apply Model.mul h199 h212
  norm_num [mulError,Cubic.norm,p199,p212,p213,e199,e212,e213]

def p214 : Cubic := ⟨(23029877601034067/100000000000000),(3581437177341/2500000000000),(337461209713/100000000000000),(-8104859/625000000000)⟩
def e214 : ℝ := (832101339/100000000000000)
theorem h214 : Model (fun x => f214 ((101/40)+(1/40)*x)) p214 e214 := by
  apply Model.add h180 h213
  norm_num [mulError,Cubic.norm,p180,p213,p214,e180,e213,e214]

def p215 : Cubic := ⟨(480380398084401/25000000000000),(11442940530821/25000000000000),(28794463927/12500000000000),(-25213003/50000000000000)⟩
def e215 : ℝ := (134861283/50000000000000)
theorem h215 : Model (fun x => f215 ((101/40)+(1/40)*x)) p215 e215 := by
  apply Model.mul h200 h214
  norm_num [mulError,Cubic.norm,p200,p214,p215,e200,e214,e215]

def p216 : Cubic := ⟨(117383363429381/100000000000000),(318200934661/100000000000000),(69378911/50000000000000),(-936257/25000000000000)⟩
def e216 : ℝ := (14619/800000000000)
theorem h216 : Model (fun x => f216 ((101/40)+(1/40)*x)) p216 e216 := by
  apply Model.mul h199 h199
  norm_num [mulError,Cubic.norm,p199,p199,p216,e199,e199,e216]

def p217 : Cubic := ⟨(208343603147293/100000000000000),(146848048901/100000000000000),(-35482331/100000000000000),(-840109/50000000000000)⟩
def e217 : ℝ := (104989/12500000000000)
theorem h217 : Model (fun x => f217 ((101/40)+(1/40)*x)) p217 e217 := by
  apply Model.add h199 h41
  norm_num [mulError,Cubic.norm,p199,p41,p217,e199,e41,e217]

def p218 : Cubic := ⟨(434070569723967/100000000000000),(611897032463/100000000000000),(1694829/2500000000000),(-888183/12500000000000)⟩
def e218 : ℝ := (3507199/100000000000000)
theorem h218 : Model (fun x => f218 ((101/40)+(1/40)*x)) p218 e218 := by
  apply Model.mul h217 h217
  norm_num [mulError,Cubic.norm,p217,p217,p218,e217,e217,e218]

def p219 : Cubic := ⟨(180871653032979/20000000000000),(1912272487477/100000000000000),(885783209/100000000000000),(-11107337/50000000000000)⟩
def e219 : ℝ := (10983871/100000000000000)
theorem h219 : Model (fun x => f219 ((101/40)+(1/40)*x)) p219 e219 := by
  apply Model.mul h218 h217
  norm_num [mulError,Cubic.norm,p218,p217,p219,e218,e217,e219]

def p220 : Cubic := ⟨(471043148751223/25000000000000),(5312129869873/100000000000000),(2166360049/50000000000000),(-60855807/100000000000000)⟩
def e220 : ℝ := (6115457/20000000000000)
theorem h220 : Model (fun x => f220 ((101/40)+(1/40)*x)) p220 e220 := by
  apply Model.mul h219 h217
  norm_num [mulError,Cubic.norm,p219,p217,p220,e219,e217,e220]

def p221 : Cubic := ⟨(2211705164831391/100000000000000),(489240460757/4000000000000),(2460357633/10000000000000),(-120839633/100000000000000)⟩
def e221 : ℝ := (70904863/100000000000000)
theorem h221 : Model (fun x => f221 ((101/40)+(1/40)*x)) p221 e221 := by
  apply Model.mul h216 h220
  norm_num [mulError,Cubic.norm,p216,p220,p221,e216,e220,e221]

def p222 : Cubic := ⟨(108343603147293/12500000000000),(146848048901/12500000000000),(-35482331/12500000000000),(-840109/6250000000000)⟩
def e222 : ℝ := (104989/1562500000000)
theorem h222 : Model (fun x => f222 ((101/40)+(1/40)*x)) p222 e222 := by
  apply Model.mul h190 h199
  norm_num [mulError,Cubic.norm,p190,p199,p222,e190,e199,e222]

def p223 : Cubic := ⟨(39365287544309/4000000000000),(1492985325869/100000000000000),(-72550413/50000000000000),(-4296693/25000000000000)⟩
def e223 : ℝ := (8546671/100000000000000)
theorem h223 : Model (fun x => f223 ((101/40)+(1/40)*x)) p223 e223 := by
  apply Model.add h216 h222
  norm_num [mulError,Cubic.norm,p216,p222,p223,e216,e222,e223]

def p224 : Cubic := ⟨(43365287544309/4000000000000),(1492985325869/100000000000000),(-72550413/50000000000000),(-4296693/25000000000000)⟩
def e224 : ℝ := (8546671/100000000000000)
theorem h224 : Model (fun x => f224 ((101/40)+(1/40)*x)) p224 e224 := by
  apply Model.add h223 h41
  norm_num [mulError,Cubic.norm,p223,p41,p224,e223,e41,e224]

def p225 : Cubic := ⟨(479556152180733/2000000000000),(165620766431403/100000000000000),(223066647631/50000000000000),(-1340601597/100000000000000)⟩
def e225 : ℝ := (240945449/25000000000000)
theorem h225 : Model (fun x => f225 ((101/40)+(1/40)*x)) p225 e225 := by
  apply Model.mul h221 h224
  norm_num [mulError,Cubic.norm,p221,p224,p225,e221,e224,e225]

def p226 : Cubic := ⟨(417052307827/100000000000000),(-2880685507/100000000000000),(12137907/100000000000000),(-1731/25000000000000)⟩
def e226 : ℝ := (8671/50000000000000)
theorem h226 : Model (fun x => f226 ((101/40)+(1/40)*x)) p226 e226 := by
  apply Model.inv h225 (L := (186029206288489/781250000000))
  · norm_num
  · norm_num [p225,e225]
  · norm_num [mulError,Cubic.norm,p225,p226,e225,e226]

def p227 : Cubic := ⟨(4006875073119/50000000000000),(135539196243/100000000000000),(-31151051/25000000000000),(-1423439/100000000000000)⟩
def e227 : ℝ := (1500163/100000000000000)
theorem h227 : Model (fun x => f227 ((101/40)+(1/40)*x)) p227 e227 := by
  apply Model.mul h215 h226
  norm_num [mulError,Cubic.norm,p215,p226,p227,e215,e226,e227]

def p228 : Cubic := ⟨(16726091906119/100000000000000),(295755017411/100000000000000),(-34971007/100000000000000),(-3181561/100000000000000)⟩
def e228 : ℝ := (2041829/100000000000000)
theorem h228 : Model (fun x => f228 ((101/40)+(1/40)*x)) p228 e228 := by
  apply Model.add h196 h227
  norm_num [mulError,Cubic.norm,p196,p227,p228,e196,e227,e228]

def p229 : Cubic := ⟨(377733414807/2000000000000),(8336062067/3125000000000),(-654837963/100000000000000),(62603/3125000000000)⟩
def e229 : ℝ := (16735261/100000000000000)
theorem h229 : Model (fun x => f229 ((101/40)+(1/40)*x)) p229 e229 := by
  apply Model.mul h152 h228
  norm_num [mulError,Cubic.norm,p152,p228,p229,e152,e228,e229]

def p230 : Cubic := ⟨(3739934800069/50000000000000),(15793514087/50000000000000),(-572084621/100000000000000),(1614397/25000000000000)⟩
def e230 : ℝ := (6903881/100000000000000)
theorem h230 : Model (fun x => f230 ((101/40)+(1/40)*x)) p230 e230 := by
  apply Model.mul h229 h134
  norm_num [mulError,Cubic.norm,p229,p134,p230,e229,e134,e230]

def p231 : Cubic := ⟨(-161640797879361/100000000000000),(-546742938401/100000000000000),(5781242539/50000000000000),(-138498031/100000000000000)⟩
def e231 : ℝ := (18989877/100000000000000)
theorem h231 : Model (fun x => f231 ((101/40)+(1/40)*x)) p231 e231 := by
  apply Model.add h135 h230
  norm_num [mulError,Cubic.norm,p135,p230,p231,e135,e230,e231]

def p232 : Cubic := ⟨-5,0,0,0⟩
def e232 : ℝ := 0
theorem h232 : Model (fun x => f232 ((101/40)+(1/40)*x)) p232 e232 := by
  exact Model.constant _

def p233 : Cubic := ⟨(-10201/320),(-101/160),(-1/320),0⟩
def e233 : ℝ := 0
theorem h233 : Model (fun x => f233 ((101/40)+(1/40)*x)) p233 e233 := by
  apply Model.mul h232 h8
  norm_num [mulError,Cubic.norm,p232,p8,p233,e232,e8,e233]

def p234 : Cubic := ⟨(2121/40),(21/40),0,0⟩
def e234 : ℝ := 0
theorem h234 : Model (fun x => f234 ((101/40)+(1/40)*x)) p234 e234 := by
  apply Model.mul h56 h0
  norm_num [mulError,Cubic.norm,p56,p0,p234,e56,e0,e234]

def p235 : Cubic := ⟨(6767/320),(-17/160),(-1/320),0⟩
def e235 : ℝ := 0
theorem h235 : Model (fun x => f235 ((101/40)+(1/40)*x)) p235 e235 := by
  apply Model.add h233 h234
  norm_num [mulError,Cubic.norm,p233,p234,p235,e233,e234,e235]

def p236 : Cubic := ⟨26,0,0,0⟩
def e236 : ℝ := 0
theorem h236 : Model (fun x => f236 ((101/40)+(1/40)*x)) p236 e236 := by
  exact Model.constant _

def p237 : Cubic := ⟨(15087/320),(-17/160),(-1/320),0⟩
def e237 : ℝ := 0
theorem h237 : Model (fun x => f237 ((101/40)+(1/40)*x)) p237 e237 := by
  apply Model.add h235 h236
  norm_num [mulError,Cubic.norm,p235,p236,p237,e235,e236,e237]

def p238 : Cubic := ⟨250,0,0,0⟩
def e238 : ℝ := 0
theorem h238 : Model (fun x => f238 ((101/40)+(1/40)*x)) p238 e238 := by
  exact Model.constant _

def p239 : Cubic := ⟨(377175/32),(-425/16),(-25/32),0⟩
def e239 : ℝ := 0
theorem h239 : Model (fun x => f239 ((101/40)+(1/40)*x)) p239 e239 := by
  apply Model.mul h238 h237
  norm_num [mulError,Cubic.norm,p238,p237,p239,e238,e237,e239]

def p240 : Cubic := ⟨(14039/1600),(19/800),(-1/1600),0⟩
def e240 : ℝ := 0
theorem h240 : Model (fun x => f240 ((101/40)+(1/40)*x)) p240 e240 := by
  apply Model.add h140 h143
  norm_num [mulError,Cubic.norm,p140,p143,p240,e140,e143,e240]

def p241 : Cubic := ⟨(23639/1600),(19/800),(-1/1600),0⟩
def e241 : ℝ := 0
theorem h241 : Model (fun x => f241 ((101/40)+(1/40)*x)) p241 e241 := by
  apply Model.add h240 h142
  norm_num [mulError,Cubic.norm,p240,p142,p241,e240,e142,e241]

def p242 : Cubic := ⟨189,0,0,0⟩
def e242 : ℝ := 0
theorem h242 : Model (fun x => f242 ((101/40)+(1/40)*x)) p242 e242 := by
  exact Model.constant _

def p243 : Cubic := ⟨(4467771/1600),(3591/800),(-189/1600),0⟩
def e243 : ℝ := 0
theorem h243 : Model (fun x => f243 ((101/40)+(1/40)*x)) p243 e243 := by
  apply Model.mul h242 h241
  norm_num [mulError,Cubic.norm,p242,p241,p243,e242,e241,e243]

def p244 : Cubic := ⟨(8953010349/25000000000000),(-57568323/100000000000000),(1607497/100000000000000),(-251/5000000000000)⟩
def e244 : ℝ := (79/100000000000000)
theorem h244 : Model (fun x => f244 ((101/40)+(1/40)*x)) p244 e244 := by
  apply Model.inv h243 (L := (11151/4))
  · norm_num
  · norm_num [p243,e243]
  · norm_num [mulError,Cubic.norm,p243,p244,e243,e244]

def p245 : Cubic := ⟨(422106459798009/100000000000000),(-407449745423/25000000000000),(-7501883731/100000000000000),(-11378643/20000000000000)⟩
def e245 : ℝ := (514937/25000000000000)
theorem h245 : Model (fun x => f245 ((101/40)+(1/40)*x)) p245 e245 := by
  apply Model.mul h239 h244
  norm_num [mulError,Cubic.norm,p239,p244,p245,e239,e244,e245]

def p246 : Cubic := ⟨(909/20),(9/20),0,0⟩
def e246 : ℝ := 0
theorem h246 : Model (fun x => f246 ((101/40)+(1/40)*x)) p246 e246 := by
  apply Model.mul h137 h0
  norm_num [mulError,Cubic.norm,p137,p0,p246,e137,e0,e246]

def p247 : Cubic := ⟨(82921/1600),(461/800),(1/1600),0⟩
def e247 : ℝ := 0
theorem h247 : Model (fun x => f247 ((101/40)+(1/40)*x)) p247 e247 := by
  apply Model.add h8 h246
  norm_num [mulError,Cubic.norm,p8,p246,p247,e8,e246,e247]

def p248 : Cubic := ⟨(116521/1600),(461/800),(1/1600),0⟩
def e248 : ℝ := 0
theorem h248 : Model (fun x => f248 ((101/40)+(1/40)*x)) p248 e248 := by
  apply Model.add h247 h56
  norm_num [mulError,Cubic.norm,p247,p56,p248,e247,e56,e248]

def p249 : Cubic := ⟨(32761/1600),(181/800),(1/1600),0⟩
def e249 : ℝ := 0
theorem h249 : Model (fun x => f249 ((101/40)+(1/40)*x)) p249 e249 := by
  apply Model.mul h49 h49
  norm_num [mulError,Cubic.norm,p49,p49,p249,e49,e49,e249]

def p250 : Cubic := ⟨(3817344481/2560000),(18096561/640000),(241523/1280000),(321/640000)⟩
def e250 : ℝ := (1/2560000)
theorem h250 : Model (fun x => f250 ((101/40)+(1/40)*x)) p250 e250 := by
  apply Model.mul h248 h249
  norm_num [mulError,Cubic.norm,p248,p249,p250,e248,e249,e250]

def p251 : Cubic := ⟨90,0,0,0⟩
def e251 : ℝ := 0
theorem h251 : Model (fun x => f251 ((101/40)+(1/40)*x)) p251 e251 := by
  exact Model.constant _

def p252 : Cubic := ⟨(178929/160),(1269/80),(9/160),0⟩
def e252 : ℝ := 0
theorem h252 : Model (fun x => f252 ((101/40)+(1/40)*x)) p252 e252 := by
  apply Model.mul h251 h43
  norm_num [mulError,Cubic.norm,p251,p43,p252,e251,e43,e252]

def p253 : Cubic := ⟨(44710471751/50000000000000),(-634191089/50000000000000),(13493427/100000000000000),(-63799/50000000000000)⟩
def e253 : ℝ := (1157/100000000000000)
theorem h253 : Model (fun x => f253 ((101/40)+(1/40)*x)) p253 e253 := by
  apply Model.inv h252 (L := (88191/80))
  · norm_num
  · norm_num [p252,e252]
  · norm_num [mulError,Cubic.norm,p252,p253,e252,e253]

def p254 : Cubic := ⟨(33335014176091/25000000000000),(637107237523/100000000000000),(282233041/25000000000000),(-3209949/100000000000000)⟩
def e254 : ℝ := (1754523/50000000000000)
theorem h254 : Model (fun x => f254 ((101/40)+(1/40)*x)) p254 e254 := by
  apply Model.mul h250 h253
  norm_num [mulError,Cubic.norm,p250,p253,p254,e250,e253,e254]

def p255 : Cubic := ⟨(58335014176091/25000000000000),(637107237523/100000000000000),(282233041/25000000000000),(-3209949/100000000000000)⟩
def e255 : ℝ := (1754523/50000000000000)
theorem h255 : Model (fun x => f255 ((101/40)+(1/40)*x)) p255 e255 := by
  apply Model.add h254 h41
  norm_num [mulError,Cubic.norm,p254,p41,p255,e254,e41,e255]

def p256 : Cubic := ⟨(58335014176091/50000000000000),(318553618761/100000000000000),(282233041/50000000000000),(-64199/4000000000000)⟩
def e256 : ℝ := (438631/25000000000000)
theorem h256 : Model (fun x => f256 ((101/40)+(1/40)*x)) p256 e256 := by
  apply Model.mul h255 h54
  norm_num [mulError,Cubic.norm,p255,p54,p256,e255,e54,e256]

def p257 : Cubic := ⟨(8335014176091/50000000000000),(318553618761/100000000000000),(282233041/50000000000000),(-64199/4000000000000)⟩
def e257 : ℝ := (438631/25000000000000)
theorem h257 : Model (fun x => f257 ((101/40)+(1/40)*x)) p257 e257 := by
  apply Model.add h256 h58
  norm_num [mulError,Cubic.norm,p256,p58,p257,e256,e58,e257]

def p258 : Cubic := ⟨(430567961775909/100000000000000),(1175614545427/100000000000000),(416629727/20000000000000),(-5923123/100000000000000)⟩
def e258 : ℝ := (6475033/100000000000000)
theorem h258 : Model (fun x => f258 ((101/40)+(1/40)*x)) p258 e258 := by
  apply Model.mul h256 h161
  norm_num [mulError,Cubic.norm,p256,p161,p258,e256,e161,e258]

def p259 : Cubic := ⟨(1393141123745097/50000000000000),(1175614545427/100000000000000),(416629727/20000000000000),(-5923123/100000000000000)⟩
def e259 : ℝ := (3237517/50000000000000)
theorem h259 : Model (fun x => f259 ((101/40)+(1/40)*x)) p259 e259 := by
  apply Model.add h162 h258
  norm_num [mulError,Cubic.norm,p162,p258,p259,e162,e258,e259]

def p260 : Cubic := ⟨(3250756288118623/100000000000000),(10247392751737/100000000000000),(2737873877/12500000000000),(-38357753/100000000000000)⟩
def e260 : ℝ := (14126947/25000000000000)
theorem h260 : Model (fun x => f260 ((101/40)+(1/40)*x)) p260 e260 := by
  apply Model.mul h256 h259
  norm_num [mulError,Cubic.norm,p256,p259,p260,e256,e259,e260]

def p261 : Cubic := ⟨(341325489619983/4000000000000),(10247392751737/100000000000000),(2737873877/12500000000000),(-38357753/100000000000000)⟩
def e261 : ℝ := (56507789/100000000000000)
theorem h261 : Model (fun x => f261 ((101/40)+(1/40)*x)) p261 e261 := by
  apply Model.add h165 h260
  norm_num [mulError,Cubic.norm,p165,p260,p261,e165,e260,e261]

def p262 : Cubic := ⟨(4977806818910727/50000000000000),(4892281687783/12500000000000),(2659108293/2500000000000),(-27045447/50000000000000)⟩
def e262 : ℝ := (13510481/6250000000000)
theorem h262 : Model (fun x => f262 ((101/40)+(1/40)*x)) p262 e262 := by
  apply Model.mul h256 h261
  norm_num [mulError,Cubic.norm,p256,p261,p262,e256,e261,e262]

def p263 : Cubic := ⟨(15224661256869073/100000000000000),(4892281687783/12500000000000),(2659108293/2500000000000),(-27045447/50000000000000)⟩
def e263 : ℝ := (216167697/100000000000000)
theorem h263 : Model (fun x => f263 ((101/40)+(1/40)*x)) p263 e263 := by
  apply Model.add h168 h262
  norm_num [mulError,Cubic.norm,p168,p262,p263,e168,e262,e263]

def p264 : Cubic := ⟨(3552523320982563/20000000000000),(188322641671/200000000000),(8367741693/2500000000000),(10091589/4000000000000)⟩
def e264 : ℝ := (520903737/100000000000000)
theorem h264 : Model (fun x => f264 ((101/40)+(1/40)*x)) p264 e264 := by
  apply Model.mul h256 h263
  norm_num [mulError,Cubic.norm,p256,p263,p264,e256,e263,e264]

def p265 : Cubic := ⟨(200983308906271/1000000000000),(188322641671/200000000000),(8367741693/2500000000000),(10091589/4000000000000)⟩
def e265 : ℝ := (260451869/50000000000000)
theorem h265 : Model (fun x => f265 ((101/40)+(1/40)*x)) p265 e265 := by
  apply Model.add h171 h264
  norm_num [mulError,Cubic.norm,p171,p264,p265,e171,e264,e265]

def p266 : Cubic := ⟨(2344872834840999/10000000000000),(173882000078219/100000000000000),(401954210073/50000000000000),(196188973/12500000000000)⟩
def e266 : ℝ := (964874543/100000000000000)
theorem h266 : Model (fun x => f266 ((101/40)+(1/40)*x)) p266 e266 := by
  apply Model.mul h256 h265
  norm_num [mulError,Cubic.norm,p256,p265,p266,e256,e265,e266]

def p267 : Cubic := ⟨(11925554650395471/50000000000000),(173882000078219/100000000000000),(401954210073/50000000000000),(196188973/12500000000000)⟩
def e267 : ℝ := (60304659/6250000000000)
theorem h267 : Model (fun x => f267 ((101/40)+(1/40)*x)) p267 e267 := by
  apply Model.add h174 h266
  norm_num [mulError,Cubic.norm,p174,p266,p267,e174,e266,e267]

def p268 : Cubic := ⟨(2782709598354271/10000000000000),(27884675058291/10000000000000),(406614751879/25000000000000),(2495364889/50000000000000)⟩
def e268 : ℝ := (1557087731/100000000000000)
theorem h268 : Model (fun x => f268 ((101/40)+(1/40)*x)) p268 e268 := by
  apply Model.mul h256 h267
  norm_num [mulError,Cubic.norm,p256,p267,p268,e256,e267,e268]

def p269 : Cubic := ⟨(13904738467961831/50000000000000),(27884675058291/10000000000000),(406614751879/25000000000000),(2495364889/50000000000000)⟩
def e269 : ℝ := (389271933/25000000000000)
theorem h269 : Model (fun x => f269 ((101/40)+(1/40)*x)) p269 e269 := by
  apply Model.add h177 h268
  norm_num [mulError,Cubic.norm,p177,p268,p269,e177,e268,e269]

def p270 : Cubic := ⟨(648906492514713/2000000000000),(413918678102109/100000000000000),(2942841664869/100000000000000),(47388633/390625000000)⟩
def e270 : ℝ := (2335074393/100000000000000)
theorem h270 : Model (fun x => f270 ((101/40)+(1/40)*x)) p270 e270 := by
  apply Model.mul h256 h269
  norm_num [mulError,Cubic.norm,p256,p269,p270,e256,e269,e270]

def p271 : Cubic := ⟨(32448657959068983/100000000000000),(413918678102109/100000000000000),(2942841664869/100000000000000),(47388633/390625000000)⟩
def e271 : ℝ := (1167537197/50000000000000)
theorem h271 : Model (fun x => f271 ((101/40)+(1/40)*x)) p271 e271 := by
  apply Model.add h180 h270
  norm_num [mulError,Cubic.norm,p180,p270,p271,e180,e270,e271]

def p272 : Cubic := ⟨(528242234539/9765625000),(5386460473831/3125000000000),(996143567979/50000000000000),(2642497829/20000000000000)⟩
def e272 : ℝ := (510988861/50000000000000)
theorem h272 : Model (fun x => f272 ((101/40)+(1/40)*x)) p272 e272 := by
  apply Model.mul h257 h271
  norm_num [mulError,Cubic.norm,p257,p271,p272,e257,e271,e272]

def p273 : Cubic := ⟨(136118955156989/100000000000000),(14866263893/2000000000000),(582972389/25000000000000),(-37199/25000000000000)⟩
def e273 : ℝ := (822453/20000000000000)
theorem h273 : Model (fun x => f273 ((101/40)+(1/40)*x)) p273 e273 := by
  apply Model.mul h256 h256
  norm_num [mulError,Cubic.norm,p256,p256,p273,e256,e256,e273]

def p274 : Cubic := ⟨(108335014176091/50000000000000),(318553618761/100000000000000),(282233041/50000000000000),(-64199/4000000000000)⟩
def e274 : ℝ := (438631/25000000000000)
theorem h274 : Model (fun x => f274 ((101/40)+(1/40)*x)) p274 e274 := by
  apply Model.add h256 h41
  norm_num [mulError,Cubic.norm,p256,p41,p274,e256,e41,e274]

def p275 : Cubic := ⟨(469459011861353/100000000000000),(345105108043/25000000000000),(86520543/2500000000000),(-1679373/50000000000000)⟩
def e275 : ℝ := (7621313/100000000000000)
theorem h275 : Model (fun x => f275 ((101/40)+(1/40)*x)) p275 e275 := by
  apply Model.mul h274 h274
  norm_num [mulError,Cubic.norm,p274,p274,p275,e274,e274,e275]

def p276 : Cubic := ⟨(1017176974101867/100000000000000),(89728720253/2000000000000),(14545879533/100000000000000),(2002241/50000000000000)⟩
def e276 : ℝ := (2481187/10000000000000)
theorem h276 : Model (fun x => f276 ((101/40)+(1/40)*x)) p276 e276 := by
  apply Model.mul h275 h274
  norm_num [mulError,Cubic.norm,p275,p274,p276,e275,e274,e276]

def p277 : Cubic := ⟨(1101958819089191/50000000000000),(810063515051/6250000000000),(3221867787/6250000000000),(64011911/100000000000000)⟩
def e277 : ℝ := (71787721/100000000000000)
theorem h277 : Model (fun x => f277 ((101/40)+(1/40)*x)) p277 e277 := by
  apply Model.mul h276 h274
  norm_num [mulError,Cubic.norm,p276,p274,p277,e276,e274,e277]

def p278 : Cubic := ⟨(1499974830804501/50000000000000),(8506102622131/25000000000000),(217903033397/100000000000000),(769266681/100000000000000)⟩
def e278 : ℝ := (191078057/100000000000000)
theorem h278 : Model (fun x => f278 ((101/40)+(1/40)*x)) p278 e278 := by
  apply Model.mul h273 h277
  norm_num [mulError,Cubic.norm,p273,p277,p278,e273,e277,e278]

def p279 : Cubic := ⟨(58335014176091/6250000000000),(318553618761/12500000000000),(282233041/6250000000000),(-64199/500000000000)⟩
def e279 : ℝ := (438631/3125000000000)
theorem h279 : Model (fun x => f279 ((101/40)+(1/40)*x)) p279 e279 := by
  apply Model.mul h190 h256
  norm_num [mulError,Cubic.norm,p190,p256,p279,e190,e256,e279]

def p280 : Cubic := ⟨(213895836394889/20000000000000),(1645871072369/50000000000000),(1711904553/25000000000000),(-3247149/25000000000000)⟩
def e280 : ℝ := (18148457/100000000000000)
theorem h280 : Model (fun x => f280 ((101/40)+(1/40)*x)) p280 e280 := by
  apply Model.add h273 h279
  norm_num [mulError,Cubic.norm,p273,p279,p280,e273,e279,e280]

def p281 : Cubic := ⟨(233895836394889/20000000000000),(1645871072369/50000000000000),(1711904553/25000000000000),(-3247149/25000000000000)⟩
def e281 : ℝ := (18148457/100000000000000)
theorem h281 : Model (fun x => f281 ((101/40)+(1/40)*x)) p281 e281 := by
  apply Model.add h280 h41
  norm_num [mulError,Cubic.norm,p280,p41,p281,e280,e41,e281]

def p282 : Cubic := ⟨(35083786762230087/100000000000000),(248329502392463/50000000000000),(3873751571397/100000000000000),(905471503/5000000000000)⟩
def e282 : ℝ := (282742883/10000000000000)
theorem h282 : Model (fun x => f282 ((101/40)+(1/40)*x)) p282 e282 := by
  apply Model.mul h278 h281
  norm_num [mulError,Cubic.norm,p278,p281,p282,e278,e281,e282]

def p283 : Cubic := ⟨(71257986401/25000000000000),(-126094287/3125000000000),(25649587/100000000000000),(-64709/100000000000000)⟩
def e283 : ℝ := (11907/50000000000000)
theorem h283 : Model (fun x => f283 ((101/40)+(1/40)*x)) p283 e283 := by
  apply Model.inv h282 (L := (17291616534507437/50000000000000))
  · norm_num
  · norm_num [p282,e282]
  · norm_num [mulError,Cubic.norm,p282,p283,e282,e283]

def p284 : Cubic := ⟨(15417949374551/100000000000000),(54607617971/20000000000000),(22212997/20000000000000),(-1009099/50000000000000)⟩
def e284 : ℝ := (552487/12500000000000)
theorem h284 : Model (fun x => f284 ((101/40)+(1/40)*x)) p284 e284 := by
  apply Model.mul h272 h283
  norm_num [mulError,Cubic.norm,p272,p283,p284,e272,e283,e284]

def p285 : Cubic := ⟨(33335014176091/12500000000000),(637107237523/50000000000000),(282233041/12500000000000),(-3209949/50000000000000)⟩
def e285 : ℝ := (1754523/25000000000000)
theorem h285 : Model (fun x => f285 ((101/40)+(1/40)*x)) p285 e285 := by
  apply Model.mul h48 h254
  norm_num [mulError,Cubic.norm,p48,p254,p285,e48,e254,e285]

def p286 : Cubic := ⟨(42855907987841/100000000000000),(-7313309579/6250000000000),(28036749/25000000000000),(849469/100000000000000)⟩
def e286 : ℝ := (81563/12500000000000)
theorem h286 : Model (fun x => f286 ((101/40)+(1/40)*x)) p286 e286 := by
  apply Model.inv h255 (L := (116350906907841/50000000000000))
  · norm_num
  · norm_num [p255,e255]
  · norm_num [mulError,Cubic.norm,p255,p286,e255,e286]

def p287 : Cubic := ⟨(57144092012157/50000000000000),(117012953263/50000000000000),(-112146997/50000000000000),(-849471/50000000000000)⟩
def e287 : ℝ := (2392599/50000000000000)
theorem h287 : Model (fun x => f287 ((101/40)+(1/40)*x)) p287 e287 := by
  apply Model.mul h285 h286
  norm_num [mulError,Cubic.norm,p285,p286,p287,e285,e286,e287]

def p288 : Cubic := ⟨(7144092012157/50000000000000),(117012953263/50000000000000),(-112146997/50000000000000),(-849471/50000000000000)⟩
def e288 : ℝ := (2392599/50000000000000)
theorem h288 : Model (fun x => f288 ((101/40)+(1/40)*x)) p288 e288 := by
  apply Model.add h287 h58
  norm_num [mulError,Cubic.norm,p287,p58,p288,e287,e58,e288]

def p289 : Cubic := ⟨(105444455498623/25000000000000),(215916758997/25000000000000),(-165550329/20000000000000),(-1253981/20000000000000)⟩
def e289 : ℝ := (17659661/100000000000000)
theorem h289 : Model (fun x => f289 ((101/40)+(1/40)*x)) p289 e289 := by
  apply Model.mul h287 h161
  norm_num [mulError,Cubic.norm,p287,p161,p289,e287,e161,e289]

def p290 : Cubic := ⟨(2777492107708777/100000000000000),(215916758997/25000000000000),(-165550329/20000000000000),(-1253981/20000000000000)⟩
def e290 : ℝ := (8829831/50000000000000)
theorem h290 : Model (fun x => f290 ((101/40)+(1/40)*x)) p290 e290 := by
  apply Model.add h162 h289
  norm_num [mulError,Cubic.norm,p162,p289,p290,e162,e289,e290]

def p291 : Cubic := ⟨(793586322829751/25000000000000),(9358900569/125000000000),(-1030913139/20000000000000),(-3639253/6250000000000)⟩
def e291 : ℝ := (76600831/50000000000000)
theorem h291 : Model (fun x => f291 ((101/40)+(1/40)*x)) p291 e291 := by
  apply Model.mul h287 h290
  norm_num [mulError,Cubic.norm,p287,p290,p291,e287,e290,e291]

def p292 : Cubic := ⟨(2114181560924989/25000000000000),(9358900569/125000000000),(-1030913139/20000000000000),(-3639253/6250000000000)⟩
def e292 : ℝ := (153201663/100000000000000)
theorem h292 : Model (fun x => f292 ((101/40)+(1/40)*x)) p292 e292 := by
  apply Model.add h165 h291
  norm_num [mulError,Cubic.norm,p165,p291,p292,e165,e291,e292]

def p293 : Cubic := ⟨(4832519425916131/50000000000000),(14173912129101/50000000000000),(-7337187063/100000000000000),(-119539417/50000000000000)⟩
def e293 : ℝ := (4536969/781250000000)
theorem h293 : Model (fun x => f293 ((101/40)+(1/40)*x)) p293 e293 := by
  apply Model.mul h287 h292
  norm_num [mulError,Cubic.norm,p287,p292,p293,e287,e292,e293]

def p294 : Cubic := ⟨(14934086470879881/100000000000000),(14173912129101/50000000000000),(-7337187063/100000000000000),(-119539417/50000000000000)⟩
def e294 : ℝ := (580732033/100000000000000)
theorem h294 : Model (fun x => f294 ((101/40)+(1/40)*x)) p294 e294 := by
  apply Model.add h168 h293
  norm_num [mulError,Cubic.norm,p168,p293,p294,e168,e293,e294]

def p295 : Cubic := ⟨(8533948114094689/50000000000000),(16836961199989/25000000000000),(12229727917/50000000000000),(-607713711/100000000000000)⟩
def e295 : ℝ := (1382076297/100000000000000)
theorem h295 : Model (fun x => f295 ((101/40)+(1/40)*x)) p295 e295 := by
  apply Model.mul h287 h294
  norm_num [mulError,Cubic.norm,p287,p294,p295,e287,e294,e295]

def p296 : Cubic := ⟨(19403610513903663/100000000000000),(16836961199989/25000000000000),(12229727917/50000000000000),(-607713711/100000000000000)⟩
def e296 : ℝ := (691038149/50000000000000)
theorem h296 : Model (fun x => f296 ((101/40)+(1/40)*x)) p296 e296 := by
  apply Model.add h171 h295
  norm_num [mulError,Cubic.norm,p171,p295,p296,e171,e295,e296]

def p297 : Cubic := ⟨(22176034091491357/100000000000000),(3059502605133/2500000000000),(142044539211/100000000000000),(-1118016761/100000000000000)⟩
def e297 : ℝ := (2517134849/100000000000000)
theorem h297 : Model (fun x => f297 ((101/40)+(1/40)*x)) p297 e297 := by
  apply Model.mul h287 h296
  norm_num [mulError,Cubic.norm,p287,p296,p297,e287,e296,e297]

def p298 : Cubic := ⟨(22578415043872309/100000000000000),(3059502605133/2500000000000),(142044539211/100000000000000),(-1118016761/100000000000000)⟩
def e298 : ℝ := (50342697/2000000000000)
theorem h298 : Model (fun x => f298 ((101/40)+(1/40)*x)) p298 e298 := by
  apply Model.add h174 h297
  norm_num [mulError,Cubic.norm,p174,p297,p298,e174,e297,e298]

def p299 : Cubic := ⟨(25804460535114181/100000000000000),(48176334797237/25000000000000),(4976240547/1250000000000),(-1603425433/100000000000000)⟩
def e299 : ℝ := (49674793/1250000000000)
theorem h299 : Model (fun x => f299 ((101/40)+(1/40)*x)) p299 e299 := by
  apply Model.mul h287 h298
  norm_num [mulError,Cubic.norm,p287,p298,p299,e287,e298,e299]

def p300 : Cubic := ⟨(25786841487495133/100000000000000),(48176334797237/25000000000000),(4976240547/1250000000000),(-1603425433/100000000000000)⟩
def e300 : ℝ := (3973983441/100000000000000)
theorem h300 : Model (fun x => f300 ((101/40)+(1/40)*x)) p300 e300 := by
  apply Model.add h177 h299
  norm_num [mulError,Cubic.norm,p177,p299,p300,e177,e299,e300]

def p301 : Cubic := ⟨(29471312853286587/100000000000000),(70146830558119/25000000000000),(84812247657/10000000000000),(-442800107/25000000000000)⟩
def e301 : ℝ := (5802217203/100000000000000)
theorem h301 : Model (fun x => f301 ((101/40)+(1/40)*x)) p301 e301 := by
  apply Model.mul h287 h300
  norm_num [mulError,Cubic.norm,p287,p300,p301,e287,e300,e301]

def p302 : Cubic := ⟨(368433077332749/1250000000000),(70146830558119/25000000000000),(84812247657/10000000000000),(-442800107/25000000000000)⟩
def e302 : ℝ := (1450554301/25000000000000)
theorem h302 : Model (fun x => f302 ((101/40)+(1/40)*x)) p302 e302 := by
  apply Model.add h180 h301
  norm_num [mulError,Cubic.norm,p180,p301,p302,e180,e301,e302]

def p303 : Cubic := ⟨(4211391687659703/100000000000000),(109069140883039/100000000000000),(355859231753/50000000000000),(300828141/50000000000000)⟩
def e303 : ℝ := (2277335901/100000000000000)
theorem h303 : Model (fun x => f303 ((101/40)+(1/40)*x)) p303 e303 := by
  apply Model.mul h288 h302
  norm_num [mulError,Cubic.norm,p288,p302,p303,e288,e302,e303]

def p304 : Cubic := ⟨(65308945037877/50000000000000),(53492791743/10000000000000),(4374773/12500000000000),(-4933193/100000000000000)⟩
def e304 : ℝ := (10967709/100000000000000)
theorem h304 : Model (fun x => f304 ((101/40)+(1/40)*x)) p304 e304 := by
  apply Model.mul h287 h287
  norm_num [mulError,Cubic.norm,p287,p287,p304,e287,e287,e304]

def p305 : Cubic := ⟨(107144092012157/50000000000000),(117012953263/50000000000000),(-112146997/50000000000000),(-849471/50000000000000)⟩
def e305 : ℝ := (2392599/50000000000000)
theorem h305 : Model (fun x => f305 ((101/40)+(1/40)*x)) p305 e305 := by
  apply Model.add h287 h41
  norm_num [mulError,Cubic.norm,p287,p41,p305,e287,e41,e305]

def p306 : Cubic := ⟨(229597129062191/50000000000000),(501489865241/50000000000000),(-103397451/25000000000000),(-8331077/100000000000000)⟩
def e306 : ℝ := (4107621/20000000000000)
theorem h306 : Model (fun x => f306 ((101/40)+(1/40)*x)) p306 e306 := by
  apply Model.mul h305 h305
  norm_num [mulError,Cubic.norm,p305,p305,p306,e305,e305,e306]

def p307 : Cubic := ⟨(983999036878659/100000000000000),(25186723249/781250000000),(6734581/1562500000000),(-28871489/100000000000000)⟩
def e307 : ℝ := (66115851/100000000000000)
theorem h307 : Model (fun x => f307 ((101/40)+(1/40)*x)) p307 e307 := by
  apply Model.mul h306 h305
  norm_num [mulError,Cubic.norm,p306,p305,p307,e306,e305,e307]

def p308 : Cubic := ⟨(1054296833472009/50000000000000),(9211250665047/100000000000000),(1565330533/25000000000000),(-2650253/3125000000000)⟩
def e308 : ℝ := (94598649/50000000000000)
theorem h308 : Model (fun x => f308 ((101/40)+(1/40)*x)) p308 e308 := by
  apply Model.mul h307 h305
  norm_num [mulError,Cubic.norm,p307,p305,p308,e307,e305,e308]

def p309 : Cubic := ⟨(2754200558033247/100000000000000),(23310997457917/100000000000000),(29094963851/50000000000000),(-178078211/100000000000000)⟩
def e309 : ℝ := (481319287/100000000000000)
theorem h309 : Model (fun x => f309 ((101/40)+(1/40)*x)) p309 e309 := by
  apply Model.mul h304 h308
  norm_num [mulError,Cubic.norm,p304,p308,p309,e304,e308,e309]

def p310 : Cubic := ⟨(57144092012157/6250000000000),(117012953263/6250000000000),(-112146997/6250000000000),(-849471/6250000000000)⟩
def e310 : ℝ := (2392599/6250000000000)
theorem h310 : Model (fun x => f310 ((101/40)+(1/40)*x)) p310 e310 := by
  apply Model.mul h190 h287
  norm_num [mulError,Cubic.norm,p190,p287,p310,e190,e287,e310]

def p311 : Cubic := ⟨(522461681135133/50000000000000),(1203567584819/50000000000000),(-219919221/12500000000000),(-18524729/100000000000000)⟩
def e311 : ℝ := (49249293/100000000000000)
theorem h311 : Model (fun x => f311 ((101/40)+(1/40)*x)) p311 e311 := by
  apply Model.add h304 h310
  norm_num [mulError,Cubic.norm,p304,p310,p311,e304,e310,e311]

def p312 : Cubic := ⟨(572461681135133/50000000000000),(1203567584819/50000000000000),(-219919221/12500000000000),(-18524729/100000000000000)⟩
def e312 : ℝ := (49249293/100000000000000)
theorem h312 : Model (fun x => f312 ((101/40)+(1/40)*x)) p312 e312 := by
  apply Model.add h311 h41
  norm_num [mulError,Cubic.norm,p311,p41,p312,e311,e41,e312]

def p313 : Cubic := ⟨(788337140817517/2500000000000),(333190386148703/100000000000000),(235780232731/20000000000000),(-194809991/12500000000000)⟩
def e313 : ℝ := (1379980329/20000000000000)
theorem h313 : Model (fun x => f313 ((101/40)+(1/40)*x)) p313 e313 := by
  apply Model.mul h309 h312
  norm_num [mulError,Cubic.norm,p309,p312,p313,e309,e312,e313]

def p314 : Cubic := ⟨(317123204091/100000000000000),(-1675399987/50000000000000),(23549487/100000000000000),(-21577/20000000000000)⟩
def e314 : ℝ := (35491/50000000000000)
theorem h314 : Model (fun x => f314 ((101/40)+(1/40)*x)) p314 e314 := by
  apply Model.inv h313 (L := (31199107887006749/100000000000000))
  · norm_num
  · norm_num [p313,e313]
  · norm_num [mulError,Cubic.norm,p313,p314,e313,e314]

def p315 : Cubic := ⟨(1669412532091/12500000000000),(204768242667/100000000000000),(-405903211/100000000000000),(-199627/25000000000000)⟩
def e315 : ℝ := (10396471/100000000000000)
theorem h315 : Model (fun x => f315 ((101/40)+(1/40)*x)) p315 e315 := by
  apply Model.mul h303 h314
  norm_num [mulError,Cubic.norm,p303,p314,p315,e303,e314,e315]

def p316 : Cubic := ⟨(28773249631279/100000000000000),(238903166261/50000000000000),(-147419113/50000000000000),(-1408353/50000000000000)⟩
def e316 : ℝ := (14816367/100000000000000)
theorem h316 : Model (fun x => f316 ((101/40)+(1/40)*x)) p316 e316 := by
  apply Model.add h284 h315
  norm_num [mulError,Cubic.norm,p284,p315,p316,e284,e315,e316]

def p317 : Cubic := ⟨(24290749077487/20000000000000),(1547905265409/100000000000000),(-11190349673/100000000000000),(-5929873/10000000000000)⟩
def e317 : ℝ := (3179507/5000000000000)
theorem h317 : Model (fun x => f317 ((101/40)+(1/40)*x)) p317 e317 := by
  apply Model.mul h245 h316
  norm_num [mulError,Cubic.norm,p245,p316,p317,e245,e316,e317]

def p318 : Cubic := ⟨(9620098644549/20000000000000),(34197320281/25000000000000),(-1446542743/25000000000000),(1352167/4000000000000)⟩
def e318 : ℝ := (13353933/50000000000000)
theorem h318 : Model (fun x => f318 ((101/40)+(1/40)*x)) p318 e318 := by
  apply Model.mul h317 h134
  norm_num [mulError,Cubic.norm,p317,p134,p318,e317,e134,e318]

def p319 : Cubic := ⟨(-14192538082077/12500000000000),(-409953657277/100000000000000),(2888157053/50000000000000),(-3271683/3125000000000)⟩
def e319 : ℝ := (45697743/100000000000000)
theorem h319 : Model (fun x => f319 ((101/40)+(1/40)*x)) p319 e319 := by
  apply Model.add h231 h318
  norm_num [mulError,Cubic.norm,p231,p318,p319,e231,e318,e319]

def p320 : Cubic := ⟨-11,0,0,0⟩
def e320 : ℝ := 0
theorem h320 : Model (fun x => f320 ((101/40)+(1/40)*x)) p320 e320 := by
  exact Model.constant _

def p321 : Cubic := ⟨(-112211/1600),(-1111/800),(-11/1600),0⟩
def e321 : ℝ := 0
theorem h321 : Model (fun x => f321 ((101/40)+(1/40)*x)) p321 e321 := by
  apply Model.mul h320 h8
  norm_num [mulError,Cubic.norm,p320,p8,p321,e320,e8,e321]

def p322 : Cubic := ⟨97,0,0,0⟩
def e322 : ℝ := 0
theorem h322 : Model (fun x => f322 ((101/40)+(1/40)*x)) p322 e322 := by
  exact Model.constant _

def p323 : Cubic := ⟨(9797/40),(97/40),0,0⟩
def e323 : ℝ := 0
theorem h323 : Model (fun x => f323 ((101/40)+(1/40)*x)) p323 e323 := by
  apply Model.mul h322 h0
  norm_num [mulError,Cubic.norm,p322,p0,p323,e322,e0,e323]

def p324 : Cubic := ⟨(279669/1600),(829/800),(-11/1600),0⟩
def e324 : ℝ := 0
theorem h324 : Model (fun x => f324 ((101/40)+(1/40)*x)) p324 e324 := by
  apply Model.add h321 h323
  norm_num [mulError,Cubic.norm,p321,p323,p324,e321,e323,e324]

def p325 : Cubic := ⟨108,0,0,0⟩
def e325 : ℝ := 0
theorem h325 : Model (fun x => f325 ((101/40)+(1/40)*x)) p325 e325 := by
  exact Model.constant _

def p326 : Cubic := ⟨(452469/1600),(829/800),(-11/1600),0⟩
def e326 : ℝ := 0
theorem h326 : Model (fun x => f326 ((101/40)+(1/40)*x)) p326 e326 := by
  apply Model.add h324 h325
  norm_num [mulError,Cubic.norm,p324,p325,p326,e324,e325,e326]

def p327 : Cubic := ⟨(2262345/32),(4145/16),(-55/32),0⟩
def e327 : ℝ := 0
theorem h327 : Model (fun x => f327 ((101/40)+(1/40)*x)) p327 e327 := by
  apply Model.mul h238 h326
  norm_num [mulError,Cubic.norm,p238,p326,p327,e238,e326,e327]

def p328 : Cubic := ⟨(292797540973287/400000000000),0,0,0⟩
def e328 : ℝ := (189/2000000000000)
theorem h328 : Model (fun x => f328 ((101/40)+(1/40)*x)) p328 e328 := by
  apply Model.mul h242 h1
  norm_num [mulError,Cubic.norm,p242,p1,p328,e242,e1,e328]

def p329 : Cubic := ⟨(54073758367715089/5000000000000),(1738485399528891/100000000000000),(-45749615777077/100000000000000),0⟩
def e329 : ℝ := (2797/2000000000000)
theorem h329 : Model (fun x => f329 ((101/40)+(1/40)*x)) p329 e329 := by
  apply Model.mul h328 h241
  norm_num [mulError,Cubic.norm,p328,p241,p329,e328,e241,e329]

def p330 : Cubic := ⟨(577914333/6250000000000),(-14864077/100000000000000),(207527/50000000000000),(-81/6250000000000)⟩
def e330 : ℝ := (1/5000000000000)
theorem h330 : Model (fun x => f330 ((101/40)+(1/40)*x)) p330 e330 := by
  apply Model.inv h329 (L := (539845466169427981/50000000000000))
  · norm_num
  · norm_num [p329,e329]
  · norm_num [mulError,Cubic.norm,p329,p330,e329,e330]

def p331 : Cubic := ⟨(326860400422721/50000000000000),(1344590214017/100000000000000),(240005883/2500000000000),(20723793/50000000000000)⟩
def e331 : ℝ := (247053/10000000000000)
theorem h331 : Model (fun x => f331 ((101/40)+(1/40)*x)) p331 e331 := by
  apply Model.mul h327 h330
  norm_num [mulError,Cubic.norm,p327,p330,p331,e327,e330,e331]

def p332 : Cubic := ⟨9,0,0,0⟩
def e332 : ℝ := 0
theorem h332 : Model (fun x => f332 ((101/40)+(1/40)*x)) p332 e332 := by
  exact Model.constant _

def p333 : Cubic := ⟨(461/40),(1/40),0,0⟩
def e333 : ℝ := 0
theorem h333 : Model (fun x => f333 ((101/40)+(1/40)*x)) p333 e333 := by
  apply Model.add h0 h332
  norm_num [mulError,Cubic.norm,p0,p332,p333,e0,e332,e333]

def p334 : Cubic := ⟨(1549193338483/200000000000),0,0,0⟩
def e334 : ℝ := (1/1000000000000)
theorem h334 : Model (fun x => f334 ((101/40)+(1/40)*x)) p334 e334 := by
  apply Model.mul h48 h1
  norm_num [mulError,Cubic.norm,p48,p1,p334,e48,e1,e334]

def p335 : Cubic := ⟨(-1549193338483/200000000000),0,0,0⟩
def e335 : ℝ := (1/1000000000000)
theorem h335 : Model (fun x => f335 ((101/40)+(1/40)*x)) p335 e335 := by
  convert h334.neg using 1 <;> norm_num [f335,p334,p335,e334,e335]

def p336 : Cubic := ⟨(755806661517/200000000000),(1/40),0,0⟩
def e336 : ℝ := (1/1000000000000)
theorem h336 : Model (fun x => f336 ((101/40)+(1/40)*x)) p336 e336 := by
  apply Model.add h333 h335
  norm_num [mulError,Cubic.norm,p333,p335,p336,e333,e335,e336]

def p337 : Cubic := ⟨5,0,0,0⟩
def e337 : ℝ := 0
theorem h337 : Model (fun x => f337 ((101/40)+(1/40)*x)) p337 e337 := by
  exact Model.constant _

def p338 : Cubic := ⟨(3549193338483/400000000000),0,0,0⟩
def e338 : ℝ := (1/2000000000000)
theorem h338 : Model (fun x => f338 ((101/40)+(1/40)*x)) p338 e338 := by
  apply Model.add h337 h1
  norm_num [mulError,Cubic.norm,p337,p1,p338,e337,e1,e338]

def p339 : Cubic := ⟨(1676564980148257/50000000000000),(11091229182759/50000000000000),0,0⟩
def e339 : ℝ := (27/2500000000000)
theorem h339 : Model (fun x => f339 ((101/40)+(1/40)*x)) p339 e339 := by
  apply Model.mul h336 h338
  norm_num [mulError,Cubic.norm,p336,p338,p339,e336,e338,e339]

def p340 : Cubic := ⟨(3854193338483/200000000000),(1/40),0,0⟩
def e340 : ℝ := (1/1000000000000)
theorem h340 : Model (fun x => f340 ((101/40)+(1/40)*x)) p340 e340 := by
  apply Model.add h333 h334
  norm_num [mulError,Cubic.norm,p333,p334,p340,e333,e334,e340]

def p341 : Cubic := ⟨(-1549193338483/400000000000),0,0,0⟩
def e341 : ℝ := (1/2000000000000)
theorem h341 : Model (fun x => f341 ((101/40)+(1/40)*x)) p341 e341 := by
  convert h1.neg using 1 <;> norm_num [f341,p1,p341,e1,e341]

def p342 : Cubic := ⟨(450806661517/400000000000),0,0,0⟩
def e342 : ℝ := (1/2000000000000)
theorem h342 : Model (fun x => f342 ((101/40)+(1/40)*x)) p342 e342 := by
  apply Model.add h337 h341
  norm_num [mulError,Cubic.norm,p337,p341,p342,e337,e341,e342]

def p343 : Cubic := ⟨(2171870039703227/100000000000000),(2817541634481/100000000000000),0,0⟩
def e343 : ℝ := (1079/100000000000000)
theorem h343 : Model (fun x => f343 ((101/40)+(1/40)*x)) p343 e343 := by
  apply Model.mul h340 h342
  norm_num [mulError,Cubic.norm,p340,p342,p343,e340,e342,e343]

def p344 : Cubic := ⟨(2302163531241/50000000000000),(-5973139719/100000000000000),(1937221/25000000000000),(-10053/100000000000000)⟩
def e344 : ℝ := (9/50000000000000)
theorem h344 : Model (fun x => f344 ((101/40)+(1/40)*x)) p344 e344 := by
  apply Model.inv h343 (L := (2169052498067667/100000000000000))
  · norm_num
  · norm_num [p343,e343]
  · norm_num [mulError,Cubic.norm,p343,p344,e343,e344]

def p345 : Cubic := ⟨(38597267550531/25000000000000),(821065796159/100000000000000),(-1065159081/100000000000000),(690901/50000000000000)⟩
def e345 : ℝ := (289/10000000000000)
theorem h345 : Model (fun x => f345 ((101/40)+(1/40)*x)) p345 e345 := by
  apply Model.mul h339 h344
  norm_num [mulError,Cubic.norm,p339,p344,p345,e339,e344,e345]

def p346 : Cubic := ⟨(63597267550531/25000000000000),(821065796159/100000000000000),(-1065159081/100000000000000),(690901/50000000000000)⟩
def e346 : ℝ := (289/10000000000000)
theorem h346 : Model (fun x => f346 ((101/40)+(1/40)*x)) p346 e346 := by
  apply Model.add h345 h41
  norm_num [mulError,Cubic.norm,p345,p41,p346,e345,e41,e346]

def p347 : Cubic := ⟨(63597267550531/50000000000000),(410532898079/100000000000000),(-532579541/100000000000000),(690901/100000000000000)⟩
def e347 : ℝ := (723/50000000000000)
theorem h347 : Model (fun x => f347 ((101/40)+(1/40)*x)) p347 e347 := by
  apply Model.mul h346 h54
  norm_num [mulError,Cubic.norm,p346,p54,p347,e346,e54,e347]

def p348 : Cubic := ⟨(13597267550531/50000000000000),(410532898079/100000000000000),(-532579541/100000000000000),(690901/100000000000000)⟩
def e348 : ℝ := (723/50000000000000)
theorem h348 : Model (fun x => f348 ((101/40)+(1/40)*x)) p348 e348 := by
  apply Model.add h347 h58
  norm_num [mulError,Cubic.norm,p347,p58,p348,e347,e58,e348]

def p349 : Cubic := ⟨(469408403349157/100000000000000),(1515061885767/100000000000000),(-491368029/25000000000000),(2549753/100000000000000)⟩
def e349 : ℝ := (5339/100000000000000)
theorem h349 : Model (fun x => f349 ((101/40)+(1/40)*x)) p349 e349 := by
  apply Model.mul h347 h161
  norm_num [mulError,Cubic.norm,p347,p161,p349,e347,e161,e349]

def p350 : Cubic := ⟨(1412561344531721/50000000000000),(1515061885767/100000000000000),(-491368029/25000000000000),(2549753/100000000000000)⟩
def e350 : ℝ := (267/5000000000000)
theorem h350 : Model (fun x => f350 ((101/40)+(1/40)*x)) p350 e350 := by
  apply Model.add h162 h349
  norm_num [mulError,Cubic.norm,p162,p349,p350,e162,e349,e350]

def p351 : Cubic := ⟨(1796700835194433/50000000000000),(6762566985897/50000000000000),(-353942847/3125000000000),(51751/781250000000)⟩
def e351 : ℝ := (79119/100000000000000)
theorem h351 : Model (fun x => f351 ((101/40)+(1/40)*x)) p351 e351 := by
  apply Model.mul h347 h350
  norm_num [mulError,Cubic.norm,p347,p350,p351,e347,e350,e351]

def p352 : Cubic := ⟨(4437891311384909/50000000000000),(6762566985897/50000000000000),(-353942847/3125000000000),(51751/781250000000)⟩
def e352 : ℝ := (989/1250000000000)
theorem h352 : Model (fun x => f352 ((101/40)+(1/40)*x)) p352 e352 := by
  apply Model.add h165 h351
  norm_num [mulError,Cubic.norm,p165,p351,p352,e165,e351,e352]

def p353 : Cubic := ⟨(11289510443612917/100000000000000),(13410309726417/25000000000000),(-615174857/10000000000000),(-12195339/25000000000000)⟩
def e353 : ℝ := (205289/50000000000000)
theorem h353 : Model (fun x => f353 ((101/40)+(1/40)*x)) p353 e353 := by
  apply Model.mul h347 h352
  norm_num [mulError,Cubic.norm,p347,p352,p353,e347,e352,e353]

def p354 : Cubic := ⟨(2069819757832567/12500000000000),(13410309726417/25000000000000),(-615174857/10000000000000),(-12195339/25000000000000)⟩
def e354 : ℝ := (410579/100000000000000)
theorem h354 : Model (fun x => f354 ((101/40)+(1/40)*x)) p354 e354 := by
  apply Model.add h168 h353
  norm_num [mulError,Cubic.norm,p168,p353,p354,e168,e353,e354]

def p355 : Cubic := ⟨(21061580947240487/100000000000000),(8512940796453/6250000000000),(31050688031/25000000000000),(-32322649/12500000000000)⟩
def e355 : ℝ := (483731/50000000000000)
theorem h355 : Model (fun x => f355 ((101/40)+(1/40)*x)) p355 e355 := by
  apply Model.mul h347 h354
  norm_num [mulError,Cubic.norm,p347,p354,p355,e347,e354,e355]

def p356 : Cubic := ⟨(5849323808238693/25000000000000),(8512940796453/6250000000000),(31050688031/25000000000000),(-32322649/12500000000000)⟩
def e356 : ℝ := (967463/100000000000000)
theorem h356 : Model (fun x => f356 ((101/40)+(1/40)*x)) p356 e356 := by
  apply Model.add h171 h355
  norm_num [mulError,Cubic.norm,p171,p355,p356,e171,e355,e356]

def p357 : Cubic := ⟨(29760080897779763/100000000000000),(269301521703581/100000000000000),(592544666603/100000000000000),(-382766737/100000000000000)⟩
def e357 : ℝ := (147441/6250000000000)
theorem h357 : Model (fun x => f357 ((101/40)+(1/40)*x)) p357 e357 := by
  apply Model.mul h347 h356
  norm_num [mulError,Cubic.norm,p347,p356,p357,e347,e356,e357]

def p358 : Cubic := ⟨(6032492370032143/20000000000000),(269301521703581/100000000000000),(592544666603/100000000000000),(-382766737/100000000000000)⟩
def e358 : ℝ := (2359057/100000000000000)
theorem h358 : Model (fun x => f358 ((101/40)+(1/40)*x)) p358 e358 := by
  apply Model.add h174 h357
  norm_num [mulError,Cubic.norm,p174,p357,p358,e174,e357,e358]

def p359 : Cubic := ⟨(7673000625069421/20000000000000),(58295455914549/12500000000000),(212327084337/12500000000000),(359940181/50000000000000)⟩
def e359 : ℝ := (6323027/100000000000000)
theorem h359 : Model (fun x => f359 ((101/40)+(1/40)*x)) p359 e359 := by
  apply Model.mul h347 h358
  norm_num [mulError,Cubic.norm,p347,p358,p359,e347,e358,e359]

def p360 : Cubic := ⟨(38347384077728057/100000000000000),(58295455914549/12500000000000),(212327084337/12500000000000),(359940181/50000000000000)⟩
def e360 : ℝ := (1580757/25000000000000)
theorem h360 : Model (fun x => f360 ((101/40)+(1/40)*x)) p360 e360 := by
  apply Model.add h177 h359
  norm_num [mulError,Cubic.norm,p177,p359,p360,e177,e359,e360]

def p361 : Cubic := ⟨(48775776901084873/100000000000000),(750617700276223/100000000000000),(483861682167/12500000000000),(5670213829/100000000000000)⟩
def e361 : ℝ := (11506747/100000000000000)
theorem h361 : Model (fun x => f361 ((101/40)+(1/40)*x)) p361 e361 := by
  apply Model.mul h347 h360
  norm_num [mulError,Cubic.norm,p347,p360,p361,e347,e360,e361]

def p362 : Cubic := ⟨(24389555117209103/50000000000000),(750617700276223/100000000000000),(483861682167/12500000000000),(5670213829/100000000000000)⟩
def e362 : ℝ := (2876687/25000000000000)
theorem h362 : Model (fun x => f362 ((101/40)+(1/40)*x)) p362 e362 := by
  apply Model.add h180 h361
  norm_num [mulError,Cubic.norm,p180,p361,p362,e180,e361,e362]

def p363 : Cubic := ⟨(2653050450936917/20000000000000),(101095322219727/25000000000000),(3874416517027/100000000000000),(13772658439/100000000000000)⟩
def e363 : ℝ := (11744791/100000000000000)
theorem h363 : Model (fun x => f363 ((101/40)+(1/40)*x)) p363 e363 := by
  apply Model.mul h348 h362
  norm_num [mulError,Cubic.norm,p348,p362,p363,e348,e362,e363]

def p364 : Cubic := ⟨(20223062199469/12500000000000),(1044350822297/100000000000000),(330548461/100000000000000),(-653813/25000000000000)⟩
def e364 : ℝ := (12209/100000000000000)
theorem h364 : Model (fun x => f364 ((101/40)+(1/40)*x)) p364 e364 := by
  apply Model.mul h347 h347
  norm_num [mulError,Cubic.norm,p347,p347,p364,e347,e347,e364]

def p365 : Cubic := ⟨(113597267550531/50000000000000),(410532898079/100000000000000),(-532579541/100000000000000),(690901/100000000000000)⟩
def e365 : ℝ := (723/50000000000000)
theorem h365 : Model (fun x => f365 ((101/40)+(1/40)*x)) p365 e365 := by
  apply Model.add h347 h41
  norm_num [mulError,Cubic.norm,p347,p41,p365,e347,e41,e365]

def p366 : Cubic := ⟨(129043391949469/25000000000000),(373083323691/20000000000000),(-734610621/100000000000000),(-24669/2000000000000)⟩
def e366 : ℝ := (15101/100000000000000)
theorem h366 : Model (fun x => f366 ((101/40)+(1/40)*x)) p366 e366 := by
  apply Model.mul h365 h365
  norm_num [mulError,Cubic.norm,p365,p365,p366,e365,e365,e366]

def p367 : Cubic := ⟨(1172718137672949/100000000000000),(1271437384199/20000000000000),(3240118901/100000000000000),(-12186729/100000000000000)⟩
def e367 : ℝ := (53603/100000000000000)
theorem h367 : Model (fun x => f367 ((101/40)+(1/40)*x)) p367 e367 := by
  apply Model.mul h366 h365
  norm_num [mulError,Cubic.norm,p366,p365,p367,e366,e365,e367]

def p368 : Cubic := ⟨(166521970058243/6250000000000),(9628787513773/50000000000000),(13607029951/50000000000000),(-5017573/12500000000000)⟩
def e368 : ℝ := (40627/25000000000000)
theorem h368 : Model (fun x => f368 ((101/40)+(1/40)*x)) p368 e368 := by
  apply Model.mul h367 h365
  norm_num [mulError,Cubic.norm,p367,p365,p368,e367,e365,e368]

def p369 : Cubic := ⟨(269406732645277/6250000000000),(2359237921007/4000000000000),(25395174619/10000000000000),(213245127/100000000000000)⟩
def e369 : ℝ := (142599/10000000000000)
theorem h369 : Model (fun x => f369 ((101/40)+(1/40)*x)) p369 e369 := by
  apply Model.mul h364 h368
  norm_num [mulError,Cubic.norm,p364,p368,p369,e364,e368,e369]

def p370 : Cubic := ⟨(63597267550531/6250000000000),(410532898079/12500000000000),(-532579541/12500000000000),(690901/12500000000000)⟩
def e370 : ℝ := (723/6250000000000)
theorem h370 : Model (fun x => f370 ((101/40)+(1/40)*x)) p370 e370 := by
  apply Model.mul h190 h347
  norm_num [mulError,Cubic.norm,p190,p347,p370,e190,e347,e370]

def p371 : Cubic := ⟨(147417597300531/12500000000000),(4328614006929/100000000000000),(-3930087867/100000000000000),(727989/25000000000000)⟩
def e371 : ℝ := (23777/100000000000000)
theorem h371 : Model (fun x => f371 ((101/40)+(1/40)*x)) p371 e371 := by
  apply Model.add h364 h370
  norm_num [mulError,Cubic.norm,p364,p370,p371,e364,e370,e371]

def p372 : Cubic := ⟨(159917597300531/12500000000000),(4328614006929/100000000000000),(-3930087867/100000000000000),(727989/25000000000000)⟩
def e372 : ℝ := (23777/100000000000000)
theorem h372 : Model (fun x => f372 ((101/40)+(1/40)*x)) p372 e372 := by
  apply Model.add h371 h41
  norm_num [mulError,Cubic.norm,p371,p41,p372,e371,e41,e372]

def p373 : Cubic := ⟨(55146083047960609/100000000000000),(94115256061377/10000000000000),(2816279541557/50000000000000),(1152823973/10000000000000)⟩
def e373 : ℝ := (5078143/25000000000000)
theorem h373 : Model (fun x => f373 ((101/40)+(1/40)*x)) p373 e373 := by
  apply Model.mul h369 h372
  norm_num [mulError,Cubic.norm,p369,p372,p373,e369,e372,e373]

def p374 : Cubic := ⟨(181336541913/100000000000000),(-1547393227/50000000000000),(3429577/10000000000000),(-307121/100000000000000)⟩
def e374 : ℝ := (101/4000000000000)
theorem h374 : Model (fun x => f374 ((101/40)+(1/40)*x)) p374 e374 := by
  apply Model.inv h373 (L := (54199286379711423/100000000000000))
  · norm_num
  · norm_num [p373,e373]
  · norm_num [mulError,Cubic.norm,p373,p374,e373,e374]

def p375 : Cubic := ⟨(24054749714681/100000000000000),(322759815529/100000000000000),(-939584017/100000000000000),(1507623/50000000000000)⟩
def e375 : ℝ := (142711/20000000000000)
theorem h375 : Model (fun x => f375 ((101/40)+(1/40)*x)) p375 e375 := by
  apply Model.mul h363 h374
  norm_num [mulError,Cubic.norm,p363,p374,p375,e363,e374,e375]

def p376 : Cubic := ⟨(38597267550531/12500000000000),(821065796159/50000000000000),(-1065159081/50000000000000),(690901/25000000000000)⟩
def e376 : ℝ := (289/5000000000000)
theorem h376 : Model (fun x => f376 ((101/40)+(1/40)*x)) p376 e376 := by
  apply Model.mul h48 h345
  norm_num [mulError,Cubic.norm,p48,p345,p376,e48,e345,e376]

def p377 : Cubic := ⟨(39309864972007/100000000000000),(-253752927/200000000000),(287050823/50000000000000),(-2597743/100000000000000)⟩
def e377 : ℝ := (11981/100000000000000)
theorem h377 : Model (fun x => f377 ((101/40)+(1/40)*x)) p377 e377 := by
  apply Model.inv h346 (L := (15847933616387/6250000000000))
  · norm_num
  · norm_num [p346,e346]
  · norm_num [mulError,Cubic.norm,p346,p377,e346,e377]

def p378 : Cubic := ⟨(7586266878499/6250000000000),(63438231749/25000000000000),(-1148203297/100000000000000),(5195483/100000000000000)⟩
def e378 : ℝ := (97939/100000000000000)
theorem h378 : Model (fun x => f378 ((101/40)+(1/40)*x)) p378 e378 := by
  apply Model.mul h376 h377
  norm_num [mulError,Cubic.norm,p376,p377,p378,e376,e377,e378]

def p379 : Cubic := ⟨(1336266878499/6250000000000),(63438231749/25000000000000),(-1148203297/100000000000000),(5195483/100000000000000)⟩
def e379 : ℝ := (97939/100000000000000)
theorem h379 : Model (fun x => f379 ((101/40)+(1/40)*x)) p379 e379 := by
  apply Model.add h378 h58
  norm_num [mulError,Cubic.norm,p378,p58,p379,e378,e58,e379]

def p380 : Cubic := ⟨(447950996635179/100000000000000),(468234567671/50000000000000),(-423741693/10000000000000),(9586903/50000000000000)⟩
def e380 : ℝ := (361443/100000000000000)
theorem h380 : Model (fun x => f380 ((101/40)+(1/40)*x)) p380 e380 := by
  apply Model.mul h378 h161
  norm_num [mulError,Cubic.norm,p378,p161,p380,e378,e161,e380]

def p381 : Cubic := ⟨(350458160293683/12500000000000),(468234567671/50000000000000),(-423741693/10000000000000),(9586903/50000000000000)⟩
def e381 : ℝ := (90361/25000000000000)
theorem h381 : Model (fun x => f381 ((101/40)+(1/40)*x)) p381 e381 := by
  apply Model.add h162 h380
  norm_num [mulError,Cubic.norm,p162,p380,p381,e162,e380,e381]

def p382 : Cubic := ⟨(680619298236329/20000000000000),(8251071482601/100000000000000),(-34958847481/100000000000000),(147432031/100000000000000)⟩
def e382 : ℝ := (3332853/100000000000000)
theorem h382 : Model (fun x => f382 ((101/40)+(1/40)*x)) p382 e382 := by
  apply Model.mul h378 h381
  norm_num [mulError,Cubic.norm,p378,p381,p382,e378,e381,e382]

def p383 : Cubic := ⟨(8685477443562597/100000000000000),(8251071482601/100000000000000),(-34958847481/100000000000000),(147432031/100000000000000)⟩
def e383 : ℝ := (1666427/50000000000000)
theorem h383 : Model (fun x => f383 ((101/40)+(1/40)*x)) p383 e383 := by
  apply Model.add h165 h382
  norm_num [mulError,Cubic.norm,p165,p382,p383,e165,e382,e383]

def p384 : Cubic := ⟨(2108491195329571/20000000000000),(3205482608471/10000000000000),(-121222746453/100000000000000),(446757727/100000000000000)⟩
def e384 : ℝ := (13776223/100000000000000)
theorem h384 : Model (fun x => f384 ((101/40)+(1/40)*x)) p384 e384 := by
  apply Model.mul h378 h383
  norm_num [mulError,Cubic.norm,p378,p383,p384,e378,e383,e384]

def p385 : Cubic := ⟨(7905751797847737/50000000000000),(3205482608471/10000000000000),(-121222746453/100000000000000),(446757727/100000000000000)⟩
def e385 : ℝ := (430507/3125000000000)
theorem h385 : Model (fun x => f385 ((101/40)+(1/40)*x)) p385 e385 := by
  apply Model.add h168 h384
  norm_num [mulError,Cubic.norm,p168,p384,p385,e168,e384,e385]

def p386 : Cubic := ⟨(9596022882183393/50000000000000),(9878798455469/12500000000000),(-61837160793/25000000000000),(688098879/100000000000000)⟩
def e386 : ℝ := (36476277/100000000000000)
theorem h386 : Model (fun x => f386 ((101/40)+(1/40)*x)) p386 e386 := by
  apply Model.mul h378 h385
  norm_num [mulError,Cubic.norm,p378,p385,p386,e378,e385,e386]

def p387 : Cubic := ⟨(21527760050081071/100000000000000),(9878798455469/12500000000000),(-61837160793/25000000000000),(688098879/100000000000000)⟩
def e387 : ℝ := (18238139/50000000000000)
theorem h387 : Model (fun x => f387 ((101/40)+(1/40)*x)) p387 e387 := by
  apply Model.add h171 h386
  norm_num [mulError,Cubic.norm,p171,p386,p387,e171,e386,e387]

def p388 : Cubic := ⟨(40828833259051/156250000000),(150554619192033/100000000000000),(-69374595973/20000000000000),(104650863/25000000000000)⟩
def e388 : ℝ := (74242639/100000000000000)
theorem h388 : Model (fun x => f388 ((101/40)+(1/40)*x)) p388 e388 := by
  apply Model.mul h378 h387
  norm_num [mulError,Cubic.norm,p378,p387,p388,e378,e387,e388]

def p389 : Cubic := ⟨(3316604279771699/12500000000000),(150554619192033/100000000000000),(-69374595973/20000000000000),(104650863/25000000000000)⟩
def e389 : ℝ := (928033/1250000000000)
theorem h389 : Model (fun x => f389 ((101/40)+(1/40)*x)) p389 e389 := by
  apply Model.add h174 h388
  norm_num [mulError,Cubic.norm,p174,p388,p389,e174,e388,e389]

def p390 : Cubic := ⟨(3220562585180169/10000000000000),(25007144685141/10000000000000),(-68729896859/20000000000000),(-180565637/25000000000000)⟩
def e390 : ℝ := (32332217/25000000000000)
theorem h390 : Model (fun x => f390 ((101/40)+(1/40)*x)) p390 e390 := by
  apply Model.mul h378 h389
  norm_num [mulError,Cubic.norm,p378,p389,p390,e378,e389,e390]

def p391 : Cubic := ⟨(16094003402091321/50000000000000),(25007144685141/10000000000000),(-68729896859/20000000000000),(-180565637/25000000000000)⟩
def e391 : ℝ := (129328869/100000000000000)
theorem h391 : Model (fun x => f391 ((101/40)+(1/40)*x)) p391 e391 := by
  apply Model.add h177 h390
  norm_num [mulError,Cubic.norm,p177,p390,p391,e177,e390,e391]

def p392 : Cubic := ⟨(7813977916911079/20000000000000),(385215406928433/100000000000000),(-152142811481/100000000000000),(-2947711033/100000000000000)⟩
def e392 : ℝ := (102097159/50000000000000)
theorem h392 : Model (fun x => f392 ((101/40)+(1/40)*x)) p392 e392 := by
  apply Model.mul h378 h391
  norm_num [mulError,Cubic.norm,p378,p391,p392,e378,e391,e392]

def p393 : Cubic := ⟨(4884152864736091/12500000000000),(385215406928433/100000000000000),(-152142811481/100000000000000),(-2947711033/100000000000000)⟩
def e393 : ℝ := (204194319/100000000000000)
theorem h393 : Model (fun x => f393 ((101/40)+(1/40)*x)) p393 e393 := by
  apply Model.add h180 h392
  norm_num [mulError,Cubic.norm,p180,p392,p393,e180,e392,e393]

def p394 : Cubic := ⟨(8353960579421241/100000000000000),(181509541124371/100000000000000),(496326792567/100000000000000),(-1704654383/50000000000000)⟩
def e394 : ℝ := (97130057/100000000000000)
theorem h394 : Model (fun x => f394 ((101/40)+(1/40)*x)) p394 e394 := by
  apply Model.mul h379 h393
  norm_num [mulError,Cubic.norm,p379,p393,p394,e379,e393,e394]

def p395 : Cubic := ⟨(36832924897159/25000000000000),(4928095809/800000000000),(-1071739523/50000000000000),(6785383/100000000000000)⟩
def e395 : ℝ := (277929/100000000000000)
theorem h395 : Model (fun x => f395 ((101/40)+(1/40)*x)) p395 e395 := by
  apply Model.mul h378 h378
  norm_num [mulError,Cubic.norm,p378,p378,p395,e378,e378,e395]

def p396 : Cubic := ⟨(13836266878499/6250000000000),(63438231749/25000000000000),(-1148203297/100000000000000),(5195483/100000000000000)⟩
def e396 : ℝ := (97939/100000000000000)
theorem h396 : Model (fun x => f396 ((101/40)+(1/40)*x)) p396 e396 := by
  apply Model.add h378 h41
  norm_num [mulError,Cubic.norm,p378,p41,p396,e378,e41,e396]

def p397 : Cubic := ⟨(122523059925151/25000000000000),(1123517830117/100000000000000),(-110997141/2500000000000),(17176349/100000000000000)⟩
def e397 : ℝ := (473807/100000000000000)
theorem h397 : Model (fun x => f397 ((101/40)+(1/40)*x)) p397 e397 := by
  apply Model.mul h396 h396
  norm_num [mulError,Cubic.norm,p396,p396,p397,e396,e396,e397]

def p398 : Cubic := ⟨(1084967523772617/100000000000000),(186543510483/5000000000000),(-1575665837/12500000000000),(19660549/50000000000000)⟩
def e398 : ℝ := (1684587/100000000000000)
theorem h398 : Model (fun x => f398 ((101/40)+(1/40)*x)) p398 e398 := by
  apply Model.mul h397 h396
  norm_num [mulError,Cubic.norm,p397,p396,p398,e397,e396,e398]

def p399 : Cubic := ⟨(2401904034147541/100000000000000),(172071053033/1562500000000),(-30896146801/100000000000000),(13718819/20000000000000)⟩
def e399 : ℝ := (1309843/25000000000000)
theorem h399 : Model (fun x => f399 ((101/40)+(1/40)*x)) p399 e399 := by
  apply Model.mul h398 h396
  norm_num [mulError,Cubic.norm,p398,p396,p399,e398,e396,e399]

def p400 : Cubic := ⟨(221172877249849/6250000000000),(31020989749127/100000000000000),(-29165517043/100000000000000),(-162336377/100000000000000)⟩
def e400 : ℝ := (16293543/100000000000000)
theorem h400 : Model (fun x => f400 ((101/40)+(1/40)*x)) p400 e400 := by
  apply Model.mul h395 h399
  norm_num [mulError,Cubic.norm,p395,p399,p400,e395,e399,e400]

def p401 : Cubic := ⟨(7586266878499/781250000000),(63438231749/3125000000000),(-1148203297/12500000000000),(5195483/12500000000000)⟩
def e401 : ℝ := (97939/12500000000000)
theorem h401 : Model (fun x => f401 ((101/40)+(1/40)*x)) p401 e401 := by
  apply Model.mul h190 h378
  norm_num [mulError,Cubic.norm,p190,p378,p401,e190,e378,e401]

def p402 : Cubic := ⟨(279593465009127/25000000000000),(2646035392093/100000000000000),(-5664552711/50000000000000),(48349247/100000000000000)⟩
def e402 : ℝ := (1061441/100000000000000)
theorem h402 : Model (fun x => f402 ((101/40)+(1/40)*x)) p402 e402 := by
  apply Model.add h395 h401
  norm_num [mulError,Cubic.norm,p395,p401,p402,e395,e401,e402]

def p403 : Cubic := ⟨(304593465009127/25000000000000),(2646035392093/100000000000000),(-5664552711/50000000000000),(48349247/100000000000000)⟩
def e403 : ℝ := (1061441/100000000000000)
theorem h403 : Model (fun x => f403 ((101/40)+(1/40)*x)) p403 e403 := by
  apply Model.add h402 h41
  norm_num [mulError,Cubic.norm,p402,p41,p403,e402,e41,e403]

def p404 : Cubic := ⟨(21557700175222343/50000000000000),(47158863198383/10000000000000),(32285398543/50000000000000),(-4553027787/100000000000000)⟩
def e404 : ℝ := (250852251/100000000000000)
theorem h404 : Model (fun x => f404 ((101/40)+(1/40)*x)) p404 e404 := by
  apply Model.mul h400 h403
  norm_num [mulError,Cubic.norm,p400,p403,p404,e400,e403,e404]

def p405 : Cubic := ⟨(231935686987/100000000000000),(-2536871569/100000000000000),(27400499/100000000000000),(-27141/10000000000000)⟩
def e405 : ℝ := (4073/100000000000000)
theorem h405 : Model (fun x => f405 ((101/40)+(1/40)*x)) p405 e405 := by
  apply Model.inv h404 (L := (10660935585945933/25000000000000))
  · norm_num
  · norm_num [p404,e404]
  · norm_num [mulError,Cubic.norm,p404,p405,e404,e405]

def p406 : Cubic := ⟨(19375815860503/100000000000000),(26132018791/12500000000000),(-1164478103/100000000000000),(3281229/50000000000000)⟩
def e406 : ℝ := (847883/100000000000000)
theorem h406 : Model (fun x => f406 ((101/40)+(1/40)*x)) p406 e406 := by
  apply Model.mul h394 h405
  norm_num [mulError,Cubic.norm,p394,p405,p406,e394,e405,e406]

def p407 : Cubic := ⟨(2714410348449/6250000000000),(531815965857/100000000000000),(-52601553/2500000000000),(1197213/12500000000000)⟩
def e407 : ℝ := (780719/50000000000000)
theorem h407 : Model (fun x => f407 ((101/40)+(1/40)*x)) p407 e407 := by
  apply Model.add h375 h406
  norm_num [mulError,Cubic.norm,p375,p406,p407,e375,e406,e407]

def p408 : Cubic := ⟨(283914641089797/100000000000000),(101513868141/2500000000000),(-608627453/25000000000000),(20675387/20000000000000)⟩
def e408 : ℝ := (11462011/100000000000000)
theorem h408 : Model (fun x => f408 ((101/40)+(1/40)*x)) p408 e408 := by
  apply Model.mul h331 h407
  norm_num [mulError,Cubic.norm,p331,p407,p408,e331,e407,e408]

def p409 : Cubic := ⟨(112441442015759/100000000000000),(123714720321/25000000000000),(-1465938797/25000000000000),(98998341/100000000000000)⟩
def e409 : ℝ := (7757487/100000000000000)
theorem h409 : Model (fun x => f409 ((101/40)+(1/40)*x)) p409 e409 := by
  apply Model.mul h408 h134
  norm_num [mulError,Cubic.norm,p408,p134,p409,e408,e134,e409]

def p410 : Cubic := ⟨(-1098862640857/100000000000000),(84905224007/100000000000000),(-43720541/50000000000000),(-1139103/20000000000000)⟩
def e410 : ℝ := (5345523/10000000000000)
theorem h410 : Model (fun x => f410 ((101/40)+(1/40)*x)) p410 e410 := by
  apply Model.add h319 h409
  norm_num [mulError,Cubic.norm,p319,p409,p410,e319,e409,e410]

def p411 : Cubic := ⟨(1791078679321289/12500000000000),(167272989501953/25000000000000),(10201/81920),(11817/10240000)⟩
def e411 : ℝ := (266601563/50000000000000)
theorem h411 : Model (fun x => f411 ((101/40)+(1/40)*x)) p411 e411 := by
  apply Model.mul h18 h42
  norm_num [mulError,Cubic.norm,p18,p42,p411,e18,e42,e411]

def p412 : Cubic := ⟨(48841/1600),(221/800),(1/1600),0⟩
def e412 : ℝ := 0
theorem h412 : Model (fun x => f412 ((101/40)+(1/40)*x)) p412 e412 := by
  apply Model.mul h153 h153
  norm_num [mulError,Cubic.norm,p153,p153,p412,e153,e153,e412]

def p413 : Cubic := ⟨(10793861/64000),(146523/64000),(663/64000),(1/64000)⟩
def e413 : ℝ := 0
theorem h413 : Model (fun x => f413 ((101/40)+(1/40)*x)) p413 e413 := by
  apply Model.mul h412 h153
  norm_num [mulError,Cubic.norm,p412,p153,p413,e412,e153,e413]

def p414 : Cubic := ⟨(96663271523287839/4000000000000),(145649365024932897/100000000000000),(3780416201312681/100000000000000),(55126785797973/100000000000000)⟩
def e414 : ℝ := (496198733131/100000000000000)
theorem h414 : Model (fun x => f414 ((101/40)+(1/40)*x)) p414 e414 := by
  apply Model.mul h411 h413
  norm_num [mulError,Cubic.norm,p411,p413,p414,e411,e413,e414]

def p415 : Cubic := ⟨(1034519093/25000000000000),(-49881051/20000000000000),(2139599/25000000000000),(-220059/100000000000000)⟩
def e415 : ℝ := (7061/100000000000000)
theorem h415 : Model (fun x => f415 ((101/40)+(1/40)*x)) p415 e415 := by
  apply Model.inv h414 (L := (2267096383871419293/100000000000000))
  · norm_num
  · norm_num [p414,e414]
  · norm_num [mulError,Cubic.norm,p414,p415,e414,e415]

def p416 : Cubic := ⟨(5592131912763/100000000000000),(-1743884231/12500000000000),(-62144067/25000000000000),(2931829/50000000000000)⟩
def e416 : ℝ := (18232391/100000000000000)
theorem h416 : Model (fun x => f416 ((101/40)+(1/40)*x)) p416 e416 := by
  apply Model.mul h32 h415
  norm_num [mulError,Cubic.norm,p32,p415,p416,e32,e415,e416]

def p417 : Cubic := ⟨(2246634635953/50000000000000),(70954150159/100000000000000),(-6720347/2000000000000),(168143/100000000000000)⟩
def e417 : ℝ := (71687621/100000000000000)
theorem h417 : Model (fun x => f417 ((101/40)+(1/40)*x)) p417 e417 := by
  apply Model.add h410 h416
  norm_num [mulError,Cubic.norm,p410,p416,p417,e410,e416,e417]

theorem kernel_model : Model (fun x => kernel ((101/40)+(1/40)*x)) p417 e417 := by
  simp only [kernel_dag]
  exact h417

theorem mass_bounds : ((2695851347101/1200000000000000):ℝ) ≤ SigmaActualBlockSeparable.endpointCellMass (5/2) (51/20) ∧
    SigmaActualBlockSeparable.endpointCellMass (5/2) (51/20) ≤ (13479686861231/6000000000000000) := by
  have hh := endpoint_model (by norm_num : (0:ℝ)<(1/40)) (by norm_num : (1:ℝ)≤(101/40)-(1/40)) (by norm_num : ((101/40):ℝ)+(1/40)≤3) kernel_model
  norm_num [p417,e417] at hh
  exact hh

end Hf4Quad.Panel30

